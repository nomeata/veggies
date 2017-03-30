{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
module Veggies.CodeGen where

import Data.List
import Data.Maybe
import Data.Bifunctor
import Control.Arrow ((&&&))
import Data.Either
import Control.Monad.State
import Control.Monad.Writer

import Var
import Id
import MkId
import Module
import Type
import TyCon
import DataCon
import Name
import OccName
import CoreSyn
import CoreUtils
import CoreFVs
import Encoding
import Outputable
import PrelNames
import TysWiredIn
import TysPrim
import BasicTypes
import VarSet
import VarEnv
import Literal

import Ollvm_ast

import Debug.Trace
import GHC.Stack

import Veggies.GenMonad
import Veggies.CodeGenTypes
import Veggies.ASTUtils
import Veggies.Common


data GenEnv = GenEnv
    { topLvls :: IdSet
    , topLvlArities :: VarEnv Integer
    }

genCode :: ModuleName -> [TyCon] -> CoreProgram -> Coq_modul
genCode name tycons binds
    = mkCoqModul (moduleNameString name) $ concat
        [ globals
        , external_decls
        , defaultTyDecls
        , defaultDecls
        ]
  where
    env = mkGenEnv (flattenBinds binds)

    (globals, externals) =
        bimap id nub $
        runG $ sequence_ [genStaticVal env v e | (v,e) <- flattenBinds binds ]

    external_decls = [ mkExternalDecl v | v <- externals ]
    defaultDecls =
        [ mallocDecl
        , returnArgDecl
        , badArityDecl
        ]

mkGenEnv :: [(Id, CoreExpr)] -> GenEnv
mkGenEnv pairs =
    GenEnv { topLvls = mkVarSet (map fst pairs)
           , topLvlArities = mkVarEnv
                [ (v, fromIntegral (length (fst (collectMoreValBinders e)))) | (v,e) <- pairs ]
           }

getIdArity :: GenEnv -> Id -> Integer
getIdArity env v | isExternalName (idName v)                    = fromIntegral $ idArity v
                 | Just a <- lookupVarEnv (topLvlArities env) v = a
                 | otherwise                                    = fromIntegral $ idArity v

isTopLvl :: GenEnv -> Id -> Bool
isTopLvl env v = v `elemVarSet` topLvls env

genStaticVal :: GenEnv -> Var -> CoreExpr -> G ()
genStaticVal env v rhs
    | getIdArity env v == 0
    , Just dc <- isDataConId_maybe v
    = do
    let val = SV $VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                               , (TYPE_I 64, SV (VALUE_Integer (fromIntegral (dataConTag dc))))
                               , (envTy 0 , SV (VALUE_Array []))
                               ]
    emitTL $ TLGlobal $ Coq_mk_global
           (varRawIdTmp v)
           (mkDataConTy 0) --hsTyP
           True -- constant
           (Just val)
           (Just LINKAGE_Private)
           Nothing
           Nothing
           Nothing
           False
           Nothing
           False
           Nothing
           Nothing
    emitTL $ TLAlias $ Coq_mk_alias
           (varRawId v)
           hsTyP
           (SV (OP_Conversion Bitcast (mkDataConTy 0) (ident (ID_Global (varRawIdTmp v))) hsTyP))
           (Just LINKAGE_External)
           Nothing
           Nothing
           Nothing
           False

-- A top-level data con application
genStaticVal env v rhs
    | (Var f, args) <- collectArgs rhs
    , Just dc <- isDataConId_maybe f
    , let val_args = mapMaybe getStaticArg args
    , not (null val_args)
    = do
    args_idents <- map (hsTyP,) <$> mapM genStaticArg val_args
    let arity = fromIntegral (length args_idents)
        val = SV $ VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                                , (TYPE_I 64, SV (VALUE_Integer (fromIntegral (dataConTag dc))))
                                , (envTy arity , SV (VALUE_Array args_idents))
                                ]
    unless (arity == fromIntegral (dataConRepArity dc)) $ do
           pprTrace "genStaticVal arity" (ppr v <+> ppr rhs <+> ppr (dataConRepArity dc) <+> ppr (fromIntegral arity::Int)) (return ())

    emitTL $ TLGlobal $ Coq_mk_global
         (varRawIdTmp v)
         (mkDataConTy arity) --hsTyP
         True -- constant
         (Just val)
         (Just LINKAGE_Private)
         Nothing
         Nothing
         Nothing
         False
         Nothing
         False
         Nothing
         Nothing
    emitTL $ TLAlias $ Coq_mk_alias
         (varRawId v)
         hsTyP
         (SV (OP_Conversion Bitcast (mkDataConTy arity) (ident (ID_Global (varRawIdTmp v))) hsTyP))
         (Just LINKAGE_External)
         Nothing
         Nothing
         Nothing
         False
  where
    cast arity val = SV (OP_Conversion Bitcast (mkDataConTy arity) val hsTyP)

    getStaticArg :: CoreExpr -> Maybe CoreExpr
    getStaticArg (Cast e _)              = getStaticArg e
    getStaticArg (App e a) | isTyCoArg a = getStaticArg e
    getStaticArg (Var v)                 = Just (Var v)
    getStaticArg (Lit l)                 = Just (Lit l)
    getStaticArg _                       = Nothing

    genStaticArg :: CoreExpr -> G Coq_value
    genStaticArg (Var v) = do
        when (isGlobalId v && not (isTopLvl env v)) $ noteExternalVar v
        return $ cast (getIdArity env v) (ident (varIdent env v))
    genStaticArg (Lit (MachInt l)) = do
        lit <- genIntegerLit l
        return (ident lit)
    genStaticArg (Lit (MachWord l)) = do
        lit <- genIntegerLit l
        return (ident lit)
    genStaticArg (Lit l) =
        pprTrace "getStaticArg" (ppr l) $
        return $ SV (VALUE_Null)
    genStaticArg e = pprPanic "genStaticArg" (ppr e)



-- A top-level function
genStaticVal env v rhs | exprIsHNF rhs = do
    genTopLvlFunction env v rhs
    emitTL $ TLGlobal $ Coq_mk_global
            (varRawIdTmp v)
            (mkFunClosureTy arity 0) --hsTyP
            True -- constant
            (Just val)
            (Just LINKAGE_Private)
            Nothing
            Nothing
            Nothing
            False
            Nothing
            False
            Nothing
            Nothing
    emitTL $ TLAlias $ Coq_mk_alias
            (varRawId v)
            hsTyP
            (SV (OP_Conversion Bitcast (mkFunClosureTy arity 0) (ident (ID_Global (varRawIdTmp v))) hsTyP))
            (Just LINKAGE_External)
            Nothing
            Nothing
            Nothing
            False
  where
    arity = getIdArity env v
    val = SV $VALUE_Struct [ (enterFunTyP,                     ident returnArgIdent)
                           , (TYPE_Pointer (hsFunTy arity 0) , ident (funIdent env v))

                           , (TYPE_I 64, SV (VALUE_Integer arity))
                           , (envTy 0 , SV (VALUE_Array []))
                      ]

-- A static thunk
genStaticVal env v rhs = do
    blocks <- runLG $ do
        ret <- genExpr env rhs
        -- TODO: update thunk here
        returnFromFunction ret
    emitTL $ TLDef $ mkEnterFunDefinition
        LINKAGE_Internal
        (funRawId v)
        blocks
    emitTL $ TLGlobal $ Coq_mk_global
            (varRawIdTmp v)
            (mkThunkTy 0)
            True -- constant
            (Just val)
            (Just LINKAGE_Private)
            Nothing
            Nothing
            Nothing
            False
            Nothing
            False
            Nothing
            Nothing
    emitTL $ TLAlias $ Coq_mk_alias
            (varRawId v)
            hsTyP
            (SV (OP_Conversion Bitcast (TYPE_Pointer (mkThunkTy 0)) (ident (ID_Global (varRawIdTmp v))) hsTyP))
            (Just LINKAGE_External)
            Nothing
            Nothing
            Nothing
            False
  where
    val = SV $ VALUE_Struct [ (enterFunTyP, ident (funIdent env v))
                            , (envTy 0,     mkThunkArray [])
                            ]

genTopLvlFunction :: GenEnv -> Id -> CoreExpr -> G ()
genTopLvlFunction env v rhs
    | Just dc <- isDataConWorkId_maybe v = genDataConWorker dc
genTopLvlFunction env v rhs
    | length params /= fromIntegral (getIdArity env v)
    = pprPanic "genTopLvlFunction" (ppr v <+> ppr rhs <+> ppr (fromIntegral (getIdArity env v)::Int))
    | otherwise
    = do
      blocks <- runLG (genExpr env body >>= returnFromFunction)
      emitTL $ TLDef $ mkHsFunDefinition
            LINKAGE_External
            (funRawId v)
            [ varRawId p | p <- params ]
            0
            blocks
  where
    (params, body) = collectMoreValBinders rhs


genDataConWorker :: DataCon -> G ()
genDataConWorker dc = do
    blocks <- runLG $ do
        let (alloc, fill) = allocateDataCon (Name "dc") (fromIntegral (dataConTag dc)) (fromIntegral (dataConRepArity dc))
        alloc
        fill [ ID_Local (Name (paramName n)) | n <- [0..dataConRepArity dc - 1]]
        returnFromFunction (ID_Local (Name "dc"))
    emitTL $ TLDef $ mkHsFunDefinition linkage
        (funRawId (dataConWorkId dc))
        [ Name (paramName n) | n <- [0.. dataConRepArity dc-1]]
        0
        blocks
  where
    linkage | isUnboxedTupleCon dc -- || isUnboxedSumCon dc -- see Id.hasNoBinding
            = LINKAGE_Private
            | otherwise
            = LINKAGE_External

    paramName n = "dcArg_" ++ show n

mkExternalDecl :: Var -> TopLevelThing
mkExternalDecl v =
    TLGlobal $ Coq_mk_global
       (varRawId v)
       hsTy
       True -- constant
       Nothing
       (Just LINKAGE_External)
       Nothing
       Nothing
       Nothing
       False
       Nothing
       False
       Nothing
       Nothing


{- For debugging
deriving instance Show Coq_alias
deriving instance Show Coq_raw_id
deriving instance Show Coq_type_decl
deriving instance Show Coq_typ
deriving instance Show Coq_ident
deriving instance Show Coq_fn_attr
deriving instance Show Coq_linkage
deriving instance Show Coq_dll_storage
deriving instance Show Coq_cconv
deriving instance Show Coq_declaration
deriving instance Show Coq_param_attr
deriving instance Show Coq_visibility
deriving instance Show Coq_icmp
deriving instance Show Coq_ibinop
deriving instance Show Coq_fcmp
deriving instance Show Coq_fbinop
deriving instance Show Coq_fast_math
deriving instance Show Coq_conversion_type
deriving instance Show a => Show (Ollvm_ast.Expr a)
deriving instance Show Coq_value
deriving instance Show Coq_terminator
deriving instance Show Coq_instr
deriving instance Show Coq_instr_id
deriving instance Show Coq_block
deriving instance Show Coq_definition
deriving instance Show Coq_toplevel_entity
deriving instance Show Coq_thread_local_storage
deriving instance Show Coq_global
deriving instance Show Coq_metadata
deriving instance Show Coq_modul
-}

returnFromFunction :: Coq_ident -> LG ()
returnFromFunction lid = emitTerm (TERM_Ret (hsTyP, ident lid))


collectMoreValBinders :: CoreExpr -> ([Id], CoreExpr)
collectMoreValBinders = go []
  where
    go ids (Lam b e) | isId b = go (b:ids) e
    go ids (Lam b e)          = go ids e
    go ids (Cast e _)         = go ids e
    go ids body               = (reverse ids, body)

genExpr :: GenEnv -> CoreExpr -> LG Coq_ident
genExpr env (App e a) | isTypeArg a = genExpr env e 

genExpr env (Cast e _) = genExpr env e

genExpr env (Case scrut b _ [(DEFAULT, _, body)]) = do
    scrut_eval <- genExpr env scrut
    emitNamedInstr (varRawId b) $ noop hsTyP (ident scrut_eval)
    genExpr env body

genExpr env (Case scrut _ _ []) = do
    genExpr env scrut

genExpr env (Case scrut b _ alts) = do
    scrut_eval <- genExpr env scrut
    emitNamedInstr (varRawId b) $ noop hsTyP (ident scrut_eval)

    emitNamedInstr scrut_cast_raw_id $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident scrut_eval) scrut_cast_tyP))

    tagPtr <- emitInstr $ getElemPtr scrut_cast_tyP scrut_cast_ident [0,1]
    t <- emitInstr $ INSTR_Load False tagTy (tagTyP, ident tagPtr) Nothing

    emitTerm $ tagSwitch t [ (tagOf ac, caseAltEntryRawId b (tagOf ac))
                           | (ac, _, _) <- alts ]

    mapM_ genAlt alts

    res <- namedPhiBlock hsTyP (caseAltJoinRawId b)
        [ (caseAltRetIdent b (tagOf ac), caseAltExitRawId b (tagOf ac))
        | (ac, _, _) <- alts ]
    return res
  where
    scrut_cast_tyP | intPrimTy `eqType` idType b = intBoxTyP
                   | otherwise                   = dataConTyP


    tagSwitch :: Coq_ident -> [(Maybe Integer, Coq_local_id)] -> Coq_terminator
    tagSwitch tag ((_,l):xs) =
        TERM_Switch (tagTy,ident tag) (TYPE_Label, ID_Local l)
            [ ((tagTy, SV (VALUE_Integer n)), (TYPE_Label, ID_Local l))
            | (Just n, l) <- xs ]

    scrut_cast_raw_id = caseScrutCastedRawId b
    scrut_cast_ident = caseScrutCastedIdent b

    tagOf DEFAULT      = Nothing
    tagOf (DataAlt dc) = Just (fromIntegral (dataConTag dc))
    tagOf (LitAlt l)   = Just (litValue l)

    genAlt (ac, pats, rhs) = do
        startNamedBlock (caseAltEntryRawId b (tagOf ac))
        forM_ (zip [0..] pats) $ \(n,pat) -> do
            patPtr <- emitInstr $ getElemPtr dataConTyP scrut_cast_ident [0,2,n]
            emitNamedInstr (varRawId pat) $ INSTR_Load False hsTyP (hsTyP, ident patPtr) Nothing

        tmpId <- genExpr env rhs
        emitNamedInstr (caseAltRetRawId b (tagOf ac)) $ noop hsTyP (ident tmpId)
        namedBr1Block (caseAltExitRawId b (tagOf ac)) (caseAltJoinRawId b)

genExpr env (Let binds body) = do
    let (allocs, fills) = unzip [ genLetBind env v e | (v,e) <- flattenBinds [binds] ]
    sequence_ allocs
    sequence_ fills
    genExpr env body
  where
    pairs = flattenBinds [binds]

 -- Saturated data con application
 -- We could just use the normal code for function calls, but
 -- unboxed tuples do not actually exist as global names, so we
 -- have to do them here on the fly. So just do all of them here.
genExpr env e
    | (Var v, args) <- collectArgs e
    , Just dc <- isDataConWorkId_maybe v
    , let args' = filter isValArg args
    , not (null args')
    , length args' == dataConRepArity dc
    = do

    arg_locals <- mapM (genArg env) args'
    dc_local <- freshLocal
    let (alloc, fill) = allocateDataCon dc_local (fromIntegral (dataConTag dc)) (fromIntegral (dataConRepArity dc))
    alloc
    fill arg_locals
    return (ID_Local dc_local)

genExpr env e
    | (f, args) <- collectArgs e
    , let args' = filter isValArg args
    , not (null args') = do

    evaledFun <- genExpr env f
    args_locals <- mapM (genArg env) args'
    genFunctionCall evaledFun args_locals

genExpr env (Var v) | isUnliftedType (idType v) = do
    when (isGlobalId v && not (isTopLvl env v)) $ liftG $ noteExternalVar v
    return (varIdent env v)

genExpr env (Var v) = do
    when (isGlobalId v && not (isTopLvl env v)) $ liftG $ noteExternalVar v
    genEnterAndEval (varIdent env v)

genExpr env (Coercion _) = do
    liftG $ noteExternalVar coercionTokenId
    return (varIdent env coercionTokenId)

genExpr env (Lit (MachInt l)) = do
    liftG $ genIntegerLit l

genExpr env (Lit (MachWord l)) = do
    liftG $ genIntegerLit l

genExpr env (Lam {}) =
    pprTrace "genExpr" (text "lambda") $
    emitInstr $ noop hsTyP (SV (VALUE_Null))

genExpr env e =
    pprTrace "genExpr" (ppr e) $
    emitInstr $ noop hsTyP (SV (VALUE_Null))

genArg :: GenEnv -> CoreArg -> LG Coq_ident
genArg env (Cast e _) = genArg env e
genArg env (App e a) | isTyCoArg a = genArg env e
genArg env (Var v) = do
    when (isGlobalId v && not (isTopLvl env v )) $ liftG $ noteExternalVar v
    return $ varIdent env v
genArg env (Lit (MachInt l)) = do
    liftG $ genIntegerLit l
genArg env (Lit (MachWord l)) = do
    liftG $ genIntegerLit l
genArg env e = pprTrace "genArg" (ppr e) $
    emitInstr $ noop hsTyP (SV VALUE_Null) -- hack

genLetBind :: GenEnv -> Var -> CoreExpr -> (LG (), LG ())
genLetBind env v e
    | (Var f, args) <- collectArgs e
    , Just dc <- isDataConId_maybe f
    = let (alloc, fill) = allocateDataCon (varRawId v) (fromIntegral (dataConTag dc)) (fromIntegral (dataConRepArity dc))
          fill' = do
            arg_locals <- mapM (genArg env) (filter isValArg args)
            fill arg_locals
      in (alloc, fill')

genLetBind env v rhs | exprIsHNF rhs = (alloc, fill)
  where
    (params, body) = collectMoreValBinders rhs
    arity = fromIntegral $ length params
    env_size = fromIntegral $ length fvs

    fvs = filter isId $ exprsFreeVarsList [rhs]
    thisFunClosureTy = mkFunClosureTy arity env_size
    thisFunClosureTyP = TYPE_Pointer thisFunClosureTy

    thisFunTy = hsFunTy arity env_size
    thisFunTyP = TYPE_Pointer thisFunTy

    alloc = do
        closureRawPtr <- genMalloc thisFunClosureTyP
        emitNamedInstr (varRawId v) $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTyP (ident closureRawPtr) hsTyP))
        return ()

        liftG $ genFunCode

    fill = do
        castedPtr <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (varIdent env v)) thisFunClosureTyP))

        p <- emitInstr $ getElemPtr thisFunClosureTyP castedPtr [0,0]
        emitInstr $ INSTR_Store False (TYPE_Pointer enterFunTyP, ident p) (enterFunTyP, ident returnArgIdent) Nothing

        p <- emitInstr $ getElemPtr thisFunClosureTyP castedPtr [0,1]
        emitInstr $ INSTR_Store False (TYPE_Pointer thisFunTyP, ident p) (thisFunTyP, ident (funIdent env v)) Nothing

        p <- emitInstr $ getElemPtr thisFunClosureTyP castedPtr [0,2]
        emitInstr $ INSTR_Store False (arityTyP, ident p) (arityTy, SV (VALUE_Integer arity)) Nothing

        forM_ (zip [0..] fvs) $ \(n,fv) -> do
            p <- emitInstr $ getElemPtr thisFunClosureTyP castedPtr [0,3,n]
            emitInstr $ INSTR_Store False (hsTyP, ident p) (hsTyP, ident (varIdent env fv)) Nothing

    genFunCode = do
      blocks <- runLG $ do
        -- load free variables
        castedClosPtr <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident closIdent) (envTyP env_size)))
        forM_ (zip [0..] fvs) $ \(n,fv) -> do
            p <- emitInstr $ getElemPtr (envTyP env_size) castedClosPtr [0,n]
            emitNamedInstr (varRawId fv) $ INSTR_Load False hsTyP (TYPE_Pointer hsTyP, ident p) Nothing
        -- evaluate body
        res <- genExpr env body
        -- TODO: update thunk here
        returnFromFunction res
      emitTL $ TLDef $ mkHsFunDefinition
            LINKAGE_Internal
            (funRawId v)
            [ varRawId p | p <- params ]
            env_size
            blocks

genLetBind env v rhs = (alloc, fill)
  where
    alloc = do
        thunkRawPtr <- genMalloc thisThunkTyP
        emitNamedInstr (varRawId v) $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTyP (ident thunkRawPtr) hsTyP))

        liftG $ genThunkCode

    fill = do
        castedPtr <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (varIdent env v)) thisThunkTyP))

        p <- emitInstr $ getElemPtr thisThunkTyP castedPtr [0,0]
        emitInstr $ INSTR_Store False (enterFunTyP, ident p) (enterFunTyP, ident (funIdent env v)) Nothing

        forM_ (zip [0..] fvs) $ \(n,fv) -> do
            p <- emitInstr $ getElemPtr thisThunkTyP castedPtr [0,1,n]
            emitInstr $ INSTR_Store False (hsTyP, ident p) (hsTyP, ident (varIdent env fv)) Nothing

    genThunkCode = do
      blocks <- runLG $ do
        -- load free variables
        castedClosPtr <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident closIdent) thisThunkTyP))
        forM_ (zip [0..] fvs) $ \(n,fv) -> do
            p <- emitInstr $ getElemPtr thisThunkTyP castedClosPtr [0,1,n]
            emitNamedInstr (varRawId fv) $ INSTR_Load False hsTyP (TYPE_Pointer hsTyP, ident p) Nothing
        -- evaluate body
        res <- genExpr env rhs
        -- TODO: update thunk here
        returnFromFunction res
      emitTL $ TLDef $ mkEnterFunDefinition
            LINKAGE_Internal
            (funRawId v)
            blocks

    fvs = filter isId $ exprsFreeVarsList [rhs]
    env_size = fromIntegral $ length fvs
    thisThunkTyP = TYPE_Pointer $ mkThunkTy env_size



funIdent :: GenEnv -> Id -> Coq_ident
funIdent env v = ID_Global (funRawId v)
funRawId :: Id ->  Coq_raw_id
funRawId v = Name (codeNameStr (getName v) ++ "_fun")

varIdent :: GenEnv -> Id -> Coq_ident
varIdent env v
    | isGlobalId v || isTopLvl env v
    = ID_Global (varRawId v)
    | otherwise
    = ID_Local (varRawId v)

varRawId :: Id ->  Coq_raw_id
varRawId v = Name (codeNameStr (getName v))


varRawIdTmp :: Id ->  Coq_raw_id
varRawIdTmp v = Name (codeNameStr (getName v) ++ "_tmp")


caseScrutCastedIdent :: Var -> Coq_ident
caseScrutCastedIdent n = ID_Local (caseScrutCastedRawId n)

caseScrutCastedRawId :: Var -> Coq_raw_id
caseScrutCastedRawId n = Name (codeNameStr (getName n) ++ "_casted")

caseAltEntryIdent :: Var -> Maybe Integer -> Coq_ident
caseAltEntryIdent v mbi = ID_Local (caseAltEntryRawId v mbi)

caseAltEntryRawId :: Var -> Maybe Integer -> Coq_raw_id
caseAltEntryRawId n Nothing  = Name (codeNameStr (getName n) ++ "_br_def")
caseAltEntryRawId n (Just i) = Name (codeNameStr (getName n) ++ "_br_" ++ show i)

caseAltRetIdent :: Var -> Maybe Integer -> Coq_ident
caseAltRetIdent v mbi = ID_Local (caseAltRetRawId v mbi)

caseAltRetRawId :: Var -> Maybe Integer -> Coq_raw_id
caseAltRetRawId n Nothing  = Name (codeNameStr (getName n) ++ "_br_ret")
caseAltRetRawId n (Just i) = Name (codeNameStr (getName n) ++ "_br_ret_" ++ show i)

caseAltExitIdent :: Var -> Maybe Integer -> Coq_ident
caseAltExitIdent v mbi = ID_Local (caseAltExitRawId v mbi)

caseAltExitRawId :: Var -> Maybe Integer -> Coq_raw_id
caseAltExitRawId n Nothing  = Name (codeNameStr (getName n) ++ "_br_ex")
caseAltExitRawId n (Just i) = Name (codeNameStr (getName n) ++ "_br_ex_" ++ show i)

caseAltJoin :: Var -> Coq_ident
caseAltJoin n = ID_Local (Name (codeNameStr (getName n) ++ "_br_join"))

caseAltJoinIdent :: Var -> Coq_ident
caseAltJoinIdent v = ID_Local (caseAltJoinRawId v)

caseAltJoinRawId :: Var -> Coq_raw_id
caseAltJoinRawId n = Name (codeNameStr (getName n) ++ "_br_join")

