{-# LANGUAGE TupleSections #-}
module Veggies.CodeGen where

import Data.List
import Data.Char
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
import ForeignCall
import FastString

import Ollvm_ast

import Debug.Trace
import GHC.Stack

import Veggies.GenMonad
import Veggies.CodeGenTypes
import Veggies.ASTUtils
import Veggies.Common
import Veggies.FFI


data GenEnv = GenEnv
    { topLvls :: IdSet
    }

genCode :: ModuleName -> [TyCon] -> CoreProgram -> Coq_modul
genCode name tycons binds
    = mkCoqModul (moduleNameString name) $ concat
        [ globals
        , defaultTyDecls
        ]
  where
    env = mkGenEnv (flattenBinds binds)

    globals = runG $ do
        genStaticIntLits
        sequence_ [genStaticVal env v e | (v,e) <- flattenBinds binds ]

mkGenEnv :: [(Id, CoreExpr)] -> GenEnv
mkGenEnv pairs = GenEnv { topLvls = mkVarSet (map fst pairs) }

isTopLvl :: GenEnv -> Id -> Bool
isTopLvl env v = v `elemVarSet` topLvls env

genStaticVal :: GenEnv -> Var -> CoreExpr -> G ()
genStaticVal env v (Cast e _)               = genStaticVal env v e
genStaticVal env v (Lam b e) | not (isId b) = genStaticVal env v e
genStaticVal env v (App e a) | isTyCoArg a  = genStaticVal env v e

-- The top level binding for a nullary data constructor
genStaticVal env v _rhs
    | Just dc <- isDataConWorkId_maybe v
    , dataConRepArity dc == 0
    = emitAliasedGlobal LINKAGE_External (varRawId v) hsTy (mkDataConTy 0) $
        SV $ VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                          , (TYPE_I 64, SV (VALUE_Integer (fromIntegral (dataConTag dc))))
                          , (envTy 0 , SV (VALUE_Array []))
                          ]
-- The top level binding for a non-nullary data constructor
genStaticVal env v _rhs
    | Just dc <- isDataConWorkId_maybe v
    , let arity = fromIntegral (dataConRepArity dc)
    = do
        let paramName n = "dcArg_" ++ show n
            param_raw_ids = [ Name (paramName n) | n <- [0..arity-1] ]
        emitHsFun LINKAGE_Private (funRawId (dataConWorkId dc)) [] $ do
            loadArgs param_raw_ids
            (dcIdent, fill) <- allocateDataCon (fromIntegral (dataConTag dc)) (fromIntegral (dataConRepArity dc))
            fill $ map ID_Local param_raw_ids
            return dcIdent
        emitAliasedGlobal LINKAGE_External (varRawId v) hsTy (mkFunClosureTy 0) $
            SV $ VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                              , (hsFunTyP,    ident (funIdent env v))
                              , (TYPE_I 64,   SV (VALUE_Integer arity))
                              , (envTy 0 ,    SV (VALUE_Array []))
                              ]

-- A top-level data con application
genStaticVal env v rhs
    | (Var f, args) <- collectMoreValArgs rhs
    , Just dc <- isDataConWorkId_maybe f
    , let val_args = mapMaybe getStaticArg args
    , not (null val_args)
    = do
    args_idents <- map (hsTyP,) <$> mapM genStaticArg val_args
    let arity = fromIntegral (length args_idents)
    unless (arity == fromIntegral (dataConRepArity dc)) $ do
           pprTrace "genStaticVal arity" (ppr v <+> ppr rhs <+> ppr (dataConRepArity dc) <+> ppr (fromIntegral arity::Int)) (return ())

    emitAliasedGlobal linkage (varRawId v) hsTy (mkDataConTy arity) $
        SV $ VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                          , (TYPE_I 64, SV (VALUE_Integer (fromIntegral (dataConTag dc))))
                          , (envTy arity , SV (VALUE_Array args_idents))
                          ]
  where
    linkage = if isExternalName (idName v) then LINKAGE_External else LINKAGE_Private

    cast arity val = SV (OP_Conversion Bitcast (mkDataConTy arity) val hsTyP)

    getStaticArg :: CoreExpr -> Maybe CoreExpr
    getStaticArg (Cast e _)               = getStaticArg e
    getStaticArg (App e a) | isTyCoArg a  = getStaticArg e
    getStaticArg (Lam v e) | not (isId v) = getStaticArg e
    getStaticArg (Case e _ _ [])          = getStaticArg e -- See Note [Empty case is trivial]
    getStaticArg (Var v)                  = Just (Var v)
    getStaticArg (Lit l)                  = Just (Lit l)
    getStaticArg _                        = Nothing

    genStaticArg :: CoreExpr -> G Coq_value
    genStaticArg (Var v) = do
        return $ ident (varIdent env v)
    genStaticArg (Lit (MachInt l)) = do
        lit <- genIntegerLit l
        return (ident lit)
    genStaticArg (Lit (MachWord l)) = do
        lit <- genIntegerLit l
        return (ident lit)
    genStaticArg (Lit (MachChar c)) = do
        lit <- genIntegerLit (fromIntegral (ord c))
        return (ident lit)
    genStaticArg (Lit (MachStr s)) = do
        lit <- genByteStringLit s
        return (ident lit)
    genStaticArg (Lit MachNullAddr) = do
        return (ident nullPtrBoxIdent)
    genStaticArg (Lit l) =
        pprTrace "genStaticArg" (ppr l) $
        return $ SV (VALUE_Null)
    genStaticArg e = pprPanic "genStaticArg" (ppr e)


-- An alias
genStaticVal env v (Var v2) = do
    emitAliasedGlobal linkage (varRawId v) hsTy indTy $
        SV $ VALUE_Struct [ (enterFunTyP, ident indirectionIdent)
                          , (hsTyP,       ident (varIdent env v2))
                          ]
  where
    linkage = if isExternalName (idName v) then LINKAGE_External else LINKAGE_Private

-- A top-level function
genStaticVal env v rhs | exprIsHNF rhs = do
    unless (arity > 0) $ pprPanic "genStaticVal" (ppr v <+> ppr rhs)

    emitHsFun LINKAGE_Private (funRawId v) [] $ do
        loadArgs [ varRawId p | p <- params ]
        genExpr env body

    emitAliasedGlobal linkage (varRawId v) hsTy (mkFunClosureTy 0) $
        SV $ VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                          , (hsFunTyP,    ident (funIdent env v))
                          , (TYPE_I 64,   SV (VALUE_Integer arity))
                          , (envTy 0 ,    SV (VALUE_Array []))
                          ]
  where
    (params, body) = collectMoreValBinders rhs
    arity = fromIntegral (length params)
    linkage = if isExternalName (idName v) then LINKAGE_External else LINKAGE_Private

-- A static thunk
genStaticVal env v rhs = do
    blocks <- runLG $ do
        ret <- genExpr env rhs
        -- update the thunk
        overrideWithIndirection closIdent ret
        emitTerm $ TERM_Ret (hsTyP, ident ret)
    emitTL $ TLDef $ mkEnterFunDefinition
        LINKAGE_Internal
        (funRawId v)
        blocks
    emitAliasedGlobal linkage (varRawId v) hsTy (mkThunkTy 0) $
        SV $ VALUE_Struct [ (enterFunTyP, ident (funIdent env v))
                          , (envTy 0,     mkThunkArray [])
                          ]
  where
    linkage = if isExternalName (idName v) then LINKAGE_External else LINKAGE_Private


collectMoreValBinders :: CoreExpr -> ([Id], CoreExpr)
collectMoreValBinders = go []
  where
    go ids (Lam b e) | isId b = go (b:ids) e
    go ids (Lam b e)          = go ids e
    go ids (Cast e _)         = go ids e
    go ids body               = (reverse ids, body)

collectMoreValArgs :: CoreExpr -> (CoreExpr, [CoreArg])
collectMoreValArgs expr = go expr []
  where
    go (Cast e _) as               = go e as
    go (App e a)  as | isTypeArg a = go e as
    go (App e a)  as               = go e (a:as)
    go e          as               = (e, as)

genExpr :: GenEnv -> CoreExpr -> LG Coq_ident
genExpr env (Lam v e) | not (isId v) = genExpr env e
genExpr env (App e a) | isTypeArg a = genExpr env e
genExpr env (Cast e _) = genExpr env e
genExpr env (Case scrut _ _ []) = genExpr env scrut

genExpr env (Case scrut b _ [(DEFAULT, _, body)]) = do
    scrut_eval <- genExpr env scrut
    emitNamedInstr (varRawId b) $ noop hsTyP (ident scrut_eval)
    genExpr env body


genExpr env (Case scrut b _ alts) = do
    scrut_eval <- genExpr env scrut
    emitNamedInstr (varRawId b) $ noop hsTyP (ident scrut_eval)

    emitNamedInstr scrut_cast_raw_id $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident scrut_eval) scrut_cast_tyP))

    case alts of
        [(_, pats, rhs)] ->
            genAltBody pats rhs
        _ -> do
            tagPtr <- emitInstr $ getElemPtr scrut_cast_tyP scrut_cast_ident [0,1]
            t <- emitInstr $ INSTR_Load False tagTy (tagTyP, ident tagPtr) Nothing

            emitTerm $ tagSwitch t [ (tagOf ac, caseAltEntryRawId b (tagOf ac))
                                   | (ac, _, _) <- alts ]

            phiArgs <- mapM genAlt alts

            namedPhiBlock hsTyP (caseAltJoinRawId b) phiArgs
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
        ret <- genAltBody pats rhs
        namedBr1Block (caseAltExitRawId b (tagOf ac)) (caseAltJoinRawId b)
        return (ident ret, ID_Local (caseAltExitRawId b (tagOf ac)))

    genAltBody pats rhs = do
        forM_ (zip [0..] (filter isId pats)) $ \(n,pat) -> do
            patPtr <- emitInstr $ getElemPtr dataConTyP scrut_cast_ident [0,2,n]
            emitNamedInstr (varRawId pat) $ INSTR_Load False hsTyP (TYPE_Pointer hsTyP, ident patPtr) Nothing

        genExpr env rhs

genExpr env (Let binds body) = do
    fills <- sequence [ genLetBind env v e | (v,e) <- flattenBinds [binds] ]
    sequence_ fills
    genExpr env body
  where
    pairs = flattenBinds [binds]

 -- Saturated data con application
 -- We could just use the normal code for function calls, but
 -- unboxed tuples do not actually exist as global names, so we
 -- have to do them here on the fly. So just do all of them here.
genExpr env e
    | (Var v, args) <- collectMoreValArgs e
    , Just dc <- isDataConWorkId_maybe v
    , not (null args)
    , length args == dataConRepArity dc
    = do

    arg_locals <- mapM (genArg env) args
    (dc_local, fill) <- allocateDataCon (fromIntegral (dataConTag dc)) (fromIntegral (dataConRepArity dc))
    fill arg_locals
    return dc_local

genExpr env e
    | (Var v, args) <- collectMoreValArgs e
    , Just (CCall (CCallSpec (StaticTarget _ l _ _) _ _)) <- isFCallId_maybe v = do
    args_locals <- mapM (genArg env) args
    mkFFICall (unpackFS l) args_locals

genExpr env e
    | (f, args) <- collectMoreValArgs e
    , not (null args) = do

    evaledFun <- genExpr env f
    args_locals <- mapM (genArg env) args
    genFunctionCall evaledFun args_locals

genExpr env (Var v)
    | Just (CCall (CCallSpec (StaticTarget _ l _ _) _ _)) <- isFCallId_maybe v =
    pprPanic "genExpr FFI" (ppr v) 

genExpr env (Var v) | isUnliftedType (idType v) = do
    return (varIdent env v)

genExpr env (Var v) = do
    genEnterAndEval (varIdent env v)

genExpr env (Coercion _) = do
    return (varIdent env coercionTokenId)

genExpr env (Lit (MachInt l)) = do
    liftG $ genIntegerLit l
genExpr env (Lit (MachWord l)) = do
    liftG $ genIntegerLit l
genExpr env (Lit (MachChar c)) = do
    liftG $ genIntegerLit (fromIntegral (ord c))

genExpr env (Lit (MachStr s)) = do
    liftG $ genByteStringLit s

genExpr env (Lit MachNullAddr) = do
    return nullPtrBoxIdent

genExpr env (Lam {}) =
    pprTrace "genExpr" (text "lambda") $
    emitInstr $ noop hsTyP (SV (VALUE_Null))

genExpr env e =
    pprTrace "genExpr" (ppr e) $
    emitInstr $ noop hsTyP (SV (VALUE_Null))

genArg :: GenEnv -> CoreArg -> LG Coq_ident
genArg env (Cast e _)               = genArg env e
genArg env (App e a) | isTyCoArg a  = genArg env e
genArg env (Lam v e) | not (isId v) = genArg env e
genArg env (Case e _ _ [])          = genArg env e -- See Note [Empty case is trivial]
genArg env (Var v) = do
    return $ varIdent env v
genArg env (Lit (MachInt l)) = do
    liftG $ genIntegerLit l
genArg env (Lit (MachWord l)) = do
    liftG $ genIntegerLit l
genArg env (Lit (MachChar c)) = do
    liftG $ genIntegerLit (fromIntegral (ord c))
genArg env (Lit (MachStr s)) = do
    liftG $ genByteStringLit s
genArg env (Lit MachNullAddr) = do
    return nullPtrBoxIdent
genArg env e = pprTrace "genArg" (ppr e) $
    emitInstr $ noop hsTyP (SV VALUE_Null) -- hack

genLetBind :: GenEnv -> Var -> CoreExpr -> LG (LG ())

-- A let-bound data constructor
genLetBind env v (Cast e _) = genLetBind env v e
genLetBind env v e
    | (Var f, args) <- collectMoreValArgs e
    , Just dc <- isDataConWorkId_maybe f
    = do
      (dc_local, fill) <- allocateDataCon (fromIntegral (dataConTag dc)) (fromIntegral (dataConRepArity dc))
      emitNamedInstr (varRawId v) $ noop hsTyP (ident dc_local)
      let fill' = do
          arg_locals <- mapM (genArg env) args
          fill arg_locals
      return fill'

-- A let-bound function
genLetBind env v rhs | exprIsHNF rhs =
    if arity > 0 then alloc
                 else pprPanic "genLetBind" (ppr v <+> ppr rhs)
  where
    (params, body) = collectMoreValBinders rhs
    arity = fromIntegral $ length params
    env_size = fromIntegral $ length fvs

    fvs = filter isId $ exprsFreeVarsList [rhs]
    thisFunClosureTy = mkFunClosureTy env_size
    thisFunClosureTyP = TYPE_Pointer thisFunClosureTy

    alloc = do
        closureRawPtr <- genMalloc thisFunClosureTyP
        emitNamedInstr (varRawId v) $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTy (ident closureRawPtr) hsTyP))

        liftG $ genFunCode

        return fill

    fill = do
        castedPtr <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (varIdent env v)) thisFunClosureTyP))

        p <- emitInstr $ getElemPtr thisFunClosureTyP castedPtr [0,0]
        emitVoidInstr $ INSTR_Store False (TYPE_Pointer enterFunTyP, ident p) (enterFunTyP, ident returnArgIdent) Nothing

        p <- emitInstr $ getElemPtr thisFunClosureTyP castedPtr [0,1]
        emitVoidInstr $ INSTR_Store False (TYPE_Pointer hsFunTyP, ident p) (hsFunTyP, ident (funIdent env v)) Nothing

        p <- emitInstr $ getElemPtr thisFunClosureTyP castedPtr [0,2]
        emitVoidInstr $ INSTR_Store False (arityTyP, ident p) (arityTy, SV (VALUE_Integer arity)) Nothing

        envPtr <- emitInstr $ getElemPtr thisFunClosureTyP castedPtr [0,3]
        storeEnv env_size envPtr [ varIdent env fv | fv <- fvs ]

    genFunCode = do
      emitHsFun LINKAGE_Internal (funRawId v) [ varRawId p | p <- fvs ] $ do
        loadArgs [ varRawId p | p <- params ]
        genExpr env body

-- A let-bound thunk
genLetBind env v rhs = alloc
  where
    alloc = do
        thunkRawPtr <- genMalloc thisThunkTyP
        emitNamedInstr (varRawId v) $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTy (ident thunkRawPtr) hsTyP))

        liftG $ genThunkCode

        return fill

    fill = do
        castedPtr <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (varIdent env v)) thisThunkTyP))

        p <- emitInstr $ getElemPtr thisThunkTyP castedPtr [0,0]
        emitVoidInstr $ INSTR_Store False (TYPE_Pointer enterFunTyP, ident p) (enterFunTyP, ident (funIdent env v)) Nothing

        forM_ (zip [0..] fvs) $ \(n,fv) -> do
            p <- emitInstr $ getElemPtr thisThunkTyP castedPtr [0,1,n]
            emitVoidInstr $ INSTR_Store False (TYPE_Pointer hsTyP, ident p) (hsTyP, ident (varIdent env fv)) Nothing

    genThunkCode = do
      blocks <- runLG $ do
        -- load free variables
        castedClosPtr <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident closIdent) thisThunkTyP))
        forM_ (zip [0..] fvs) $ \(n,fv) -> do
            p <- emitInstr $ getElemPtr thisThunkTyP castedClosPtr [0,1,n]
            emitNamedInstr (varRawId fv) $ INSTR_Load False hsTyP (TYPE_Pointer hsTyP, ident p) Nothing
        -- evaluate body
        ret <- genExpr env rhs

        -- update the thunk
        overrideWithIndirection closIdent ret
        emitTerm $ TERM_Ret (hsTyP, ident ret)
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

