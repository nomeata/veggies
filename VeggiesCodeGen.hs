{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
module VeggiesCodeGen where

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

data GenEnv = GenEnv
    { topLvls :: IdSet
    , topLvlArities :: VarEnv Arity
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
        ]

mkGenEnv :: [(Id, CoreExpr)] -> GenEnv
mkGenEnv pairs =
    GenEnv { topLvls = mkVarSet (map fst pairs)
           , topLvlArities = mkVarEnv
                [ (v, length (fst (collectMoreValBinders e))) | (v,e) <- pairs ]
           }

getIdArity :: GenEnv -> Id -> Arity
getIdArity env v | isExternalName (idName v)                    = idArity v
                 | Just a <- lookupVarEnv (topLvlArities env) v = a
                 | otherwise                                    = idArity v

isTopLvl :: GenEnv -> Id -> Bool
isTopLvl env v = v `elemVarSet` topLvls env

defaultTyDecls :: [TopLevelThing]
defaultTyDecls =
    [ TLTyDef $ Coq_mk_type_decl (Name "hs")    mkClosureTy
    , TLTyDef $ Coq_mk_type_decl (Name "thunk") (mkThunkTy 0)
    , TLTyDef $ Coq_mk_type_decl (Name "dc")    (mkDataConTy 0)
    , TLTyDef $ Coq_mk_type_decl (Name "int")   mkIntBoxTy
    ]

returnArgDecl :: TopLevelThing
returnArgDecl =  TLDecl $ mkEnterFunDeclaration
    LINKAGE_External
    (Name "rts_returnArg")

returnArgIdent :: Coq_ident
returnArgIdent = ID_Global (Name "rts_returnArg")

mkClosureTy :: Coq_typ
mkClosureTy = TYPE_Struct [ enterFunTyP ]

hsTy :: Coq_typ
hsTy = TYPE_Identified (ID_Global (Name "hs"))

hsTyP :: Coq_typ
hsTyP = TYPE_Pointer (TYPE_Identified (ID_Global (Name "hs")))

-- An explicit, global function to call
hsFunTy :: Int -> Int -> Coq_typ
hsFunTy n m = TYPE_Function hsTyP (envTyP m : replicate n hsTyP)

-- Entering a closure
enterFunTy  = TYPE_Function hsTyP [hsTyP]
enterFunTyP = TYPE_Pointer enterFunTy

mkThunkTy :: Int -> Coq_typ
mkThunkTy n = TYPE_Struct [ enterFunTyP, envTy n' ]
  where n' = max 1 n

-- space for at least one element!
mkThunkArray :: [Coq_tvalue] -> Coq_value
mkThunkArray [] = SV (VALUE_Array [(hsTyP, SV VALUE_Null)])
mkThunkArray xs = SV (VALUE_Array xs)

thunkTy :: Coq_typ
thunkTy = TYPE_Identified (ID_Global (Name "thunk"))

thunkTyP :: Coq_typ
thunkTyP = TYPE_Pointer thunkTy

tagTy = TYPE_I 64
tagTyP = TYPE_Pointer tagTy

arityTy = TYPE_I 64
arityTyP = TYPE_Pointer arityTy

mkDataConTy n = TYPE_Struct [ enterFunTyP, tagTy, TYPE_Array n hsTyP ]

envTy m = TYPE_Array m hsTyP
envTyP m = TYPE_Pointer (envTy m)

mkFunClosureTy n m =
    TYPE_Struct [ enterFunTyP
                , TYPE_Pointer (hsFunTy n m)
                , arityTy
                , envTy m
                ]

dataConTy = TYPE_Identified (ID_Global (Name "dc"))
dataConTyP = TYPE_Pointer dataConTy

mkIntBoxTy = TYPE_Struct [ enterFunTyP, TYPE_I 64 ]
intBoxTy = TYPE_Identified (ID_Global (Name "int"))
intBoxTyP = TYPE_Pointer intBoxTy

genStaticVal :: GenEnv -> Var -> CoreExpr -> G ()
genStaticVal env v rhs
    | getIdArity env v == 0
    , Just dc <- isDataConId_maybe v
    = do
    let val = SV $VALUE_Struct [ (enterFunTyP,                     ident returnArgIdent)
                               , (TYPE_I 64, SV (VALUE_Integer (dataConTag dc)))
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
    let arity = length args_idents
        val = SV $ VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                                , (TYPE_I 64, SV (VALUE_Integer (dataConTag dc)))
                                , (envTy arity , SV (VALUE_Array args_idents))
                                ]
    unless (arity == dataConRepArity dc) $ do
           pprTrace "genStaticVal arity" (ppr v <+> ppr rhs <+> ppr (dataConRepArity dc) <+> ppr arity) (return ())

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
        lit <- genIntegerLit (fromIntegral l)
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
    | length params /= getIdArity env v
    = pprPanic "genTopLvlFunction" (ppr v <+> ppr rhs <+> ppr (getIdArity env v))
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

genIntegerLit :: Int -> G Coq_ident
genIntegerLit l = do
    litNameTmp <- freshGlobal
    litName <- freshGlobal

    let val = SV $ VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                                , (TYPE_I 64, SV (VALUE_Integer (fromIntegral l)))
                                ]

    emitTL $ TLGlobal $ Coq_mk_global
         litNameTmp
         intBoxTy
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
         litName
         hsTyP
         (SV (OP_Conversion Bitcast intBoxTy (ident (ID_Global litNameTmp)) hsTyP))
         (Just LINKAGE_Private)
         Nothing
         Nothing
         Nothing
         False

    return $ ID_Global litName

genMalloc :: Coq_typ -> LG Coq_ident
genMalloc t = do
    -- http://stackoverflow.com/a/30830445/946226
    offset <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr t (t, SV VALUE_Null) [(TYPE_I 32, SV (VALUE_Integer 1))]))
    size <- emitInstr $ INSTR_Op (SV (OP_Conversion Ptrtoint t (ident offset) (TYPE_I 64)))
    emitInstr $ INSTR_Call (mallocTy, ID_Global (Name "malloc")) [(TYPE_I 64, ident size)]

allocateDataCon :: Coq_raw_id -> DataCon -> (LG (), [Coq_ident] ->  LG ())
allocateDataCon dcName dc = (alloc, fill)
  where
    alloc = do
        dcRawPtr <- genMalloc thisDataConTyP
        emitNamedInstr dcName $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTyP (ident dcRawPtr) hsTyP))

    fill args = do
        let dcClosure = ID_Local dcName
        dcCasted <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident dcClosure) thisDataConTyP))

        codePtr <- emitInstr $ getElemPtr thisDataConTyP dcCasted [0,0]
        emitInstr $ INSTR_Store False (enterFunTyP, ident codePtr) (enterFunTyP, ident returnArgIdent) Nothing

        tagPtr <- emitInstr $ getElemPtr thisDataConTyP dcCasted [0,1]
        emitInstr $ INSTR_Store False (tagTyP, ident tagPtr) (tagTy, SV (VALUE_Integer (dataConTag dc))) Nothing

        forM_ (zip [0..] args) $ \(n, arg) -> do
            p <- emitInstr $ getElemPtr thisDataConTyP dcCasted [0,2,n]
            emitInstr $ INSTR_Store False (hsTyP, ident p) (hsTyP, ident arg) Nothing

    thisDataConTy = mkDataConTy (dataConRepArity dc)
    thisDataConTyP = TYPE_Pointer thisDataConTy

genDataConWorker :: DataCon -> G ()
genDataConWorker dc = do
    blocks <- runLG $ do
        let (alloc, fill) = allocateDataCon (Name "dc") dc
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

mallocRetTyP = TYPE_Pointer (TYPE_I 8)
mallocTy = TYPE_Function mallocRetTyP [TYPE_I 64]

mallocDecl :: TopLevelThing
mallocDecl = TLDecl $ Coq_mk_declaration
    (Name "malloc")
    mallocTy
    ([],[[]])
    Nothing
    Nothing
    Nothing
    Nothing
    []
    Nothing
    Nothing
    Nothing


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

-- Generating top-level definitions
type G = WriterT [TopLevelThing] (WriterT [Var] (State Int))
-- Also generting instructions
type LG = WriterT [Coq_terminator -> Coq_block] (StateT Int G)

runG :: G () -> ([TopLevelThing], [Var])
runG g = evalState (runWriterT (execWriterT g)) 0

runLG :: LG () -> G ([Coq_block])
runLG lg = combine . connect <$> evalStateT (execWriterT lg) 0
  where
    final_term = error "Unterminated last block"
    connect [mkBlock]          = [mkBlock final_term]
    connect (mkBlock:mkBlocks) = mkBlock (TERM_Br_1 tident) : blocks'
      where blocks' = connect mkBlocks
            tident = (TYPE_Label, ID_Local (blk_id (head blocks')))
    combine ( (Coq_mk_block i1 bs1 (TERM_Br_1 (TYPE_Label, ID_Local (Anon br))) _)
            : (Coq_mk_block (Anon i2) bs2 t v)
            : blocks ) | br == i2
            = combine (Coq_mk_block i1 (bs1 ++ bs2) t v : blocks)
    combine (b:bs) = b : combine bs
    combine [] = []

liftG :: G a -> LG a
liftG = lift . lift

freshGlobal :: G Coq_local_id
freshGlobal = fmap Anon $ lift $ lift $ state (id &&& (+1))

freshLocal :: LG Coq_local_id
freshLocal = fmap Anon $ lift $ state (id &&& (+1))

noteExternalVar :: Var -> G ()
noteExternalVar v = lift $ tell [v]

emitTL :: TopLevelThing -> G ()
emitTL tlt = tell [tlt]

emitTerm :: Coq_terminator -> LG ()
emitTerm t = do
    blockId <- freshLocal
    tell [\_ -> Coq_mk_block blockId [] t (IVoid 0)]

emitInstr :: Coq_instr -> LG Coq_ident
emitInstr instr = do
    instrId <- freshLocal
    emitNamedInstr instrId instr
    return (ID_Local instrId)

emitNamedInstr :: Coq_local_id -> Coq_instr -> LG ()
emitNamedInstr instrId instr = do
    blockId <- freshLocal
    tell [\t -> Coq_mk_block blockId [(IId instrId, instr)] t (IVoid 0)]

namedBlock :: Coq_local_id -> LG ()
namedBlock blockId = do
    tell [\t -> Coq_mk_block blockId [] t (IVoid 0)]

namedBr1Block :: Coq_local_id -> Coq_local_id -> LG ()
namedBr1Block blockId toBlockId = do
    tell [\_ -> Coq_mk_block blockId [] (TERM_Br_1 (TYPE_Label, ID_Local toBlockId)) (IVoid 0)]

namedPhiBlock :: Coq_typ -> Coq_block_id -> [(Coq_ident, Coq_block_id)] -> LG Coq_ident
namedPhiBlock ty blockId pred = do
    tmpId <- freshLocal
    let phi = (IId tmpId, INSTR_Phi ty [ (i, SV (VALUE_Ident (ID_Local l))) | (i,l) <- pred ])
    tell [\t -> Coq_mk_block blockId [phi] t (IVoid 0)]
    return (ID_Local tmpId)

---

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


    tagSwitch :: Coq_ident -> [(Maybe Int, Coq_local_id)] -> Coq_terminator
    tagSwitch tag ((_,l):xs) =
        TERM_Switch (tagTy,ident tag) (TYPE_Label, ID_Local l)
            [ ((tagTy, SV (VALUE_Integer n)), (TYPE_Label, ID_Local l))
            | (Just n, l) <- xs ]

    scrut_cast_raw_id = caseScrutCastedRawId b
    scrut_cast_ident = caseScrutCastedIdent b

    tagOf DEFAULT      = Nothing
    tagOf (DataAlt dc) = Just (dataConTag dc)
    tagOf (LitAlt l)   = Just (fromIntegral (litValue l))

    genAlt (ac, pats, rhs) = do
        namedBlock (caseAltEntryRawId b (tagOf ac))
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
    let (alloc, fill) = allocateDataCon dc_local dc
    alloc
    fill arg_locals
    return (ID_Local dc_local)

genExpr env e
    | (f, args) <- collectArgs e
    , let args' = filter isValArg args
    , not (null args') = do
    let arity = length args'
    let thisFunClosTyP = TYPE_Pointer (mkFunClosureTy arity 0)
    let thisFunTyP = TYPE_Pointer (hsFunTy arity 0)

    evaledFun <- genExpr env f

    castedFun <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident evaledFun) thisFunClosTyP))
    codePtr <- emitInstr $ getElemPtr thisFunClosTyP castedFun [0,1]
    code <- emitInstr $ INSTR_Load False thisFunTyP (thisFunTyP, ident codePtr) Nothing

    closPtr <- emitInstr $ getElemPtr thisFunClosTyP castedFun [0,3]
    args_locals <- mapM (genArg env) args'
    emitInstr $ INSTR_Call (thisFunTyP, code) $
        (envTyP 0, ident closPtr) : [(hsTyP, ident a) | a <- args_locals ]
  where

genExpr env (Var v) | isUnliftedType (idType v) = do
    when (isGlobalId v && not (isTopLvl env v)) $ liftG $ noteExternalVar v
    return (varIdent env v)

genExpr env (Var v) = do
    when (isGlobalId v && not (isTopLvl env v)) $ liftG $ noteExternalVar v
    codePtr <- emitInstr $ getElemPtr hsTyP (varIdent env v) [0,0]
    code <- emitInstr $ INSTR_Load False enterFunTyP (enterFunTyP, ident codePtr) Nothing
    emitInstr $ INSTR_Call (enterFunTyP, code) [(hsTyP, ident (varIdent env v))]

genExpr env (Coercion _) = do
    liftG $ noteExternalVar coercionTokenId
    return (varIdent env coercionTokenId)

genExpr env (Lit (MachInt l)) = do
    liftG $ genIntegerLit (fromIntegral l)

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
    liftG $ genIntegerLit (fromIntegral l)
genArg env e = pprTrace "genArg" (ppr e) $
    emitInstr $ noop hsTyP (SV VALUE_Null) -- hack

genLetBind :: GenEnv -> Var -> CoreExpr -> (LG (), LG ())
genLetBind env v e
    | (Var f, args) <- collectArgs e
    , Just dc <- isDataConId_maybe f
    = let (alloc, fill) = allocateDataCon (varRawId v) dc
          fill' = do
            arg_locals <- mapM (genArg env) (filter isValArg args)
            fill arg_locals
      in (alloc, fill')

genLetBind env v rhs | exprIsHNF rhs = (alloc, fill)
  where
    (params, body) = collectMoreValBinders rhs
    arity = length params

    fvs = filter isId $ exprsFreeVarsList [rhs]
    thisFunClosureTy = mkFunClosureTy arity (length fvs)
    thisFunClosureTyP = TYPE_Pointer thisFunClosureTy

    thisFunTy = hsFunTy arity (length fvs)
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
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident closIdent) (envTyP (length fvs))))
        forM_ (zip [0..] fvs) $ \(n,fv) -> do
            p <- emitInstr $ getElemPtr (envTyP (length fvs)) castedClosPtr [0,n]
            emitNamedInstr (varRawId fv) $ INSTR_Load False hsTyP (TYPE_Pointer hsTyP, ident p) Nothing
        -- evaluate body
        res <- genExpr env body
        -- TODO: update thunk here
        returnFromFunction res
      emitTL $ TLDef $ mkHsFunDefinition
            LINKAGE_Internal
            (funRawId v)
            [ varRawId p | p <- params ]
            (length fvs)
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
    thisThunkTyP = TYPE_Pointer $ mkThunkTy (length fvs)




getElemPtr :: Coq_typ -> Coq_ident -> [Int] -> Coq_instr
getElemPtr t v path
    = INSTR_Op (SV (OP_GetElementPtr t (t, ident v) [(TYPE_I 32, SV (VALUE_Integer n))| n <- path]))

ident id = SV (VALUE_Ident id)

noop ty val = INSTR_Op (SV (OP_Conversion Bitcast ty val ty))

dummyBody :: [Coq_block]
dummyBody = [ Coq_mk_block (Anon 0)
                [] (TERM_Ret (hsTyP, SV VALUE_Null))
                (IVoid 1)
            ]

mkHsFunDefinition :: Coq_linkage -> Coq_raw_id -> [Coq_raw_id] -> Arity -> [Coq_block] -> Coq_definition
mkHsFunDefinition linkage n param_names env_arity blocks = Coq_mk_definition
    (mkHsFunDeclaration linkage n param_names env_arity)
    (closRawId :  param_names)
    blocks

mkHsFunDeclaration :: Coq_linkage -> Coq_raw_id -> [Coq_raw_id] -> Arity -> Coq_declaration
mkHsFunDeclaration linkage n param_names env_arity = Coq_mk_declaration
    n
    (hsFunTy (length param_names) env_arity)
    ([],([] : map (const []) param_names))
    (Just linkage)
    Nothing
    Nothing
    Nothing
    []
    Nothing
    Nothing
    Nothing

mkEnterFunDefinition :: Coq_linkage -> Coq_global_id -> [Coq_block] -> Coq_definition
mkEnterFunDefinition linkage n blocks = Coq_mk_definition
    (mkEnterFunDeclaration linkage n)
    [closRawId]
    blocks

mkEnterFunDeclaration :: Coq_linkage -> Coq_global_id -> Coq_declaration
mkEnterFunDeclaration linkage n = Coq_mk_declaration
    n
    enterFunTy
    ([],[[]])
    (Just linkage)
    Nothing
    Nothing
    Nothing
    []
    Nothing
    Nothing
    Nothing


codeNameStr :: Name -> String
codeNameStr n | isExternalName n =
    intercalate "_" $ map zEncodeString
        [ moduleNameString (moduleName (nameModule n))
        , occNameString (nameOccName n)
        ]
codeNameStr n  =
    intercalate "_" $ map zEncodeString
    [ occNameString (nameOccName n)
    , show (nameUnique n)
    ]


closIdent :: Coq_ident
closIdent = ID_Local closRawId
closRawId :: Coq_raw_id
closRawId = Name "clos"

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

caseAltEntryIdent :: Var -> Maybe Int -> Coq_ident
caseAltEntryIdent v mbi = ID_Local (caseAltEntryRawId v mbi)

caseAltEntryRawId :: Var -> Maybe Int -> Coq_raw_id
caseAltEntryRawId n Nothing  = Name (codeNameStr (getName n) ++ "_br_def")
caseAltEntryRawId n (Just i) = Name (codeNameStr (getName n) ++ "_br_" ++ show i)

caseAltRetIdent :: Var -> Maybe Int -> Coq_ident
caseAltRetIdent v mbi = ID_Local (caseAltRetRawId v mbi)

caseAltRetRawId :: Var -> Maybe Int -> Coq_raw_id
caseAltRetRawId n Nothing  = Name (codeNameStr (getName n) ++ "_br_ret")
caseAltRetRawId n (Just i) = Name (codeNameStr (getName n) ++ "_br_ret_" ++ show i)

caseAltExitIdent :: Var -> Maybe Int -> Coq_ident
caseAltExitIdent v mbi = ID_Local (caseAltExitRawId v mbi)

caseAltExitRawId :: Var -> Maybe Int -> Coq_raw_id
caseAltExitRawId n Nothing  = Name (codeNameStr (getName n) ++ "_br_ex")
caseAltExitRawId n (Just i) = Name (codeNameStr (getName n) ++ "_br_ex_" ++ show i)

caseAltJoin :: Var -> Coq_ident
caseAltJoin n = ID_Local (Name (codeNameStr (getName n) ++ "_br_join"))

caseAltJoinIdent :: Var -> Coq_ident
caseAltJoinIdent v = ID_Local (caseAltJoinRawId v)

caseAltJoinRawId :: Var -> Coq_raw_id
caseAltJoinRawId n = Name (codeNameStr (getName n) ++ "_br_join")



data TopLevelThing
    = TLAlias  Coq_alias
    | TLGlobal Coq_global
    | TLTyDef  Coq_type_decl
    | TLDecl   Coq_declaration
    | TLDef    Coq_definition

mkCoqModul :: String -> [TopLevelThing] -> Coq_modul
mkCoqModul name top_level_things
    = Coq_mk_modul name
        (TLE_Target "x86_64-pc-linux")
        (TLE_Source_filename "no data layout here")
        (map ("",) [ x | TLGlobal x <- top_level_things ])
        (map ("",) [ x | TLTyDef x  <- top_level_things ])
        (map ("",) [ x | TLDecl x   <- top_level_things ])
        (map ("",) [ x | TLDef x    <- top_level_things ])
        (map ("",) [ x | TLAlias x  <- top_level_things ])
