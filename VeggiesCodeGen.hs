{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
module VeggiesCodeGen where

import Data.List
import Data.Maybe
import Data.Bifunctor
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
        bimap concat (nub . concat) $
        unzip [genStaticVal env v e | (v,e) <- flattenBinds binds ]

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
    ]

returnArgDecl :: TopLevelThing
returnArgDecl =  TLDecl $ mkEnterFunDeclaration
    LINKAGE_External
    "rts_returnArg"

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
mkThunkTy n = TYPE_Struct [ enterFunTyP, TYPE_Array n' hsTyP ]
  where n' = max 1 n

thunkTy :: Coq_typ
thunkTy = TYPE_Identified (ID_Global (Name "thunk"))

thunkTyP :: Coq_typ
thunkTyP = TYPE_Pointer thunkTy

tagTy = TYPE_I 64
tagTyP = TYPE_Pointer tagTy

arityTy = TYPE_I 64

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

genStaticVal :: GenEnv -> Var -> CoreExpr -> ([TopLevelThing], [Var])
genStaticVal env v rhs
    | getIdArity env v == 0
    , Just dc <- isDataConId_maybe v
    =
    let val = SV $VALUE_Struct [ (enterFunTyP,                     ident returnArgIdent)
                               , (TYPE_I 64, SV (VALUE_Integer (dataConTag dc)))
                               , (envTy 0 , SV (VALUE_Array []))
                               ]
    in ( [ TLGlobal $ Coq_mk_global
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
         , TLAlias $ Coq_mk_alias
               (varRawId v)
               hsTyP
               (SV (OP_Conversion Bitcast (mkDataConTy 0) (ident (ID_Global (varRawIdTmp v))) hsTyP))
               (Just LINKAGE_External)
               Nothing
               Nothing
               Nothing
               False
         ]
       , [] )
genStaticVal env v rhs
    | (Var f, args) <- collectArgs rhs
    , Just dc <- isDataConId_maybe f
    , let val_args = filter isValArg args
    , not (null val_args)
    =
    let args_idents = [ (hsTyP, v)
                      | e <- val_args , Just v <- return $ getStaticArg e]

        getStaticArg :: CoreExpr -> Maybe Coq_value
        getStaticArg (Var v) = Just $ cast (getIdArity env v) (ident (varIdent env v))
        getStaticArg (Lit _) = Just $ SV (VALUE_Null)
        getStaticArg _ = Nothing

        externals = [ v | Var v <- val_args, (isGlobalId v && not (isTopLvl env v)) ]

        arity = length args_idents
        val = SV $VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                               , (TYPE_I 64, SV (VALUE_Integer (dataConTag dc)))
                               , (envTy arity , SV (VALUE_Array args_idents))
                               ]
    in (if length args_idents == dataConRepArity dc then id
           else pprTrace "genStaticVal arity" (ppr v <+> ppr rhs <+> ppr arity))
       ( [ TLGlobal $ Coq_mk_global
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
         , TLAlias $ Coq_mk_alias
               (varRawId v)
               hsTyP
               (SV (OP_Conversion Bitcast (mkDataConTy arity) (ident (ID_Global (varRawIdTmp v))) hsTyP))
               (Just LINKAGE_External)
               Nothing
               Nothing
               Nothing
               False
         ]
        , externals)
  where
    cast arity val = SV (OP_Conversion Bitcast (mkDataConTy arity) val hsTyP)

genStaticVal env v rhs =
    let (def, externals) = genTopLvlFunction env v rhs
    in ( [ TLGlobal $ Coq_mk_global
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
         , TLAlias $ Coq_mk_alias
               (varRawId v)
               hsTyP
               (SV (OP_Conversion Bitcast (mkFunClosureTy arity 0) (ident (ID_Global (varRawIdTmp v))) hsTyP))
               (Just LINKAGE_External)
               Nothing
               Nothing
               Nothing
               False
         , def
         ], externals)
  where
    arity = getIdArity env v
    val = SV $VALUE_Struct [ (enterFunTyP,                     ident returnArgIdent)
                           , (TYPE_Pointer (hsFunTy arity 0) , ident (funIdent env v))

                           , (TYPE_I 64, SV (VALUE_Integer arity))
                           , (envTy 0 , SV (VALUE_Array []))
                      ]
    -- casted_val = SV $ OP_Conversion Bitcast (mkFunClosureTy arity 0) val hsTy

genTopLvlFunction :: GenEnv -> Id -> CoreExpr -> (TopLevelThing, [Var])
genTopLvlFunction env v rhs
    | Just dc <- isDataConWorkId_maybe v = (genDataConWorker dc, [])
genTopLvlFunction env v rhs
    | length params /= getIdArity env v
    = pprPanic "genTopLvlFunction" (ppr v <+> ppr rhs <+> ppr (getIdArity env v))
    | otherwise
    =
    let (externals, blocks) = runG (genExpr env body >>= returnFromFunction)
        def = TLDef $ mkHsFunDefinition
            LINKAGE_External
            (funRawId v)
            [ varRawId p | p <- params ]
            blocks
    in (def, externals)
  where
    (params, body) = collectMoreValBinders rhs

genMalloc :: Coq_typ -> G Coq_ident
genMalloc t = do
    -- http://stackoverflow.com/a/30830445/946226
    offset <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr t (t, SV VALUE_Null) [(TYPE_I 32, SV (VALUE_Integer 1))]))
    size <- emitInstr $ INSTR_Op (SV (OP_Conversion Ptrtoint t (ident offset) (TYPE_I 64)))
    emitInstr $ INSTR_Call (mallocTy, ID_Global (Name "malloc")) [(TYPE_I 64, ident size)]

allocateDataCon :: Coq_raw_id -> DataCon -> (G (), [Coq_ident] ->  G ())
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

genDataConWorker :: DataCon -> TopLevelThing
genDataConWorker dc = TLDef $ mkHsFunDefinition linkage
    (funRawId (dataConWorkId dc))
    [ Name (paramName n) | n <- [0.. dataConRepArity dc-1]] $
    snd $ runG $ do
        let (alloc, fill) = allocateDataCon (Name "dc") dc
        alloc
        fill [ ID_Local (Name (paramName n)) | n <- [0..dataConRepArity dc - 1]]
        returnFromFunction (ID_Local (Name "dc"))
  where
    linkage | isUnboxedTupleCon dc
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


-- A code generation monad
type G = StateT Int (WriterT [Var] (Writer [Coq_terminator -> Coq_block]))

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

runG :: G () -> ([Var], [Coq_block])
runG g =
    let (decls, mkBlocks) = runWriter (execWriterT (execStateT g 0))
    in (decls, combine (connect mkBlocks))
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

fresh :: G Int
fresh = do
    n <- get
    put (n+1)
    return n

freshAnon :: G Coq_local_id
freshAnon = Anon <$> fresh

noteExternalVar :: Var -> G ()
noteExternalVar v = lift (tell [v])

emitTerm :: Coq_terminator -> G ()
emitTerm t = do
    blockId <- freshAnon
    lift $ lift $ tell [\_ -> Coq_mk_block blockId [] t (IVoid 0)]

emitInstr :: Coq_instr -> G Coq_ident
emitInstr instr = do
    instrId <- freshAnon
    emitNamedInstr instrId instr
    return (ID_Local instrId)

emitNamedInstr :: Coq_local_id -> Coq_instr -> G ()
emitNamedInstr instrId instr = do
    blockId <- freshAnon
    lift $ lift $ tell [\t -> Coq_mk_block blockId [(IId instrId, instr)] t (IVoid 0)]

namedBlock :: Coq_local_id -> G ()
namedBlock blockId = do
    lift $ lift $ tell [\t -> Coq_mk_block blockId [] t (IVoid 0)]

namedBr1Block :: Coq_local_id -> Coq_local_id -> G ()
namedBr1Block blockId toBlockId = do
    lift $ lift $ tell [\_ -> Coq_mk_block blockId [] (TERM_Br_1 (TYPE_Label, ID_Local toBlockId)) (IVoid 0)]

namedPhiBlock :: Coq_typ -> Coq_block_id -> [(Coq_ident, Coq_block_id)] -> G Coq_ident
namedPhiBlock ty blockId pred = do
    tmpId <- freshAnon
    let phi = (IId tmpId, INSTR_Phi ty [ (i, SV (VALUE_Ident (ID_Local l))) | (i,l) <- pred ])
    lift $ lift $ tell [\t -> Coq_mk_block blockId [phi] t (IVoid 0)]
    return (ID_Local tmpId)

---

returnFromFunction :: Coq_ident -> G ()
returnFromFunction lid = emitTerm (TERM_Ret (hsTyP, ident lid))


collectMoreValBinders :: CoreExpr -> ([Id], CoreExpr)
collectMoreValBinders = go []
  where
    go ids (Lam b e) | isId b = go (b:ids) e
    go ids (Lam b e)          = go ids e
    go ids (Cast e _)         = go ids e
    go ids body               = (reverse ids, body)

genExpr :: GenEnv -> CoreExpr -> G Coq_ident
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

    emitNamedInstr scrut_cast_raw_id $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident scrut_eval) dataConTyP))
    t <- getTag scrut_cast_ident
    emitTerm $ tagSwitch t [ (tagOf ac, caseAltEntryRawId b (tagOf ac))
                           | (ac, _, _) <- alts ]

    mapM_ genAlt alts

    res <- namedPhiBlock hsTyP (caseAltJoinRawId b)
        [ (caseAltRetIdent b (tagOf ac), caseAltExitRawId b (tagOf ac))
        | (ac, _, _) <- alts ]
    return res
  where
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
    dc_local <- freshAnon
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

genExpr env (Var v) = do
    when (isGlobalId v && not (isTopLvl env v)) $ noteExternalVar v
    codePtr <- emitInstr $ getElemPtr hsTyP (varIdent env v) [0,0]
    code <- emitInstr $ INSTR_Load False enterFunTyP (enterFunTyP, ident codePtr) Nothing
    emitInstr $ INSTR_Call (enterFunTyP, code) [(hsTyP, ident (varIdent env v))]

genExpr env (Coercion _) = do
    noteExternalVar coercionTokenId
    return (varIdent env coercionTokenId)

genExpr env e =
    pprTrace "genExpr" (ppr e) $
    emitInstr $ noop hsTyP (SV (VALUE_Null))

genArg :: GenEnv -> CoreArg -> G Coq_ident
genArg env (Cast e _) = genArg env e
genArg env (App e a) | isTyCoArg a = genArg env e
genArg env (Var v) = do
    when (isGlobalId v && not (isTopLvl env v )) $ noteExternalVar v
    return $ varIdent env v
genArg env e = pprTrace "genArg" (ppr e) $
    emitInstr $ noop hsTyP (SV VALUE_Null) -- hack

genLetBind :: GenEnv -> Var -> CoreExpr -> (G (), G ())
genLetBind env v e
    | (Var f, args) <- collectArgs e
    , Just dc <- isDataConId_maybe f
    = let (alloc, fill) = allocateDataCon (varRawId v) dc
          fill' = do
            arg_locals <- mapM (genArg env) (filter isValArg args)
            fill arg_locals
      in (alloc, fill')

genLetBind env v e = (alloc, fill)
  where
    alloc = do
        thunkRawPtr <- genMalloc thisThunkTyP
        emitNamedInstr (varRawId v) $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTyP (ident thunkRawPtr) hsTyP))

    fill = do
        castedPtr <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (varIdent env v)) thisThunkTyP))
        -- TODO: Pointer to code function here
        forM_ (zip [0..] fvs) $ \(n,fv) -> do
            p <- emitInstr $ getElemPtr thisThunkTyP castedPtr [0,1,n]
            emitInstr $ INSTR_Store False (hsTyP, ident p) (hsTyP, ident (varIdent env v)) Nothing

    fvs = exprsFreeVarsList [e]
    thisThunkTyP = TYPE_Pointer $ mkThunkTy (length fvs)


getTag :: Coq_ident -> G Coq_ident
getTag scrut_cast = do
    tagPtr <- emitInstr $ getElemPtr dataConTyP scrut_cast [0,1]
    loaded <- emitInstr $ INSTR_Load False tagTy (tagTyP, ident tagPtr) Nothing
    return loaded


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

mkHsFunDefinition :: Coq_linkage -> Coq_raw_id -> [Coq_raw_id] -> [Coq_block] -> Coq_definition
mkHsFunDefinition linkage n param_names blocks = Coq_mk_definition
    (mkHsFunDeclaration linkage n param_names)
    (Name "clos" :  param_names)
    blocks

mkHsFunDeclaration :: Coq_linkage -> Coq_raw_id -> [Coq_raw_id] -> Coq_declaration
mkHsFunDeclaration linkage n param_names = Coq_mk_declaration
    n
    (hsFunTy (length param_names) 0)
    ([],([] : map (const []) param_names))
    (Just linkage)
    Nothing
    Nothing
    Nothing
    []
    Nothing
    Nothing
    Nothing

mkEnterFunDefinition :: Coq_linkage -> String -> [Coq_block] -> Coq_definition
mkEnterFunDefinition linkage n blocks = Coq_mk_definition
    (mkEnterFunDeclaration linkage n)
    [Name "clos"]
    blocks

mkEnterFunDeclaration :: Coq_linkage -> String -> Coq_declaration
mkEnterFunDeclaration linkage n = Coq_mk_declaration
    (Name n)
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

funIdent :: GenEnv -> Id -> Coq_ident
funIdent env v
    | isGlobalId v || isTopLvl env v
    = ID_Global (funRawId v)
    | otherwise
    = ID_Local (funRawId v)
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
