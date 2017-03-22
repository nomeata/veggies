{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
module VeggiesCodeGen where

import Data.List
import Data.Maybe
import Control.Monad.State
import Control.Monad.Writer

import Var
import Id
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

import Ollvm_ast

import Debug.Trace

genCode :: ModuleName -> [TyCon] -> CoreProgram -> Coq_modul
genCode name tycons binds
    = mkCoqModul (moduleNameString name)
      []
      defaultTyDecls
      decls
      defs
  where
    defs = defaultDefs ++ concatMap genTopLvlBind binds
    decls = [ mallocDecl ]

defaultTyDecls :: [Coq_type_decl]
defaultTyDecls =
    [ Coq_mk_type_decl (Name "hs")    mkClosureTy
    , Coq_mk_type_decl (Name "thunk") (mkThunkTy 0)
    , Coq_mk_type_decl (Name "dc")    (mkDataConTy 0)
    ]

defaultDefs :: [Coq_definition]
defaultDefs = [ returnArgDef ]

returnArgDef :: Coq_definition
returnArgDef = mkCoqDefinition "returnArg"
    ["clos"]
    (runG $ returnFromFunction (Name "clos"))

mkClosureTy :: Coq_typ
mkClosureTy = TYPE_Struct [ enterFunTyP ]

hsTyP :: Coq_typ
hsTyP = TYPE_Pointer (TYPE_Identified (ID_Global (Name "hs")))

-- An explicit, global function to call
hsFunTy :: Int -> Coq_typ
hsFunTy n = TYPE_Function hsTyP (replicate n hsTyP)

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

mkDataConTy n = TYPE_Struct [ enterFunTyP, tagTy, TYPE_Array n hsTyP ]

dataConTy = TYPE_Identified (ID_Global (Name "dc"))
dataConTyP = TYPE_Pointer dataConTy

genTopLvlBind :: CoreBind -> [Coq_definition]
genTopLvlBind (NonRec v rhs) = [ genTopLvlFunction v rhs | isWanted v]
genTopLvlBind (Rec pairs)    = [ genTopLvlFunction v rhs | (v,rhs) <- pairs, isWanted v]

-- Lets filter out typeable stuff for now
isWanted :: Var -> Bool
isWanted v | Just (tc,_) <- splitTyConApp_maybe (varType v)
           , getUnique tc `elem` [ trNameTyConKey, trTyConTyConKey, trModuleTyConKey]
           = False
isWanted v = True

genTopLvlFunction  :: Var -> CoreExpr -> Coq_definition
genTopLvlFunction v rhs | Just dc <- isDataConWorkId_maybe v = genDataConWorker dc

genTopLvlFunction v rhs =
    mkCoqDefinition (codeName (getName v))
        [ codeName (getName p) | p <- params ]
        (runG (genExpr body >>= returnFromFunction))
  where (params, body) = collectBinders rhs

genMalloc :: Coq_typ -> G Coq_local_id
genMalloc t = do
    -- http://stackoverflow.com/a/30830445/946226
    offset <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr t (t, SV VALUE_Null) [(TYPE_I 32, SV (VALUE_Integer 1))]))
    size <- emitInstr $ INSTR_Op (SV (OP_Conversion Ptrtoint t (localVal offset) (TYPE_I 64)))
    emitInstr $ INSTR_Call (mallocTy, ID_Global (Name "malloc")) [(TYPE_I 64, localVal size)]

genDataConWorker :: DataCon -> Coq_definition
genDataConWorker dc = mkCoqDefinition (codeName (getName dc))
    [ paramName n | n <- [0.. dataConRepArity dc-1]] $ runG $ do
        dcRawPtr <- genMalloc thisDataConTyP
        emitNamedInstr (Name "dc_casted") $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTyP (localVal dcRawPtr) thisDataConTyP))

        codePtr <- emitInstr $ getElemPtr thisDataConTyP (Name "dc_casted") [0,0]
        emitInstr $ INSTR_Store False (enterFunTyP, localVal codePtr) (enterFunTyP, globalVal (Name "returnArg")) Nothing

        tagPtr <- emitInstr $ getElemPtr thisDataConTyP (Name "dc_casted") [0,1]
        emitInstr $ INSTR_Store False (tagTyP, localVal tagPtr) (tagTy, SV (VALUE_Integer (dataConTag dc))) Nothing

        forM_ [0..dataConRepArity dc-1] $ \n -> do
            p <- emitInstr $ getElemPtr thisDataConTyP (Name "dc_casted") [0,2,n]
            emitInstr $ INSTR_Store False (hsTyP, localVal p) (hsTyP, localVal (Name (paramName n))) Nothing

        emitNamedInstr (Name "dc_closure") $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTyP (localVal dcRawPtr) hsTyP))

        returnFromFunction (Name "dc_closure")
  where
    thisDataConTy = mkDataConTy (dataConRepArity dc)
    thisDataConTyP = TYPE_Pointer thisDataConTy
    paramName n = "dcArg_" ++ show n

mallocRetTyP = TYPE_Pointer (TYPE_I 8)
mallocTy = TYPE_Function mallocRetTyP [TYPE_I 64]

mallocDecl ::  Coq_declaration
mallocDecl = Coq_mk_declaration
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


-- A code generation monad
type G a = StateT Int (Writer [Coq_terminator -> Coq_block]) a

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

runG :: G () -> [Coq_block]
runG g = combine $ connect (execWriter (execStateT g 0))
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

emitTerm :: Coq_terminator -> G ()
emitTerm t = do
    blockId <- freshAnon
    tell [\_ -> Coq_mk_block blockId [] t (IVoid 0)]

emitInstr :: Coq_instr -> G Coq_local_id
emitInstr instr = do
    instrId <- freshAnon
    emitNamedInstr instrId instr
    return instrId

emitNamedInstr :: Coq_local_id -> Coq_instr -> G ()
emitNamedInstr instrId instr = do
    blockId <- freshAnon
    tell [\t -> Coq_mk_block blockId [(IId instrId, instr)] t (IVoid 0)]

namedBlock :: Coq_local_id -> G ()
namedBlock blockId = do
    tell [\t -> Coq_mk_block blockId [] t (IVoid 0)]

namedBr1Block :: Coq_local_id -> Coq_local_id -> G ()
namedBr1Block blockId toBlockId = do
    tell [\_ -> Coq_mk_block blockId [] (TERM_Br_1 (TYPE_Label, ID_Local toBlockId)) (IVoid 0)]

namedPhiBlock :: Coq_typ -> Coq_block_id -> [(Coq_local_id, Coq_block_id)] -> G Coq_local_id
namedPhiBlock ty blockId pred = do
    tmpId <- freshAnon
    let phi = (IId tmpId, INSTR_Phi ty [ (ID_Local i, localVal l) | (i,l) <- pred ])
    tell [\t -> Coq_mk_block blockId [phi] t (IVoid 0)]
    return tmpId

---

returnFromFunction :: Coq_local_id -> G ()
returnFromFunction lid = emitTerm (TERM_Ret (hsTyP, SV (VALUE_Ident (ID_Local lid))))


genExpr :: CoreExpr -> G Coq_local_id
genExpr (Case scrut b _ [(DEFAULT, _, body)]) = do
    scrut_eval <- genExpr scrut
    emitNamedInstr (Name (codeName (getName b))) $ noop hsTyP (localVal scrut_eval)
    genExpr body

genExpr (Case scrut b _ alts) = do
    scrut_eval <- genExpr scrut
    emitNamedInstr (Name (codeName (getName b))) $ noop hsTyP (localVal scrut_eval)

    emitNamedInstr scrut_cast $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (localVal scrut_eval) dataConTyP))
    t <- getTag scrut_cast
    emitTerm $ tagSwitch t [ (tagOf ac, Name (caseAltEntry b (tagOf ac)))
                           | (ac, _, _) <- alts ]

    mapM_ genAlt alts

    res <- namedPhiBlock hsTyP (Name (caseAltJoin b))
        [ (Name (caseAltRet b (tagOf ac)), Name (caseAltExit b (tagOf ac)))
        | (ac, _, _) <- alts ]
    return res
  where
    tagSwitch :: Coq_local_id -> [(Maybe Int, Coq_local_id)] -> Coq_terminator
    tagSwitch tag ((_,l):xs) =
        TERM_Switch (tagTy,localVal tag) (TYPE_Label, ID_Local l)
            [ ((tagTy, SV (VALUE_Integer n)), (TYPE_Label, ID_Local l))
            | (Just n, l) <- xs ]

    scrut_cast = Name (caseScrutCasted b)
    tagOf DEFAULT      = Nothing
    tagOf (DataAlt dc) = Just (dataConTag dc)
    genAlt (ac, pats, rhs) = do
        namedBlock (Name (caseAltEntry b (tagOf ac)))
        forM_ (zip [0..] pats) $ \(n,pat) -> do
            patPtr <- emitInstr $ getElemPtr dataConTyP scrut_cast [0,2,n]
            emitNamedInstr (Name (codeName (getName pat))) $ INSTR_Load False hsTyP (hsTyP, localVal patPtr) Nothing

        tmpId <- genExpr rhs
        emitNamedInstr (Name (caseAltRet b (tagOf ac))) $ noop hsTyP (localVal tmpId)
        namedBr1Block (Name (caseAltExit b (tagOf ac))) (Name (caseAltJoin b))

genExpr (Let binds body) = do
    mapM_ (uncurry allocThunk) pairs
    mapM_ (uncurry fillThunk) pairs
    genExpr body
  where
    pairs = flattenBinds [binds]

genExpr e | (Var f, args) <- collectArgs e , not (isLocalVar f) = do
    let n = codeName (getName f)
    args' <- mapM genExpr (filter isValArg args)
    emitInstr $ INSTR_Call (mallocTy, ID_Global (Name n))
        [(hsTyP, localVal a) | a <- args' ]

genExpr (Var v) | isLocalVar v = do
    let v_code_name = (Name (codeName (getName v)))
    codePtr <- emitInstr $ getElemPtr hsTyP v_code_name [0,0]
    code <- emitInstr $ INSTR_Load False enterFunTyP (enterFunTyP, localVal codePtr) Nothing
    emitInstr $ INSTR_Call (enterFunTyP, ID_Local code) [(hsTyP, localVal v_code_name)]

genExpr e =
    pprTrace "genExpr" (ppr e) $
    emitInstr $ noop hsTyP (SV (VALUE_Null))


allocThunk :: Var -> CoreExpr -> G ()
allocThunk v e = do
    thunkRawPtr <- genMalloc thisThunkTyP
    emitNamedInstr (Name (codeName (getName v))) $
        INSTR_Op (SV (OP_Conversion Bitcast mallocRetTyP (localVal thunkRawPtr) hsTyP))
  where
    fvs = exprsFreeVarsList [e]
    thisThunkTyP = TYPE_Pointer $ mkThunkTy (length fvs)

fillThunk :: Var -> CoreExpr -> G ()
fillThunk v e = do
    castedPtr <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast hsTyP (localVal (Name (codeName (getName v)))) thisThunkTyP))
    -- TODO: Pointer to code function here
    forM_ (zip [0..] fvs) $ \(n,fv) -> do
        p <- emitInstr $ getElemPtr thisThunkTyP castedPtr [0,1,n]
        emitInstr $ INSTR_Store False (hsTyP, localVal p) (hsTyP, localVal (Name (codeName (getName fv)))) Nothing
  where
    fvs = exprsFreeVarsList [e]
    thisThunkTyP = TYPE_Pointer $ mkThunkTy (length fvs)


getTag :: Coq_local_id -> G Coq_local_id
getTag scrut_cast = do
    tagPtr <- emitInstr $ getElemPtr dataConTyP scrut_cast [0,1]
    loaded <- emitInstr $ INSTR_Load False tagTy (tagTyP, localVal tagPtr) Nothing
    return loaded


getElemPtr :: Coq_typ -> Coq_local_id -> [Int] -> Coq_instr
getElemPtr t v path
    = INSTR_Op (SV (OP_GetElementPtr t (t, localVal v) [(TYPE_I 32, SV (VALUE_Integer n))| n <- path]))

localVal  local_id  = SV (VALUE_Ident (ID_Local local_id))
globalVal global_id = SV (VALUE_Ident (ID_Global global_id))

noop ty val = INSTR_Op (SV (OP_Conversion Bitcast ty val ty))

dummyBody :: [Coq_block]
dummyBody = [ Coq_mk_block (Anon 0)
                [] (TERM_Ret (hsTyP, SV VALUE_Null))
                (IVoid 1)
            ]

mkCoqDefinition :: String -> [String] -> [Coq_block] -> Coq_definition
mkCoqDefinition n param_names blocks = Coq_mk_definition
    (mkCoqDeclaration n param_names)
    (map Name param_names)
    blocks

mkCoqDeclaration :: String -> [String] -> Coq_declaration
mkCoqDeclaration n param_names = Coq_mk_declaration
    (Name n)
    (hsFunTy (length param_names))
    ([],(map (const []) param_names))
    Nothing
    Nothing
    Nothing
    Nothing
    []
    Nothing
    Nothing
    Nothing


funName :: Name -> String
funName n = codeName n ++ "_fun"

caseScrutCasted :: Var ->  String
caseScrutCasted n = codeName (getName n) ++ "_casted"

caseAltEntry :: Var -> Maybe Int -> String
caseAltEntry n Nothing  = codeName (getName n) ++ "_br_def"
caseAltEntry n (Just i) = codeName (getName n) ++ "_br_" ++ show i

caseAltRet :: Var -> Maybe Int -> String
caseAltRet n Nothing  = codeName (getName n) ++ "_br_ret"
caseAltRet n (Just i) = codeName (getName n) ++ "_br_ret_" ++ show i

caseAltExit :: Var -> Maybe Int -> String
caseAltExit n Nothing  = codeName (getName n) ++ "_br_ex_def"
caseAltExit n (Just i) = codeName (getName n) ++ "_br_ex_" ++ show i

caseAltJoin :: Var -> String
caseAltJoin n = codeName (getName n) ++ "_br_join"


codeName :: Name -> String
codeName n | isExternalName n =
    intercalate "_" $ map zEncodeString
        [ moduleNameString (moduleName (nameModule n))
        , occNameString (nameOccName n)
        ]
codeName n  =
    intercalate "_" $ map zEncodeString
    [ occNameString (nameOccName n)
    , show (nameUnique n)
    ]




mkCoqModul :: String -> [Coq_global] -> [Coq_type_decl] -> [Coq_declaration] -> [Coq_definition] -> Coq_modul
mkCoqModul name globals tydecls declarations definitions
    = Coq_mk_modul name
        (TLE_Target "x86_64-pc-linux")
        (TLE_Source_filename "no data layout here")
        (map ("",) globals)
        (map ("",) tydecls)
        (map ("",) declarations)
        (map ("",) definitions)
