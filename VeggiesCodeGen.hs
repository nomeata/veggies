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
    defs = concatMap genTopLvlBind binds
    decls = [ mallocDecl ]

defaultTyDecls :: [Coq_type_decl]
defaultTyDecls =
    [ ]

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

genDataConWorker :: DataCon -> Coq_definition
genDataConWorker dc = mkCoqDefinition (codeName (getName dc))
    [ paramName n | n <- [0.. dataConRepArity dc-1]] $ runG $ do
        -- http://stackoverflow.com/a/30830445/946226
        emitNamedInstr (Name "offset") $
            INSTR_Op (SV (OP_GetElementPtr dcTyP (dcTyP, SV VALUE_Null) [(TYPE_I 32, SV (VALUE_Integer 1))]))
        emitNamedInstr (Name "size") $
            INSTR_Op (SV (OP_Conversion Ptrtoint dcTyP (localVal (Name "offset")) (TYPE_I 64)))
        emitNamedInstr (Name "dc") $
            INSTR_Call (mallocTy, ID_Global (Name "malloc")) [(TYPE_I 64, localVal (Name "size"))]
        emitNamedInstr (Name "dc_casted") $
            INSTR_Op (SV (OP_Conversion Bitcast hsPtrTy (localVal (Name "dc")) dcTyP))

        tagP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr dcTyP (dcTyP, localVal (Name "dc_casted")) [(TYPE_I 32, SV (VALUE_Integer 0)), (TYPE_I 32, SV (VALUE_Integer 0))]))
        emitInstr $ INSTR_Store False (tagTyP, localVal tagP) (tagTy, SV (VALUE_Integer (dataConTag dc))) Nothing

        forM_ [0..dataConRepArity dc-1] $ \n -> do
            p <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr dcTyP (dcTyP, localVal (Name "dc_casted")) [(TYPE_I 32, SV (VALUE_Integer 0)), (TYPE_I 32, SV (VALUE_Integer 1)), (TYPE_I 32, SV (VALUE_Integer n))]))
            emitInstr $ INSTR_Store False (hsPtrTy, localVal p) (hsPtrTy, localVal (Name (paramName n))) Nothing

        returnFromFunction (Name "dc")
  where
    dcTy = TYPE_Struct [ tagTy, TYPE_Array (dataConRepArity dc) hsPtrTy ]
    dcTyP = TYPE_Pointer dcTy
    paramName n = "dcArg_" ++ show n

hsPtrTy :: Coq_typ
hsPtrTy = TYPE_Pointer (TYPE_I 8)

mallocTy = TYPE_Function (TYPE_Pointer (TYPE_I 8)) [TYPE_I 64]
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

deriving instance Eq Coq_raw_id

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
returnFromFunction lid = emitTerm (TERM_Ret (hsPtrTy, SV (VALUE_Ident (ID_Local lid))))


genExpr :: CoreExpr -> G Coq_local_id
genExpr (Case scrut b ty alts) = do
    s <- genExpr scrut
    t <- getTag s
    emitNamedInstr castedScrut $ INSTR_Op (SV (OP_Conversion Bitcast hsPtrTy (localVal s) dataConTy))
    emitTerm $ tagSwitch t [ (tagOf ac, Name (caseAltEntry b (tagOf ac)))
                           | (ac, _, _) <- alts ]

    mapM_ genAlt alts

    res <- namedPhiBlock hsPtrTy (Name (caseAltJoin b))
        [ (Name (caseAltRet b (tagOf ac)), Name (caseAltExit b (tagOf ac)))
        | (ac, _, _) <- alts ]
    return res
  where
    tagSwitch :: Coq_local_id -> [(Maybe Int, Coq_local_id)] -> Coq_terminator
    tagSwitch tag ((_,l):xs) =
        TERM_Switch (tagTy,localVal tag) (TYPE_Label, ID_Local l)
            [ ((tagTy, SV (VALUE_Integer n)), (TYPE_Label, ID_Local l))
            | (Just n, l) <- xs ]

    castedScrut = Name (caseScrutCasted b)
    tagOf DEFAULT      = Nothing
    tagOf (DataAlt dc) = Just (dataConTag dc)
    genAlt (ac, pats, rhs) = do
        namedBlock (Name (caseAltEntry b (tagOf ac)))
        forM_ (zip [0..] pats) $ \(n,pat) -> do
            patPtr <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr dataConTy (dataConTy, localVal castedScrut) [(TYPE_I 32, SV (VALUE_Integer 0)), (TYPE_I 32, SV (VALUE_Integer 1)), (TYPE_I 32, SV (VALUE_Integer n))]))
            emitNamedInstr (Name (codeName (getName pat))) $ INSTR_Load False hsPtrTy (hsPtrTy, localVal patPtr) Nothing

        tmpId <- genExpr rhs
        emitNamedInstr (Name (caseAltRet b (tagOf ac))) $ noop hsPtrTy (localVal tmpId)
        namedBr1Block (Name (caseAltExit b (tagOf ac))) (Name (caseAltJoin b))

genExpr e | (Var f, args) <- collectArgs e , not (isLocalVar f) = do
    let n = codeName (getName f)
    args' <- mapM genExpr (filter isValArg args)
    emitInstr $ INSTR_Call (mallocTy, ID_Global (Name n))
        [(hsPtrTy, localVal a) | a <- args' ]

genExpr (Var v) | isLocalVar v = do
    return (Name (codeName (getName v)))

genExpr e =
    pprTrace "genExpr" (ppr e) $
    emitInstr $ noop hsPtrTy (SV (VALUE_Null))

getTag :: Coq_local_id -> G Coq_local_id
getTag from = do
    casted <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast hsPtrTy (localVal from) tagTyP))
    loaded <- emitInstr $ INSTR_Load False tagTy (tagTyP, localVal casted) Nothing
    return loaded

tagTy = TYPE_I 64
tagTyP = TYPE_Pointer tagTy
dataConTy = TYPE_Pointer (TYPE_Struct [ TYPE_I 64, TYPE_Array 0 hsPtrTy ])

localVal  local_id  = SV (VALUE_Ident (ID_Local local_id))
globalVal global_id = SV (VALUE_Ident (ID_Global global_id))

noop ty val = INSTR_Op (SV (OP_Conversion Bitcast ty val ty))

dummyBody :: [Coq_block]
dummyBody = [ Coq_mk_block (Anon 0)
                [] (TERM_Ret (hsPtrTy, SV VALUE_Null))
                (IVoid 1)
            ]

hsFunTy :: Int -> Coq_typ
hsFunTy n = TYPE_Function hsPtrTy (replicate n hsPtrTy)

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
