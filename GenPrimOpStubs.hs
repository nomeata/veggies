import PrimOp
import Encoding
import OccName

import Data.List

import Ollvm_ast
import Veggies.GenMonad
import Veggies.CodeGenTypes
import Veggies.ASTUtils
import Veggies.Common

import qualified Ast2Ast as LLVM
import qualified Ast2Assembly as LLVM

genPrimVal :: String -> G ()
genPrimVal name = do
    emitTL $ TLGlobal $ Coq_mk_global
            raw_ident
            hsTy
            True -- constant
            (Just val)
            (Just LINKAGE_External)
            Nothing
            Nothing
            Nothing
            False
            Nothing
            False
            Nothing
            Nothing
  where
    raw_ident = Name ident_str
    ident_str = primName name Nothing

    tmp_ident = Name tmp_str
    tmp_str = primName name (Just "tmp")

    val = SV $ VALUE_Struct [ (enterFunTyP, ident returnArgIdent) ]


voidIdent = ID_Global (Name (primName "void#" Nothing))

primName :: String -> Maybe String -> String
primName name suffix = intercalate "_" $ map zEncodeString $
        [ "GHC.Prim", name ] ++ [s | Just s <- return suffix ]

genReturnIO :: Coq_ident -> Coq_ident -> LG Coq_ident
genReturnIO s x = do
    dc <- freshLocal
    let (alloc,fill) = allocateDataCon dc 1 2
    alloc
    fill [ s , x ]
    return (ID_Local dc)

primOpBody :: PrimOp -> LG ()
primOpBody MakeStablePtrOp = do
    ret <- genReturnIO (paramIdents !! 1) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody PutMVarOp = do
    ret <- genReturnIO (paramIdents !! 2) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody NewMVarOp = do
    ret <- genReturnIO (paramIdents !! 0) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody NewArrayOp = do
    ret <- genReturnIO (paramIdents !! 2) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody NoDuplicateOp = do
    emitTerm $ TERM_Ret (hsTyP, ident (paramIdents !! 0))

primOpBody MaskAsyncExceptionsOp = do
   -- apply first argument to the second argument
    evaledFun <- genEnterAndEval (paramIdents !! 0)
    ret <- genFunctionCall evaledFun [(paramIdents !! 1)]
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody MaskStatus = do
    zero <- liftG $ genIntegerLit 0
    ret <- genReturnIO (paramIdents !! 0) zero
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody MkWeakNoFinalizerOp = do
    ret <- genReturnIO (paramIdents !! 2) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody MyThreadIdOp = do
    ret <- genReturnIO (paramIdents !! 0) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody CatchOp = do
   -- apply first argument to the third argument
    evaledFun <- genEnterAndEval (paramIdents !! 0)
    ret <- genFunctionCall evaledFun [(paramIdents !! 2)]
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody pop = do
    liftG $ do
        emitTL $ TLGlobal $ Coq_mk_global
                str_ident
                msgTy
                True
                (Just (SV (VALUE_Cstring msg)))
                (Just LINKAGE_Private)
                Nothing
                Nothing
                Nothing
                False
                Nothing
                False
                Nothing
                Nothing

    casted <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast msgTy (ident (ID_Global str_ident)) (TYPE_Pointer (TYPE_I 8))))
    emitInstr $ INSTR_Call (TYPE_Pointer putsTy, putsIdent) [(TYPE_Pointer msgTy, ident casted)]
    emitInstr $ INSTR_Call (TYPE_Pointer exitTy, exitIdent) [(TYPE_I 64, SV (VALUE_Integer 1))]
    emitTerm (TERM_Ret (hsTyP, SV VALUE_Null))
  where
    str_ident = Name str_str
    str_str = intercalate "_" $ map zEncodeString
        [ "GHC.Prim"
        , occNameString (primOpOcc pop)
        , "str"
        ]

    msg = "Unsupported primop " ++ occNameString (primOpOcc pop) ++ "\0"
    msgTy = TYPE_Array (fromIntegral (length msg)) (TYPE_I 8)


genPrimOpStub :: PrimOp -> G ()
genPrimOpStub pop | arity == 0 = error (occNameString occName)
                  | otherwise  = do
    blocks <- runLG $ primOpBody pop

    emitTL $ TLDef $ mkHsFunDefinition
        LINKAGE_External
        raw_fun_ident
        (take arity paramRawId)
        0
        blocks

    emitTL $ TLGlobal $ Coq_mk_global
            tmp_ident
            (mkFunClosureTy (fromIntegral arity) 0) --hsTyP
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
           raw_ident
           hsTyP
           (SV (OP_Conversion Bitcast (mkFunClosureTy (fromIntegral arity) 0) (ident (ID_Global tmp_ident)) hsTyP))
           (Just LINKAGE_External)
           Nothing
           Nothing
           Nothing
           False

  where
    val = SV $VALUE_Struct [ (enterFunTyP,                     ident returnArgIdent)
                           , (TYPE_Pointer (hsFunTy arity' 0) , ident (ID_Global raw_fun_ident))

                           , (TYPE_I 64, SV (VALUE_Integer arity'))
                           , (envTy 0 , SV (VALUE_Array []))
                           ]


    (_, _, _, arity, _) =  primOpSig pop
    arity' = fromIntegral arity
    occName = primOpOcc pop
    raw_fun_ident = Name ident_fun_str
    ident_fun_str = intercalate "_" $ map zEncodeString
        [ "GHC.Prim"
        , occNameString occName
        , "fun"
        ]

    raw_ident = Name ident_str
    ident_str = intercalate "_" $ map zEncodeString
        [ "GHC.Prim"
        , occNameString occName
        ]

    tmp_ident = Name tmp_str
    tmp_str = intercalate "_" $ map zEncodeString
        [ "GHC.Prim"
        , occNameString occName
        , "tmp"
        ]

supportedPrimOps :: [PrimOp]
supportedPrimOps =
    [ IntAddOp
    , IntSubOp
    , IntMulOp
    , WordAddOp
    , WordSubOp
    , WordMulOp
    ]

globals :: G ()
globals = do
    mapM_ emitTL defaultTyDecls
    emitTL returnArgDecl
    emitTL badArityDecl
    emitTL exitDecl
    emitTL putsDecl
    emitTL mallocDecl

primModule :: Coq_modul
primModule = mkCoqModul "GHC.Prim" toplevels
  where
    (toplevels, []) = runG $ do
        globals
        mapM_ genPrimOpStub (allThePrimOps \\ supportedPrimOps)
        mapM_ genPrimVal ["void#", "realWorld#"]

paramStrs :: [String]
paramStrs = ["p"++show n | n <- [1..]]

paramRawId :: [Coq_raw_id]
paramRawId = map Name paramStrs

paramIdents :: [Coq_ident]
paramIdents = map ID_Local paramRawId


main = do
    let vellvm_ast = primModule
    let llvm_ast = LLVM.convModule vellvm_ast
    ir <- LLVM.ast2Assembly llvm_ast
    putStrLn ir
