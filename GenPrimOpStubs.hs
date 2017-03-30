import PrimOp
import Encoding
import OccName

import Data.List

import Ollvm_ast
import Veggies.GenMonad
import Veggies.CodeGenTypes
import Veggies.ASTUtils

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
    ident_str = intercalate "_" $ map zEncodeString
        [ "GHC.Prim"
        , name
        ]

    tmp_ident = Name tmp_str
    tmp_str = intercalate "_" $ map zEncodeString
        [ "GHC.Prim"
        , name
        , "tmp"
        ]

    val = SV $VALUE_Struct [ (enterFunTyP, ident returnArgIdent) ]


genPrimOpStub :: PrimOp -> G ()
genPrimOpStub pop | arity == 0 = error (occNameString occName)
                  | otherwise  = do
    blocks <- runLG $ do
        casted <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast msgTy (ident (ID_Global str_ident)) (TYPE_Pointer (TYPE_I 8))))
        emitInstr $ INSTR_Call (TYPE_Pointer putsTy, putsIdent) [(TYPE_Pointer msgTy, ident casted)]
        emitInstr $ INSTR_Call (TYPE_Pointer exitTy, exitIdent) [(TYPE_I 64, SV (VALUE_Integer 1))]
        emitTerm (TERM_Ret (hsTyP, SV VALUE_Null))

    emitTL $ TLDef $ mkHsFunDefinition
        LINKAGE_External
        raw_fun_ident
        (map Name $ take arity paramNames)
        0
        blocks

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

    str_ident = Name str_str
    str_str = intercalate "_" $ map zEncodeString
        [ "GHC.Prim"
        , occNameString occName
        , "str"
        ]

    msg = "Unsupported primop " ++ occNameString occName ++ "\0"
    msgTy = TYPE_Array (fromIntegral (length msg)) (TYPE_I 8)

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
    emitTL exitDecl
    emitTL putsDecl

primModule :: Coq_modul
primModule = mkCoqModul "GHC.Prim" toplevels
  where
    (toplevels, []) = runG $ do
        globals
        mapM_ genPrimOpStub (allThePrimOps \\ supportedPrimOps)
        mapM_ genPrimVal ["void#", "realWorld#"]

paramNames = ["p"++show n | n <- [1..]]

main = do
    let vellvm_ast = primModule
    let llvm_ast = LLVM.convModule vellvm_ast
    ir <- LLVM.ast2Assembly llvm_ast
    putStrLn ir
