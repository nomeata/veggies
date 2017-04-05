import PrimOp
import Encoding
import OccName

import Data.List
import qualified Data.ByteString.Lazy as B
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as T

import Ollvm_ast
import Veggies.GenMonad
import Veggies.CodeGenTypes
import Veggies.ASTUtils
import Veggies.Common

import qualified Ast2Ast as LLVM
import qualified Ast2Assembly as LLVM
import qualified LLVM.Pretty as LLVM

genPAPFun :: G ()
genPAPFun = emitHsFun LINKAGE_External papFunRawName [] [] $ do
    -- find out the PAP arity (missing arguments)
    castedPAP <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident closIdent) (mkFunClosureTyP 0)))
    arityPtr <- emitInstr $ getElemPtr (mkFunClosureTyP 0) castedPAP [0,2]
    papArity <- emitInstr $ INSTR_Load False arityTy (arityTyP, ident arityPtr) Nothing

    -- find out the function arity (all arguments)
    evaledFunPtr <- emitInstr $ getElemPtr (mkFunClosureTyP 0) castedPAP [0,3,0]
    evaledFun <- emitInstr $ INSTR_Load False hsTyP (TYPE_Pointer hsTyP, ident evaledFunPtr) Nothing
    castedFun <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident evaledFun) (mkFunClosureTyP 0)))
    arityPtr <- emitInstr $ getElemPtr (mkFunClosureTyP 0) castedFun [0,2]
    funArity <- emitInstr $ INSTR_Load False arityTy (arityTyP, ident arityPtr) Nothing

    -- The difference is the number of arguments in the PAP
    diffArity <- emitInstr $ INSTR_Op (SV (OP_IBinop (Sub False False) i64 (ident funArity) (ident papArity)))

    -- Allocate argument array
    argsRawPtr <- emitInstr $ INSTR_Alloca hsTyP (Just (i64, ident funArity)) Nothing
    argsPtr <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast (TYPE_Pointer hsTyP) (ident argsRawPtr) (envTyP 0)))

    -- Assemble argument array, part 1: Arguments from PAP
    srcPtr <- emitInstr $ getElemPtr (mkFunClosureTyP 0) castedPAP [0,3,1]
    srcPtr' <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast (TYPE_Pointer hsTyP) (ident srcPtr) ptrTy))
    destPtr <- emitInstr $ getElemPtr (envTyP 0) argsPtr [0,0]
    destPtr' <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast (TYPE_Pointer hsTyP) (ident destPtr) ptrTy))
    nBytes <- emitInstr $ INSTR_Op (SV (OP_IBinop (Mul False False) i64 (SV (VALUE_Integer 8)) (ident diffArity)))
    emitVoidInstr $ INSTR_Call (memcpyTy, memcpyIdent)
            [(ptrTy, ident destPtr'), (ptrTy, ident srcPtr'),
             (i64, ident nBytes), (i64, SV (VALUE_Integer 0)), (i1, SV (VALUE_Integer 0))]

    -- Assemble argument array, part 2: Arguments from caller
    srcPtr <- emitInstr $ getElemPtr (envTyP 0) argsIdent [0,0]
    srcPtr' <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast (TYPE_Pointer hsTyP) (ident srcPtr) ptrTy))
    destPtr <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr (envTyP 0) (envTyP 0, ident argsPtr) [(i64, SV (VALUE_Integer 0)), (i64, ident diffArity)]))
    destPtr' <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast (TYPE_Pointer hsTyP) (ident destPtr) ptrTy))
    nBytes <- emitInstr $ INSTR_Op (SV (OP_IBinop (Mul False False) i64 (SV (VALUE_Integer 8)) (ident papArity)))
    emitVoidInstr $ INSTR_Call (memcpyTy, memcpyIdent)
            [(ptrTy, ident destPtr'), (ptrTy, ident srcPtr'),
             (i64, ident nBytes), (i64, SV (VALUE_Integer 0)), (i1, SV (VALUE_Integer 0))]

    funPtr <- emitInstr $ getElemPtr (mkFunClosureTyP 0) castedFun [0,1]
    fun <- emitInstr $ INSTR_Load False hsFunTyP (TYPE_Pointer hsFunTyP, ident funPtr) Nothing
    emitInstr $ INSTR_Call (hsFunTy, fun) [(hsTyP, ident evaledFun), (envTyP 0, ident argsPtr)]

genRTSCall :: G ()
genRTSCall = do
    blocks <- runLG $ do
        let thisFunClosTyP = TYPE_Pointer (mkFunClosureTy 0)

        castedFun <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident evaledFun) thisFunClosTyP))
        funPtr <- emitInstr $ getElemPtr thisFunClosTyP castedFun [0,1]
        fun <- emitInstr $ INSTR_Load False hsFunTyP (TYPE_Pointer hsFunTyP, ident funPtr) Nothing

        arityPtr <- emitInstr $ getElemPtr thisFunClosTyP castedFun [0,2]
        funArity <- emitInstr $ INSTR_Load False arityTy (arityTyP, ident arityPtr) Nothing

        let eqL   = Name "eq"
            neqL  = Name "neq"
            fewL  = Name "few"
            manyL = Name "many"

        isEq <- emitInstr $ INSTR_Op (SV (OP_ICmp Eq i64 (ident argArity) (ident funArity)))
        emitTerm $ TERM_Br (i1, ident isEq) (TYPE_Label, ID_Local eqL) (TYPE_Label, ID_Local neqL)

        -- Arity matches
        startNamedBlock eqL
        ret <- emitInstr $ INSTR_Call (hsFunTy, fun) [(hsTyP, ident evaledFun), (envTyP 0, ident argsPtr)]
        emitTerm $ TERM_Ret (hsTyP, ident ret)

        -- Arity does not match
        startNamedBlock neqL
        isFew <- emitInstr $ INSTR_Op (SV (OP_ICmp Slt i64 (ident funArity) (ident argArity)))
        emitTerm $ TERM_Br (i1, ident isFew) (TYPE_Label, ID_Local fewL) (TYPE_Label, ID_Local manyL)

        -- Too few arguments
        startNamedBlock fewL
        -- Allocate a PAP
        let papTy = mkFunClosureTy 0
        let papTyP = mkFunClosureTyP 0
        -- Dynamic size calculation :-(
        size <- emitInstr $ INSTR_Op (SV (OP_IBinop (Mul False False) i64 (SV (VALUE_Integer 8)) (ident argArity)))
        size <- emitInstr $ INSTR_Op (SV (OP_IBinop (Add False False) i64 (SV (VALUE_Integer (4*8))) (ident size)))
        rawPtr <- emitInstr $ INSTR_Call (mallocTy, mallocIdent) [(TYPE_I 64, ident size)]
        castedPAP <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTy (ident rawPtr) papTyP))
        codePtr <- emitInstr $ getElemPtr papTyP castedPAP [0,0]
        emitVoidInstr $ INSTR_Store False (TYPE_Pointer enterFunTyP, ident codePtr) (enterFunTyP, ident returnArgIdent) Nothing
        funPtr <- emitInstr $ getElemPtr papTyP castedPAP [0,1]
        emitVoidInstr $ INSTR_Store False (TYPE_Pointer hsFunTyP, ident funPtr) (hsFunTyP, ident papFunIdent) Nothing
        diffArity <- emitInstr $ INSTR_Op (SV (OP_IBinop (Sub False False) i64 (ident funArity) (ident argArity)))
        arityPtr <- emitInstr $ getElemPtr papTyP castedPAP [0,2]
        emitVoidInstr $ INSTR_Store False (TYPE_Pointer i64, ident arityPtr) (i64, ident diffArity) Nothing

        -- Save function
        firstPayloadPtr <- emitInstr $ getElemPtr papTyP castedPAP [0,3,0]
        emitVoidInstr $ INSTR_Store False (TYPE_Pointer hsTyP, ident firstPayloadPtr) (hsTyP, ident evaledFun) Nothing

        -- Save arguments
        srcPtr <- emitInstr $ getElemPtr (envTyP 0) argsPtr [0,0]
        srcPtr' <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast (TYPE_Pointer hsTyP) (ident srcPtr) ptrTy))
        destPtr <- emitInstr $ getElemPtr (mkFunClosureTyP 0) castedPAP [0,3,1]
        destPtr' <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast (TYPE_Pointer hsTyP) (ident destPtr) ptrTy))
        nBytes <- emitInstr $ INSTR_Op (SV (OP_IBinop (Mul False False) i64 (SV (VALUE_Integer 8)) (ident diffArity)))
        emitVoidInstr $ INSTR_Call (memcpyTy, memcpyIdent)
                [(ptrTy, ident destPtr'), (ptrTy, ident srcPtr'),
                 (i64, ident nBytes), (i64, SV (VALUE_Integer 0)), (i1, SV (VALUE_Integer 0))]

        pap <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTy (ident rawPtr) hsTyP))
        emitTerm $ TERM_Ret (hsTyP, ident pap)

        -- Too many arguments
        startNamedBlock manyL
        -- Call with parameter array, taking the first few arguments (same pointer)
        newFun <- emitInstr $ INSTR_Call (hsFunTy, fun)
            [(hsTyP, ident evaledFun), (envTyP 0, ident argsPtr)]
        -- Calculate remaining arity and arguments
        leftOverArity <- emitInstr $ INSTR_Op (SV (OP_IBinop (Sub False False) i64 (ident argArity) (ident funArity)))
        firstArgPtr <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr (envTyP 0) (envTyP 0, ident argsPtr) [(i64, SV (VALUE_Integer 0)), (i64, ident funArity)]))
        leftOverArgs <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast (TYPE_Pointer hsTyP) (ident firstArgPtr) (envTyP 0)))
        -- Call the returned function
        ret <- emitInstr $ INSTR_Call (callTy, callIdent)
            [(hsTyP, ident newFun), (arityTy, ident leftOverArity), (envTyP 0, ident leftOverArgs)]
        emitTerm $ TERM_Ret (hsTyP, ident ret)

    let def = Coq_mk_definition decl [Name "f", Name "arity", Name "args"] blocks
    emitTL $ TLDef def
  where
    evaledFun = ID_Local (Name "f")
    argArity = ID_Local (Name "arity")
    argsPtr = ID_Local (Name "args")

    decl = Coq_mk_declaration
        callRawName
        callTy
        ([], [[],[],[]])
        (Just LINKAGE_External)
        Nothing Nothing Nothing [] Nothing Nothing Nothing


genNullPtrBox :: G ()
genNullPtrBox = emitAliasedGlobal LINKAGE_External nullPtrBoxRawId hsTy ptrBoxTy $
        SV $ VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                          , (ptrTy,       SV VALUE_Null) ]


genPrimVal :: String -> G ()
genPrimVal name =
    genPrintAndExitClosure (primName name Nothing) $
        "entered primitive value " ++ name

voidIdent = ID_Global (Name (primName "void#" Nothing))

primName :: String -> Maybe String -> String
primName name suffix = intercalate "_" $ map zEncodeString $
        [ "GHC.Prim", name ] ++ [s | Just s <- return suffix ]

genReturnIO :: Coq_ident -> Coq_ident -> LG Coq_ident
genReturnIO s x = do
    (dc, fill) <- allocateDataCon 1 2
    fill [ s , x ]
    return dc

genUnboxedUnitTuple :: Coq_ident -> LG Coq_ident
genUnboxedUnitTuple x = do
    (dc, fill) <- allocateDataCon 1 1
    fill [ x ]
    return dc

mkIntOpBody op = do
    o1 <- unboxPrimValue i64 intBoxTy (p 0)
    o2 <- unboxPrimValue i64 intBoxTy (p  1)
    res <- emitInstr $ INSTR_Op (SV (OP_IBinop op i64 (ident o1) (ident o2)))
    boxPrimValue i64 intBoxTy (ident res)

mkCmpBody cmp = do
    o1 <- unboxPrimValue i64 intBoxTy (p  0)
    o2 <- unboxPrimValue i64 intBoxTy (p  1)
    res <- emitInstr $ INSTR_Op (SV (OP_ICmp cmp i64 (ident o1) (ident o2)))
    resInt <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext (TYPE_I 1) (ident res) i64))
    boxPrimValue i64 intBoxTy (ident resInt)

primOpBody :: PrimOp -> Maybe (LG Coq_ident)
primOpBody TagToEnumOp = Just $ do
    tag <- unboxPrimValue i64 intBoxTy (p  0)
    tag' <- emitInstr $
            INSTR_Op (SV (OP_IBinop (Add False False) i64 (ident tag) (SV (VALUE_Integer 1))))

    dcRawPtr <- genMalloc thisDataConTyP
    dc <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTy (ident dcRawPtr) hsTyP))

    dcCasted <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident dc) thisDataConTyP))

    codePtr <- emitInstr $ getElemPtr thisDataConTyP dcCasted [0,0]
    emitVoidInstr $ INSTR_Store False (TYPE_Pointer enterFunTyP, ident codePtr) (enterFunTyP, ident returnArgIdent) Nothing

    tagPtr <- emitInstr $ getElemPtr thisDataConTyP dcCasted [0,1]
    emitVoidInstr $ INSTR_Store False (tagTyP, ident tagPtr) (tagTy, ident tag') Nothing

    return dc
  where
    thisDataConTy = mkDataConTy 0
    thisDataConTyP = TYPE_Pointer thisDataConTy

primOpBody AddrEqOp = Just $ do
    ptr1 <- unboxPrimValue ptrTy ptrBoxTy (p  0)
    ptr2 <- unboxPrimValue ptrTy ptrBoxTy (p  1)
    ptr1' <- emitInstr $ INSTR_Op (SV (OP_Conversion Ptrtoint ptrTy (ident ptr1) i64))
    ptr2' <- emitInstr $ INSTR_Op (SV (OP_Conversion Ptrtoint ptrTy (ident ptr2) i64))
    res <- emitInstr $ INSTR_Op (SV (OP_ICmp Eq i64 (ident ptr1') (ident ptr2')))
    resInt <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext (TYPE_I 1) (ident res) i64))
    boxPrimValue i64 intBoxTy (ident resInt)

primOpBody IntAddOp = Just $ mkIntOpBody (Add False False)
primOpBody IntSubOp = Just $ mkIntOpBody (Sub False False)
primOpBody IntMulOp = Just $ mkIntOpBody (Mul False False)

primOpBody IntGtOp = Just $ mkCmpBody Sgt
primOpBody IntGeOp = Just $ mkCmpBody Sge
primOpBody IntEqOp = Just $ mkCmpBody Eq
primOpBody IntNeOp = Just $ mkCmpBody Ne
primOpBody IntLtOp = Just $ mkCmpBody Slt
primOpBody IntLeOp = Just $ mkCmpBody Sle

primOpBody WordAddOp = Just $ mkIntOpBody (Add False False)
primOpBody WordSubOp = Just $ mkIntOpBody (Sub False False)
primOpBody WordMulOp = Just $ mkIntOpBody (Mul False False)

primOpBody WordGtOp = Just $ mkCmpBody Ugt
primOpBody WordGeOp = Just $ mkCmpBody Uge
primOpBody WordEqOp = Just $ mkCmpBody Eq
primOpBody WordNeOp = Just $ mkCmpBody Ne
primOpBody WordLtOp = Just $ mkCmpBody Ult
primOpBody WordLeOp = Just $ mkCmpBody Ule

primOpBody IndexOffAddrOp_Char = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    resP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr ptrTy (ptrTy, ident ptr) [(i64, ident offset)]))
    byte <- emitInstr $ INSTR_Load False i8 (ptrTy, ident resP) Nothing
    int <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext i8 (ident byte) i64))
    boxPrimValue i64 intBoxTy (ident int)

primOpBody ReadOffAddrOp_Int8 = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    resP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr ptrTy (ptrTy, ident ptr) [(i64, ident offset)]))
    byte <- emitInstr $ INSTR_Load False i8 (ptrTy, ident resP) Nothing
    int <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext i8 (ident byte) i64))
    res <- boxPrimValue i64 intBoxTy (ident int)
    genReturnIO (p 2) res

primOpBody WriteOffAddrOp_Int8 = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    byteP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr ptrTy (ptrTy, ident ptr) [(i64, ident offset)]))

    int <- unboxPrimValue i64 intBoxTy (p 2)
    byte <- emitInstr $ INSTR_Op (SV (OP_Conversion Trunc i64 (ident int) i8))

    emitVoidInstr $ INSTR_Store False (ptrTy, ident byteP) (i8, ident byte) Nothing
    return (p 3)

primOpBody MakeStablePtrOp = Just $ do
    ptr <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (p 0)) ptrTy))
    res <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    genReturnIO (p 1) res

primOpBody DeRefStablePtrOp = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast ptrTy (ident ptr) hsTyP))

primOpBody NewMVarOp = Just $ do
    res <- boxPrimValue ptrTy ptrBoxTy (SV VALUE_Null)
    genReturnIO (p 0) res
primOpBody PutMVarOp = Just $ do
    ptr <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (p 1)) ptrTy))
    setPrimValue ptrTy ptrBoxTy (p 0) (ident ptr)
    return (p 2)
primOpBody TakeMVarOp = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    val <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast ptrTy (ident ptr) hsTyP))
    genReturnIO (p 1) val

primOpBody NewMutVarOp = Just $ do
    ptr <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (p 0)) ptrTy))
    res <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    genReturnIO (p 1) res
primOpBody WriteMutVarOp = Just $ do
    ptr <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (p 1)) ptrTy))
    setPrimValue ptrTy ptrBoxTy (p 0) (ident ptr)
    return (p 2)
primOpBody ReadMutVarOp = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    val <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast ptrTy (ident ptr) hsTyP))
    genReturnIO (p 1) val

primOpBody Narrow8IntOp = Just $ do
    int <- unboxPrimValue i64 intBoxTy (p 0)
    byte <- emitInstr $ INSTR_Op (SV (OP_Conversion Trunc i64 (ident int) i8))
    int' <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext i8 (ident byte) i64))
    boxPrimValue i64 intBoxTy (ident int')

primOpBody OrdOp = Just $ return (p 0)

primOpBody NewArrayOp = Just $ do
    genReturnIO (p 2) voidIdent
primOpBody ReadArrayOp = Just $ do
    genReturnIO (p 2) voidIdent
primOpBody WriteArrayOp = Just $ return (p 3)

primOpBody  ByteArrayContents_Char = Just $ return (p 0)

primOpBody  UnsafeFreezeByteArrayOp = Just $ do
    genReturnIO (p 1) (p 0)

primOpBody  NewAlignedPinnedByteArrayOp_Char = Just $ do
   -- Int# -> Int# -> State# s -> (# State# s, MutableByteArray# s #), size first
    size <- unboxPrimValue i64 intBoxTy (p 0)
    ptr <- emitInstr $ INSTR_Call (mallocTy, mallocIdent) [(TYPE_I 64, ident size)]
    val <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    genReturnIO (p 2) val

primOpBody NoDuplicateOp = Just $ return (p 0)
primOpBody TouchOp = Just $ return (p 1)

primOpBody MaskAsyncExceptionsOp = Just $ do
   -- apply first argument to the second argument
    evaledFun <- genEnterAndEval (p 0)
    genFunctionCall evaledFun [(p 1)]

primOpBody UnmaskAsyncExceptionsOp = Just $ do
   -- apply first argument to the second argument
    evaledFun <- genEnterAndEval (p 0)
    genFunctionCall evaledFun [(p 1)]

primOpBody MaskStatus = Just $ do
    zero <- liftG $ genIntegerLit 0
    genReturnIO (p 0) zero

primOpBody MkWeakNoFinalizerOp = Just $ do
    genReturnIO (p 2) voidIdent

primOpBody MyThreadIdOp = Just $ do
    genReturnIO (p 0) voidIdent

primOpBody CatchOp = Just $ do
   -- apply first argument to the third argument
    evaledFun <- genEnterAndEval (p 0)
    genFunctionCall evaledFun [(p 2)]

primOpBody _ = Nothing

withArity :: Int -> a -> Maybe (Int, a)
withArity a x = Just (a,x)

ffiBody :: String -> Maybe (Int, LG Coq_ident)
ffiBody "ffi_getOrSetGHCConcSignalSignalHandlerStore"
    = withArity 2 $ do
        genReturnIO (p 1) (p 0)
ffiBody "ffi_hs_free_stable_ptr"
    = withArity 2 $ do
        genUnboxedUnitTuple (p 1)
ffiBody "ffi_stg_sig_install"
    = withArity 4 $ do
        genReturnIO (p 3) (p 1)
ffiBody "ffi_localeEncoding"
    = withArity 1 $ do
        res <- liftG $ genStringLit "\0"
        genReturnIO (p 0) res
ffiBody "ffi_hs_iconv_open"
    = withArity 3 $ do
        ptr1 <- unboxPrimValue ptrTy ptrBoxTy (p 0)
        ptr2 <- unboxPrimValue ptrTy ptrBoxTy (p 1)
        let iconv_open_ty = TYPE_Function ptrTy [ptrTy, ptrTy]
            iconv_open_ident = ID_Global (Name "iconv_open")
        ptr <- emitInstr $ INSTR_Call (iconv_open_ty, iconv_open_ident)
            [(ptrTy, ident ptr1), (ptrTy, ident ptr2)]
        res <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
        genReturnIO (p 2) res
ffiBody _ = Nothing



mkPrimFun :: String -> Int -> LG Coq_ident -> G ()
mkPrimFun name arity body = do
    emitHsFun LINKAGE_External raw_fun_ident [] (take arity paramRawId) body

    emitAliasedGlobal LINKAGE_External (Name name) hsTy (mkFunClosureTy 0) $
        SV $ VALUE_Struct [ (enterFunTyP,                      ident returnArgIdent)
                          , (hsFunTyP,                         ident (ID_Global raw_fun_ident))
                          , (TYPE_I 64,                        SV (VALUE_Integer arity'))
                          , (envTy 0,                          SV (VALUE_Array []))
                          ]


  where
    arity' = fromIntegral arity
    raw_fun_ident = Name $ name ++ "_fun"

genPrimOp :: PrimOp -> G ()
genPrimOp pop | arity == 0 = error (occNameString (primOpOcc pop))
              | Just body <- primOpBody pop = mkPrimFun name arity body
              | otherwise = genPrintAndExitClosure name msg
  where
    (_, _, _, arity, _) =  primOpSig pop
    name = intercalate "_" $ map zEncodeString
        [ "GHC.Prim"
        , occNameString (primOpOcc pop)
        ]
    msg = "Unsupported primop " ++ occNameString (primOpOcc pop) ++ "\0"

genFFIFunc :: String -> G ()
genFFIFunc name | Just (arity, body) <- ffiBody name = mkPrimFun name arity body
                | otherwise = genPrintAndExitClosure name msg
  where msg = "Unsupported ffi call " ++ name ++ "\0"


primModule :: Coq_modul
primModule = mkCoqModul "GHC.Prim" $ runG $ do
    genRTSCall
    genPAPFun
    mapM_ emitTL defaultTyDecls
    genStaticIntLits
    genNullPtrBox

    mapM_ genPrimOp allThePrimOps
    mapM_ genPrimVal ["void#", "realWorld#", "proxy#", "coercionToken#"]
    mapM_ genFFIFunc ffi_fuction_calls

paramStrs :: [String]
paramStrs = ["p"++show n | n <- [1..]]

paramRawId :: [Coq_raw_id]
paramRawId = map Name paramStrs

paramIdents :: [Coq_ident]
paramIdents = map ID_Local paramRawId

p n = paramIdents !! n


main = do
    let vellvm_ast = primModule
    let llvm_ast = LLVM.convModule vellvm_ast
    -- ir <- LLVM.ast2Assembly llvm_ast
    -- putStrLn ir
    let ir = LLVM.ppllvm llvm_ast
    B.putStr (T.encodeUtf8 ir)

ffi_fuction_calls :: [String]
ffi_fuction_calls = words "ffi_access ffi_calloc ffi_chmod ffi_clk_tck ffi_close ffi_cmp_thread ffi_creat ffi_debugBelch2 ffi_debugErrLn ffi_debugLn ffi_dup ffi_dup2 ffi_epoll_create ffi_epoll_ctl ffi_epoll_wait ffi_errorBelch2 ffi_eventfd ffi_eventfd_write ffi_fdReady ffi_fork ffi_forkOS_createThread ffi_forkOS_entry ffi_free ffi_freeHaskellFunctionPtr ffi_getCcFlags ffi_getConcFlags ffi_getDebugFlags ffi_getenv ffi_getFullProgArgv ffi_getGcFlags ffi_getGCStats ffi_getGCStatsEnabled ffi_getMiscFlags ffi_getMonotonicNSec ffi_getNumberOfProcessors ffi_getOrSetGHCConcSignalSignalHandlerStore ffi_getOrSetSystemEventThreadEventManagerStore ffi_getOrSetSystemEventThreadIOManagerThreadStore ffi_getOrSetSystemTimerThreadEventManagerStore ffi_getOrSetSystemTimerThreadIOManagerThreadStore ffi_getpid ffi_getProfFlags ffi_getProgArgv ffi_getTickyFlags ffi_getTraceFlags ffi_ghczuwrapperZC0ZCbaseZCGHCziFloatZCexpm1f ffi_ghczuwrapperZC0ZCbaseZCSystemziCPUTimeZCgetrusage ffi_ghczuwrapperZC0ZCbaseZCSystemziIOZCrand ffi_ghczuwrapperZC0ZCbaseZCSystemziPosixziInternalsZCSEEKzuEND ffi_ghczuwrapperZC10ZCbaseZCSystemziPosixziInternalsZCtcgetattr ffi_ghczuwrapperZC11ZCbaseZCSystemziPosixziInternalsZCsigprocmask ffi_ghczuwrapperZC12ZCbaseZCSystemziPosixziInternalsZCsigaddset ffi_ghczuwrapperZC13ZCbaseZCSystemziPosixziInternalsZCsigemptyset ffi_ghczuwrapperZC14ZCbaseZCSystemziPosixziInternalsZCmkfifo ffi_ghczuwrapperZC15ZCbaseZCSystemziPosixziInternalsZCfcntl ffi_ghczuwrapperZC16ZCbaseZCSystemziPosixziInternalsZCfcntl ffi_ghczuwrapperZC17ZCbaseZCSystemziPosixziInternalsZCfcntl ffi_ghczuwrapperZC18ZCbaseZCSystemziPosixziInternalsZCutime ffi_ghczuwrapperZC19ZCbaseZCSystemziPosixziInternalsZCwrite ffi_ghczuwrapperZC1ZCbaseZCGHCziFloatZClog1pf ffi_ghczuwrapperZC1ZCbaseZCSystemziPosixziInternalsZCSEEKzuSET ffi_ghczuwrapperZC20ZCbaseZCSystemziPosixziInternalsZCwrite ffi_ghczuwrapperZC21ZCbaseZCSystemziPosixziInternalsZCread ffi_ghczuwrapperZC22ZCbaseZCSystemziPosixziInternalsZCread ffi_ghczuwrapperZC23ZCbaseZCSystemziPosixziInternalsZClseek ffi_ghczuwrapperZC2ZCbaseZCGHCziFloatZCexpm1 ffi_ghczuwrapperZC2ZCbaseZCSystemziPosixziInternalsZCSEEKzuCUR ffi_ghczuwrapperZC3ZCbaseZCGHCziFloatZClog1p ffi_ghczuwrapperZC3ZCbaseZCSystemziPosixziInternalsZCSzuISSOCK ffi_ghczuwrapperZC4ZCbaseZCSystemziPosixziInternalsZCSzuISFIFO ffi_ghczuwrapperZC5ZCbaseZCSystemziPosixziInternalsZCSzuISDIR ffi_ghczuwrapperZC6ZCbaseZCSystemziPosixziInternalsZCSzuISBLK ffi_ghczuwrapperZC7ZCbaseZCSystemziPosixziInternalsZCSzuISCHR ffi_ghczuwrapperZC8ZCbaseZCSystemziPosixziInternalsZCSzuISREG ffi_ghczuwrapperZC9ZCbaseZCSystemziPosixziInternalsZCtcsetattr ffi___gmpn_add ffi___gmpn_add_1 ffi___gmpn_cmp ffi___gmpn_divrem_1 ffi___gmpn_mod_1 ffi___gmpn_mul ffi___gmpn_mul_1 ffi___gmpn_popcount ffi___gmpn_sub ffi___gmpn_sub_1 ffi___gmpn_tdiv_qr ffi___hsbase_MD5Final ffi___hsbase_MD5Init ffi___hsbase_MD5Update ffi___hsbase_unsetenv ffi___hscore_bufsiz ffi___hscore_echo ffi___hscore_environ ffi___hscore_fd_cloexec ffi___hscore_f_getfl ffi___hscore_f_setfd ffi___hscore_f_setfl ffi___hscore_fstat ffi___hscore_ftruncate ffi___hscore_get_errno ffi___hscore_get_saved_termios ffi___hscore_icanon ffi___hscore_lflag ffi___hscore_lstat ffi___hscore_o_append ffi___hscore_o_binary ffi___hscore_o_creat ffi___hscore_o_excl ffi___hscore_o_noctty ffi___hscore_o_nonblock ffi___hscore_open ffi___hscore_o_rdonly ffi___hscore_o_rdwr ffi___hscore_o_trunc ffi___hscore_o_wronly ffi___hscore_poke_lflag ffi___hscore_ptr_c_cc ffi___hscore_set_errno ffi___hscore_set_saved_termios ffi___hscore_sig_block ffi___hscore_sig_setmask ffi___hscore_sigttou ffi___hscore_sizeof_siginfo_t ffi___hscore_sizeof_sigset_t ffi___hscore_sizeof_stat ffi___hscore_sizeof_termios ffi___hscore_stat ffi___hscore_st_dev ffi___hscore_st_ino ffi___hscore_st_mode ffi___hscore_st_mtime ffi___hscore_st_size ffi___hscore_tcsanow ffi___hscore_vmin ffi___hscore_vtime ffi_hs_free_stable_ptr ffi_hs_iconv ffi_hs_iconv_close ffi_hs_iconv_open ffi_hs_spt_key_count ffi_hs_spt_keys ffi_hs_spt_lookup ffi_integer_gmp_gcdext ffi_integer_gmp_gcd_word ffi_integer_gmp_invert ffi_integer_gmp_invert_word ffi_integer_gmp_mpn_and_n ffi_integer_gmp_mpn_andn_n ffi_integer_gmp_mpn_export ffi_integer_gmp_mpn_export1 ffi_integer_gmp_mpn_gcd ffi_integer_gmp_mpn_gcd_1 ffi_integer_gmp_mpn_get_d ffi_integer_gmp_mpn_import ffi_integer_gmp_mpn_ior_n ffi_integer_gmp_mpn_lshift ffi_integer_gmp_mpn_rshift ffi_integer_gmp_mpn_rshift_2c ffi_integer_gmp_mpn_sizeinbase ffi_integer_gmp_mpn_sizeinbase1 ffi_integer_gmp_mpn_tdiv_q ffi_integer_gmp_mpn_tdiv_r ffi_integer_gmp_mpn_xor_n ffi_integer_gmp_next_prime ffi_integer_gmp_next_prime1 ffi_integer_gmp_powm ffi_integer_gmp_powm1 ffi_integer_gmp_powm_word ffi_integer_gmp_rscan_nzbyte ffi_integer_gmp_scan_nzbyte ffi_integer_gmp_test_prime ffi_integer_gmp_test_prime1 ffi___int_encodeDouble ffi_isatty ffi_isDoubleDenormalized ffi_isDoubleFinite ffi_isDoubleInfinite ffi_isDoubleNaN ffi_isDoubleNegativeZero ffi_isFloatDenormalized ffi_isFloatFinite ffi_isFloatInfinite ffi_isFloatNaN ffi_isFloatNegativeZero ffi_libdwGetBacktrace ffi_libdwLookupLocation ffi_libdwPoolClear ffi_libdwPoolTake ffi_link ffi_localeEncoding ffi_lockFile ffi_malloc ffi_memcpy ffi_memmove ffi_memset ffi_performGC ffi_performMajorGC ffi_pipe ffi_poll ffi_putenv ffi_readlink ffi_realloc ffi_rintDouble ffi_rintFloat ffi_rts_disableThreadAllocationLimit ffi_rts_enableThreadAllocationLimit ffi_rts_getThreadAllocationCounter ffi_rts_getThreadId ffi_rts_setThreadAllocationCounter ffi_rtsSupportsBoundThreads ffi_setIOManagerControlFd ffi_setIOManagerWakeupFd ffi_setNumCapabilities ffi_setProgArgv ffi_setTimerManagerControlFd ffi_shutdownHaskellAndExit ffi_shutdownHaskellAndSignal ffi_stackOverflow ffi_startProfTimer ffi_stg_sig_install ffi_stopProfTimer ffi_strerror ffi_u_gencat ffi_u_iswalnum ffi_u_iswalpha ffi_u_iswcntrl ffi_u_iswlower ffi_u_iswprint ffi_u_iswspace ffi_u_iswupper ffi_umask ffi_unlink ffi_unlockFile ffi_u_towlower ffi_u_towtitle ffi_u_towupper ffi_waitpid" 
