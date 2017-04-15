{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
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

import qualified Veggies.TypedLLVM as T

import qualified Ast2Ast as LLVM
import qualified LLVM.Pretty as LLVM

import Data.Tagged


genPAPFun :: G ()
genPAPFun = emitHsFun LINKAGE_External papFunRawName [] $ do
    let argsIdent' = Tagged @T.EnvP argsIdent
    let closIdent' = Tagged @T.HsP closIdent

    -- find out the PAP arity (missing arguments)
    castedPAP <- T.emitInstr @T.FunClosureP $ T.bitCast (Tagged @T.HsP closIdent)
    arityPtr <- T.emitInstr $ T.getElemPtr castedPAP (T.allKnown @[0,2])
    papArity <- T.emitInstr $ T.load arityPtr

    -- find out the function arity (all arguments)
    evaledFunPtr <- T.emitInstr $ T.getElemPtr castedPAP (T.allKnown @[0,3,0])
    evaledFun <- T.emitInstr $ T.load evaledFunPtr
    castedFun <- T.emitInstr @T.FunClosureP $ T.bitCast evaledFun
    arityPtr <- T.emitInstr $ T.getElemPtr castedFun (T.allKnown @[0,2])
    funArity <- T.emitInstr $ T.load arityPtr

    -- The difference is the number of arguments in the PAP
    diffArity <- T.emitInstr $ T.ibinop (Sub False False) (T.ident funArity) (T.ident papArity)

    -- Allocate argument array
    argsRawPtr <- T.genMallocWords (T.ident funArity)
    argsPtr <- T.emitInstr $ T.bitCast argsRawPtr


    -- Assemble argument array, part 1: Arguments from PAP
    papArgs <- T.emitInstr $ T.getElemPtr castedPAP (T.allKnown @[0,3])
    T.genMemcopy (T.ident papArgs)      (T.ident argsPtr)
                 (T.mkI64 1)            (T.mkI64 1)
                 (T.ident diffArity)


    -- Assemble argument array, part 2: Arguments from caller
    T.genMemcopy (T.ident argsIdent')    (T.ident argsPtr)
                 (T.mkI64 1)            (T.ident diffArity)
                 (T.ident papArity)

    -- Free the argument array
    casted <- T.emitInstr $ T.bitCast argsIdent'
    T.genFree (T.ident casted)

    -- Call the function
    funPtr <- T.emitInstr $ T.getElemPtr castedFun (T.allKnown @[0,1])
    fun <- T.emitInstr $ T.load funPtr
    ret <- T.emitInstr $ T.call fun (T.ident evaledFun `T.ManyCons` (T.ident argsPtr `T.ManyCons` T.ManyNil))
    return (unTagged ret)

genRTSCall :: G ()
genRTSCall = do
    blocks <- runLG $ do
        let thisFunClosTyP = TYPE_Pointer (mkFunClosureTy 0)

        castedFun <- emitInstr $ bitCast hsTyP evaledFun thisFunClosTyP
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
        isFew <- emitInstr $ INSTR_Op (SV (OP_ICmp Slt i64 (ident argArity) (ident funArity)))
        emitTerm $ TERM_Br (i1, ident isFew) (TYPE_Label, ID_Local fewL) (TYPE_Label, ID_Local manyL)

        -- Too few arguments
        startNamedBlock fewL
        -- Allocate a PAP
        let papTy = mkFunClosureTy 0
        let papTyP = mkFunClosureTyP 0
        -- Dynamic size calculation :-(
        words <- emitInstr $ INSTR_Op (SV (OP_IBinop (Add False False) i64 (SV (VALUE_Integer 4)) (ident argArity)))
        rawPtr <- genMallocWords (ident words)
        castedPAP <- emitInstr $ bitCast mallocRetTy rawPtr papTyP
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
        papArgs <- emitInstr $ getElemPtr (mkFunClosureTyP 0) castedPAP [0,3]
        genMemcopy (ident argsIdent)      (ident papArgs)
                   (SV (VALUE_Integer 0)) (SV (VALUE_Integer 1)) -- offset due to fun ptr
                   (ident argArity)

        pap <- emitInstr $ bitCast mallocRetTy rawPtr hsTyP
        emitTerm $ TERM_Ret (hsTyP, ident pap)

        -- Too many arguments
        startNamedBlock manyL

        -- Create a new array for the arguments (as the callee will free it)
        newArgsRawPtr <- genMallocWords (ident funArity)
        newArgsPtr <- emitInstr $ bitCast ptrTy newArgsRawPtr (envTyP 0)

        genMemcopy (ident argsPtr)        (ident newArgsPtr)
                   (SV (VALUE_Integer 0)) (SV (VALUE_Integer 0))
                   (ident funArity)

        -- Create a new array for the left-over arguments
        leftOverArity <- emitInstr $ INSTR_Op (SV (OP_IBinop (Sub False False) i64 (ident argArity) (ident funArity)))

        leftOverArgsRawPtr <- genMallocWords (ident leftOverArity)
        leftOverArgsPtr <- emitInstr $ bitCast ptrTy leftOverArgsRawPtr (envTyP 0)

        genMemcopy (ident argsPtr)  (ident leftOverArgsPtr)
                   (ident funArity) (SV (VALUE_Integer 0))
                   (ident leftOverArity)

        -- Free the argument array
        casted <- emitInstr $ bitCast (envTyP 0) argsPtr ptrTy
        genFree (ident casted)

        -- Call the oversaturated function
        newFun <- emitInstr $ INSTR_Call (hsFunTy, fun)
            [(hsTyP, ident evaledFun), (envTyP 0, ident newArgsPtr)]
        -- Call the returned function
        ret <- emitInstr $ INSTR_Call (callTy, callIdent)
            [(hsTyP, ident newFun), (arityTy, ident leftOverArity), (envTyP 0, ident leftOverArgsPtr)]
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

genHsMain :: G ()
genHsMain = do
    blocks <- runLG $ do
        evaled <- genEnterAndEval (ID_Global (Name "ZCMain_main"))
        genFunctionCall evaled [ID_Global (Name "GHCziPrim_realWorldzh")]
        genCallToExit (SV (VALUE_Integer 0))
        -- Returning crashes, the stack is somehow broken.
        emitTerm $ TERM_Ret (i64, SV (VALUE_Integer 0))

    emitTL $ TLDef $ Coq_mk_definition decl [] blocks
  where
    decl = Coq_mk_declaration
        (Name "hs_main")
        (TYPE_Function i64 [])
        ([], [])
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
    dc <- emitInstr $ bitCast mallocRetTy dcRawPtr hsTyP

    dcCasted <- emitInstr $ bitCast hsTyP dc thisDataConTyP

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
primOpBody ISllOp   = Just $ mkIntOpBody (Shl False False)
primOpBody ISraOp   = Just $ mkIntOpBody (AShr False)
primOpBody AndIOp   = Just $ mkIntOpBody And

primOpBody IntGtOp = Just $ mkCmpBody Sgt
primOpBody IntGeOp = Just $ mkCmpBody Sge
primOpBody IntEqOp = Just $ mkCmpBody Eq
primOpBody IntNeOp = Just $ mkCmpBody Ne
primOpBody IntLtOp = Just $ mkCmpBody Slt
primOpBody IntLeOp = Just $ mkCmpBody Sle

primOpBody CharEqOp = Just $ mkCmpBody Eq
primOpBody CharLeOp = Just $ mkCmpBody Ult

primOpBody WordAddOp = Just $ mkIntOpBody (Add False False)
primOpBody WordSubOp = Just $ mkIntOpBody (Sub False False)
primOpBody WordMulOp = Just $ mkIntOpBody (Mul False False)
primOpBody WordRemOp = Just $ mkIntOpBody URem
primOpBody WordQuotOp = Just $ mkIntOpBody (UDiv False) -- Maybe fishy?

primOpBody WordGtOp = Just $ mkCmpBody Ugt
primOpBody WordGeOp = Just $ mkCmpBody Uge
primOpBody WordEqOp = Just $ mkCmpBody Eq
primOpBody WordNeOp = Just $ mkCmpBody Ne
primOpBody WordLtOp = Just $ mkCmpBody Ult
primOpBody WordLeOp = Just $ mkCmpBody Ule

primOpBody AddrAddOp = Just $ mkIntOpBody (Add False False)

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

primOpBody ReadOffAddrOp_Word64 = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    castPtr <- emitInstr $ bitCast ptrTy ptr (TYPE_Pointer i64)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    resP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr (TYPE_Pointer i64) (TYPE_Pointer i64, ident castPtr) [(i64, ident offset)]))
    val <- emitInstr $ INSTR_Load False i64 (TYPE_Pointer i64, ident resP) Nothing
    box <- boxPrimValue i64 intBoxTy (ident val)
    genReturnIO (p 2) box

primOpBody ReadOffAddrOp_WideChar = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    castPtr <- emitInstr $ bitCast ptrTy ptr (TYPE_Pointer i32)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    resP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr (TYPE_Pointer i32) (TYPE_Pointer i32, ident castPtr) [(i64, ident offset)]))
    val <- emitInstr $ INSTR_Load False i32 (TYPE_Pointer i32, ident resP) Nothing
    valCast <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext i32 (ident val) i64))
    box <- boxPrimValue i64 intBoxTy (ident valCast)
    genReturnIO (p 2) box


primOpBody WriteOffAddrOp_Int8 = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    byteP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr ptrTy (ptrTy, ident ptr) [(i64, ident offset)]))

    int <- unboxPrimValue i64 intBoxTy (p 2)
    byte <- emitInstr $ INSTR_Op (SV (OP_Conversion Trunc i64 (ident int) i8))

    emitVoidInstr $ INSTR_Store False (ptrTy, ident byteP) (i8, ident byte) Nothing
    return (p 3)

primOpBody WriteOffAddrOp_Word8 = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    byteP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr ptrTy (ptrTy, ident ptr) [(i64, ident offset)]))

    int <- unboxPrimValue i64 intBoxTy (p 2)
    byte <- emitInstr $ INSTR_Op (SV (OP_Conversion Trunc i64 (ident int) i8))

    emitVoidInstr $ INSTR_Store False (ptrTy, ident byteP) (i8, ident byte) Nothing
    return (p 3)

primOpBody WriteOffAddrOp_WideChar = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    i32Ptr <- emitInstr $ bitCast ptrTy ptr (TYPE_Pointer i32)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    wcharP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr (TYPE_Pointer i32) (TYPE_Pointer i32, ident i32Ptr) [(i64, ident offset)]))

    int <- unboxPrimValue i64 intBoxTy (p 2)
    wchar <- emitInstr $ INSTR_Op (SV (OP_Conversion Trunc i64 (ident int) i32))

    emitVoidInstr $ INSTR_Store False (TYPE_Pointer i32, ident wcharP) (i32, ident wchar) Nothing
    return (p 3)

primOpBody WriteOffAddrOp_Addr = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    castPtr <- emitInstr $ bitCast ptrTy ptr (TYPE_Pointer ptrTy)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    destP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr (TYPE_Pointer ptrTy) (TYPE_Pointer ptrTy, ident castPtr) [(i64, ident offset)]))

    val <- unboxPrimValue ptrTy ptrBoxTy (p 2)

    emitVoidInstr $ INSTR_Store False (TYPE_Pointer ptrTy, ident destP) (ptrTy, ident val) Nothing
    return (p 3)

primOpBody WriteOffAddrOp_Word64 = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    castPtr <- emitInstr $ bitCast ptrTy ptr (TYPE_Pointer i64)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    destP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr (TYPE_Pointer i64) (TYPE_Pointer i64, ident castPtr) [(i64, ident offset)]))

    val <- unboxPrimValue i64 intBoxTy (p 2)

    emitVoidInstr $ INSTR_Store False (TYPE_Pointer i64, ident destP) (i64, ident val) Nothing
    return (p 3)

primOpBody MakeStablePtrOp = Just $ do
    ptr <- emitInstr $ bitCast hsTyP (p 0) ptrTy
    res <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    genReturnIO (p 1) res

primOpBody DeRefStablePtrOp = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    emitInstr $ bitCast ptrTy ptr hsTyP

primOpBody NewMVarOp = Just $ do
    res <- boxPrimValue ptrTy ptrBoxTy (SV VALUE_Null)
    genReturnIO (p 0) res
primOpBody PutMVarOp = Just $ do
    ptr <- emitInstr $ bitCast hsTyP (p 1) ptrTy
    setPrimValue ptrTy ptrBoxTy (p 0) (ident ptr)
    return (p 2)
primOpBody TakeMVarOp = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    val <- emitInstr $ bitCast ptrTy ptr hsTyP
    genReturnIO (p 1) val

primOpBody NewMutVarOp = Just $ do
    ptr <- emitInstr $ bitCast hsTyP (p 0) ptrTy
    res <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    genReturnIO (p 1) res
primOpBody WriteMutVarOp = Just $ do
    ptr <- emitInstr $ bitCast hsTyP (p 1) ptrTy
    setPrimValue ptrTy ptrBoxTy (p 0) (ident ptr)
    return (p 2)
primOpBody ReadMutVarOp = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    val <- emitInstr $ bitCast ptrTy ptr hsTyP
    genReturnIO (p 1) val

primOpBody Narrow8IntOp = Just $ do
    int <- unboxPrimValue i64 intBoxTy (p 0)
    byte <- emitInstr $ INSTR_Op (SV (OP_Conversion Trunc i64 (ident int) i8))
    int' <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext i8 (ident byte) i64))
    boxPrimValue i64 intBoxTy (ident int')
primOpBody Narrow8WordOp = Just $ do
    int <- unboxPrimValue i64 intBoxTy (p 0)
    byte <- emitInstr $ INSTR_Op (SV (OP_Conversion Trunc i64 (ident int) i8))
    int' <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext i8 (ident byte) i64))
    boxPrimValue i64 intBoxTy (ident int')
primOpBody Narrow32IntOp = Just $ do
    int <- unboxPrimValue i64 intBoxTy (p 0)
    byte <- emitInstr $ INSTR_Op (SV (OP_Conversion Trunc i64 (ident int) i32))
    int' <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext i32 (ident byte) i64))
    boxPrimValue i64 intBoxTy (ident int')

primOpBody OrdOp = Just $ return (p 0)
primOpBody ChrOp = Just $ return (p 0)

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
    ptr <- genMallocBytes (ident size)
    val <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    genReturnIO (p 2) val

primOpBody  NewPinnedByteArrayOp_Char = Just $ do
   -- Int# -> State# s -> (# State# s, MutableByteArray# s #)
    size <- unboxPrimValue i64 intBoxTy (p 0)
    ptr <- genMallocBytes (ident size)
    val <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    genReturnIO (p 1) val

primOpBody NoDuplicateOp = Just $ return (p 0)
primOpBody TouchOp = Just $ return (p 1)
primOpBody Int2WordOp = Just $ return (p 0)
primOpBody Word2IntOp = Just $ return (p 0)

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

primOpBody MkWeakOp = Just $ do
    ptr <- emitInstr $ bitCast hsTyP (p 1) ptrTy
    res <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    genReturnIO (p 3) res
primOpBody MkWeakNoFinalizerOp = Just $ do
    ptr <- emitInstr $ bitCast hsTyP (p 1) ptrTy
    res <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    genReturnIO (p 2) res

primOpBody MyThreadIdOp = Just $ do
    genReturnIO (p 0) voidIdent

primOpBody CatchOp = Just $ do
   -- apply first argument to the third argument
    evaledFun <- genEnterAndEval (p 0)
    genFunctionCall evaledFun [(p 2)]

primOpBody _ = Nothing

withArity :: Int -> a -> Maybe (Int, a)
withArity a x = Just (a,x)


mkPrimFun :: String -> Int -> LG Coq_ident -> G ()
mkPrimFun name arity body = do
    emitHsFun LINKAGE_External raw_fun_ident [] $ do
        loadArgs (take arity paramRawId)
        body

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


primModule :: Coq_modul
primModule = mkCoqModul "GHC.Prim" $ runG $ do
    genHsMain
    genRTSCall
    genPAPFun
    mapM_ emitTL defaultTyDecls
    genStaticIntLits
    genNullPtrBox

    mapM_ genPrimOp allThePrimOps
    mapM_ genPrimVal ["void#", "realWorld#", "proxy#", "coercionToken#"]

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
