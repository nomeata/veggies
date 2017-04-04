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
    ret <- boxPrimValue i64 intBoxTy (ident res)
    emitTerm $ TERM_Ret (hsTyP, ident ret)

mkCmpBody cmp = do
    o1 <- unboxPrimValue i64 intBoxTy (p  0)
    o2 <- unboxPrimValue i64 intBoxTy (p  1)
    res <- emitInstr $ INSTR_Op (SV (OP_ICmp cmp i64 (ident o1) (ident o2)))
    resInt <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext (TYPE_I 1) (ident res) i64))
    ret <- boxPrimValue i64 intBoxTy (ident resInt)
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody :: PrimOp -> Maybe (LG ())
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

    emitTerm $ TERM_Ret (hsTyP, ident dc)
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
    ret <- boxPrimValue i64 intBoxTy (ident resInt)
    emitTerm $ TERM_Ret (hsTyP, ident ret)

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
    byte <- emitInstr $ INSTR_Load False i8 (TYPE_Pointer ptrTy, ident resP) Nothing
    int <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext i8 (ident byte) i64))
    res <- boxPrimValue i64 intBoxTy (ident int)
    emitTerm $ TERM_Ret (hsTyP, ident res)

primOpBody ReadOffAddrOp_Int8 = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    resP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr ptrTy (ptrTy, ident ptr) [(i64, ident offset)]))
    byte <- emitInstr $ INSTR_Load False i8 (TYPE_Pointer ptrTy, ident resP) Nothing
    int <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext i8 (ident byte) i64))
    res <- boxPrimValue i64 intBoxTy (ident int)
    ret <- genReturnIO (p 2) res
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody WriteOffAddrOp_Int8 = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    offset <- unboxPrimValue i64 intBoxTy (p 1)
    byteP <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr ptrTy (ptrTy, ident ptr) [(i64, ident offset)]))

    int <- unboxPrimValue i64 intBoxTy (p 2)
    byte <- emitInstr $ INSTR_Op (SV (OP_Conversion Trunc i64 (ident int) i8))

    emitVoidInstr $ INSTR_Store False (TYPE_Pointer ptrTy, ident byteP) (i8, ident byte) Nothing
    emitTerm $ TERM_Ret (hsTyP, ident (p 3))

primOpBody MakeStablePtrOp = Just $ do
    ptr <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (p 0)) ptrTy))
    res <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    ret <- genReturnIO (p 1) res
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody DeRefStablePtrOp = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    casted <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast ptrTy (ident ptr) hsTyP))
    emitTerm $ TERM_Ret (hsTyP, ident casted)

primOpBody NewMVarOp = Just $ do
    res <- boxPrimValue ptrTy ptrBoxTy (SV VALUE_Null)
    ret <- genReturnIO (p 0) res
    emitTerm $ TERM_Ret (hsTyP, ident ret)
primOpBody PutMVarOp = Just $ do
    ptr <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (p 1)) ptrTy))
    setPrimValue ptrTy ptrBoxTy (p 0) (ident ptr)
    emitTerm $ TERM_Ret (hsTyP, ident (p 2))
primOpBody TakeMVarOp = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    val <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast ptrTy (ident ptr) hsTyP))
    ret <- genReturnIO (p 1) val
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody NewMutVarOp = Just $ do
    ptr <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (p 0)) ptrTy))
    res <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    ret <- genReturnIO (p 1) res
    emitTerm $ TERM_Ret (hsTyP, ident ret)
primOpBody WriteMutVarOp = Just $ do
    ptr <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident (p 1)) ptrTy))
    setPrimValue ptrTy ptrBoxTy (p 0) (ident ptr)
    emitTerm $ TERM_Ret (hsTyP, ident (p 2))
primOpBody ReadMutVarOp = Just $ do
    ptr <- unboxPrimValue ptrTy ptrBoxTy (p 0)
    val <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast ptrTy (ident ptr) hsTyP))
    ret <- genReturnIO (p 1) val
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody Narrow8IntOp = Just $ do
    int <- unboxPrimValue i64 intBoxTy (p 0)
    byte <- emitInstr $ INSTR_Op (SV (OP_Conversion Trunc i64 (ident int) i8))
    int' <- emitInstr $ INSTR_Op (SV (OP_Conversion Zext i8 (ident int) i64))
    val <- boxPrimValue i64 intBoxTy (ident int')
    emitTerm $ TERM_Ret (hsTyP, ident val)

primOpBody  OrdOp = Just $ do
    emitTerm $ TERM_Ret (hsTyP, ident (p 0))

primOpBody NewArrayOp = Just $ do
    ret <- genReturnIO (p 2) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)
primOpBody ReadArrayOp = Just $ do
    ret <- genReturnIO (p 2) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)
primOpBody WriteArrayOp = Just $ do
    emitTerm $ TERM_Ret (hsTyP, ident (p 3))

primOpBody  ByteArrayContents_Char = Just $ do
    emitTerm $ TERM_Ret (hsTyP, ident (p 0))

primOpBody  UnsafeFreezeByteArrayOp = Just $ do
    ret <- genReturnIO (p 1) (p 0)
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody  NewAlignedPinnedByteArrayOp_Char = Just $ do
   -- Int# -> Int# -> State# s -> (# State# s, MutableByteArray# s #), size first
    size <- unboxPrimValue i64 intBoxTy (p 0)
    ptr <- emitInstr $ INSTR_Call (mallocTy, mallocIdent) [(TYPE_I 64, ident size)]
    val <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    ret <- genReturnIO (p 2) val
    emitTerm $ TERM_Ret (hsTyP, ident ret)


primOpBody NoDuplicateOp = Just $ do
    emitTerm $ TERM_Ret (hsTyP, ident (p 0))

primOpBody MaskAsyncExceptionsOp = Just $ do
   -- apply first argument to the second argument
    evaledFun <- genEnterAndEval (p 0)
    ret <- genFunctionCall evaledFun [(p 1)]
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody UnmaskAsyncExceptionsOp = Just $ do
   -- apply first argument to the second argument
    evaledFun <- genEnterAndEval (p 0)
    ret <- genFunctionCall evaledFun [(p 1)]
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody MaskStatus = Just $ do
    zero <- liftG $ genIntegerLit 0
    ret <- genReturnIO (p 0) zero
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody MkWeakNoFinalizerOp = Just $ do
    ret <- genReturnIO (p 2) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody MyThreadIdOp = Just $ do
    ret <- genReturnIO (p 0) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody CatchOp = Just $ do
   -- apply first argument to the third argument
    evaledFun <- genEnterAndEval (p 0)
    ret <- genFunctionCall evaledFun [(p 2)]
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody _ = Nothing

withArity :: Int -> a -> Maybe (Int, a)
withArity a x = Just (a,x)

ffiBody :: String -> Maybe (Int, LG ())
ffiBody "ffi_getOrSetGHCConcSignalSignalHandlerStore"
    = withArity 2 $ do
        ret <- genReturnIO (p 1) (p 0)
        emitTerm $ TERM_Ret (hsTyP, ident ret)
ffiBody "ffi_hs_free_stable_ptr"
    = withArity 2 $ do
        ret <- genUnboxedUnitTuple (p 1)
        emitTerm $ TERM_Ret (hsTyP, ident ret)
ffiBody "ffi_stg_sig_install"
    = withArity 4 $ do
        ret <- genReturnIO (p 3) (p 1)
        emitTerm $ TERM_Ret (hsTyP, ident ret)
ffiBody "ffi_localeEncoding"
    = withArity 1 $ do
        res <- liftG $ genStringLit "\0"
        ret <- genReturnIO (p 0) res
        emitTerm $ TERM_Ret (hsTyP, ident ret)
ffiBody _ = Nothing



mkPrimFun :: String -> Int -> LG () -> G ()
mkPrimFun name arity body = do
    blocks <- runLG body

    emitTL $ TLDef $ mkHsFunDefinition
        LINKAGE_External
        raw_fun_ident
        (take arity paramRawId)
        0
        blocks

    emitAliasedGlobal LINKAGE_External (Name name) hsTy (mkFunClosureTy arity' 0) $
        SV $ VALUE_Struct [ (enterFunTyP,                      ident returnArgIdent)
                          , (TYPE_Pointer (hsFunTy arity' 0) , ident (ID_Global raw_fun_ident))
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
    ir <- LLVM.ast2Assembly llvm_ast
    putStrLn ir


ffi_fuction_calls :: [String]
ffi_fuction_calls = words "ffi_access ffi_calloc ffi_chmod ffi_clk_tck ffi_close ffi_cmp_thread ffi_creat ffi_debugBelch2 ffi_debugErrLn ffi_debugLn ffi_dup ffi_dup2 ffi_epoll_create ffi_epoll_ctl ffi_epoll_wait ffi_errorBelch2 ffi_eventfd ffi_eventfd_write ffi_fdReady ffi_fork ffi_forkOS_createThread ffi_forkOS_entry ffi_free ffi_freeHaskellFunctionPtr ffi_getCcFlags ffi_getConcFlags ffi_getDebugFlags ffi_getenv ffi_getFullProgArgv ffi_getGcFlags ffi_getGCStats ffi_getGCStatsEnabled ffi_getMiscFlags ffi_getMonotonicNSec ffi_getNumberOfProcessors ffi_getOrSetGHCConcSignalSignalHandlerStore ffi_getOrSetSystemEventThreadEventManagerStore ffi_getOrSetSystemEventThreadIOManagerThreadStore ffi_getOrSetSystemTimerThreadEventManagerStore ffi_getOrSetSystemTimerThreadIOManagerThreadStore ffi_getpid ffi_getProfFlags ffi_getProgArgv ffi_getTickyFlags ffi_getTraceFlags ffi_ghczuwrapperZC0ZCbaseZCGHCziFloatZCexpm1f ffi_ghczuwrapperZC0ZCbaseZCSystemziCPUTimeZCgetrusage ffi_ghczuwrapperZC0ZCbaseZCSystemziIOZCrand ffi_ghczuwrapperZC0ZCbaseZCSystemziPosixziInternalsZCSEEKzuEND ffi_ghczuwrapperZC10ZCbaseZCSystemziPosixziInternalsZCtcgetattr ffi_ghczuwrapperZC11ZCbaseZCSystemziPosixziInternalsZCsigprocmask ffi_ghczuwrapperZC12ZCbaseZCSystemziPosixziInternalsZCsigaddset ffi_ghczuwrapperZC13ZCbaseZCSystemziPosixziInternalsZCsigemptyset ffi_ghczuwrapperZC14ZCbaseZCSystemziPosixziInternalsZCmkfifo ffi_ghczuwrapperZC15ZCbaseZCSystemziPosixziInternalsZCfcntl ffi_ghczuwrapperZC16ZCbaseZCSystemziPosixziInternalsZCfcntl ffi_ghczuwrapperZC17ZCbaseZCSystemziPosixziInternalsZCfcntl ffi_ghczuwrapperZC18ZCbaseZCSystemziPosixziInternalsZCutime ffi_ghczuwrapperZC19ZCbaseZCSystemziPosixziInternalsZCwrite ffi_ghczuwrapperZC1ZCbaseZCGHCziFloatZClog1pf ffi_ghczuwrapperZC1ZCbaseZCSystemziPosixziInternalsZCSEEKzuSET ffi_ghczuwrapperZC20ZCbaseZCSystemziPosixziInternalsZCwrite ffi_ghczuwrapperZC21ZCbaseZCSystemziPosixziInternalsZCread ffi_ghczuwrapperZC22ZCbaseZCSystemziPosixziInternalsZCread ffi_ghczuwrapperZC23ZCbaseZCSystemziPosixziInternalsZClseek ffi_ghczuwrapperZC2ZCbaseZCGHCziFloatZCexpm1 ffi_ghczuwrapperZC2ZCbaseZCSystemziPosixziInternalsZCSEEKzuCUR ffi_ghczuwrapperZC3ZCbaseZCGHCziFloatZClog1p ffi_ghczuwrapperZC3ZCbaseZCSystemziPosixziInternalsZCSzuISSOCK ffi_ghczuwrapperZC4ZCbaseZCSystemziPosixziInternalsZCSzuISFIFO ffi_ghczuwrapperZC5ZCbaseZCSystemziPosixziInternalsZCSzuISDIR ffi_ghczuwrapperZC6ZCbaseZCSystemziPosixziInternalsZCSzuISBLK ffi_ghczuwrapperZC7ZCbaseZCSystemziPosixziInternalsZCSzuISCHR ffi_ghczuwrapperZC8ZCbaseZCSystemziPosixziInternalsZCSzuISREG ffi_ghczuwrapperZC9ZCbaseZCSystemziPosixziInternalsZCtcsetattr ffi___gmpn_add ffi___gmpn_add_1 ffi___gmpn_cmp ffi___gmpn_divrem_1 ffi___gmpn_mod_1 ffi___gmpn_mul ffi___gmpn_mul_1 ffi___gmpn_popcount ffi___gmpn_sub ffi___gmpn_sub_1 ffi___gmpn_tdiv_qr ffi___hsbase_MD5Final ffi___hsbase_MD5Init ffi___hsbase_MD5Update ffi___hsbase_unsetenv ffi___hscore_bufsiz ffi___hscore_echo ffi___hscore_environ ffi___hscore_fd_cloexec ffi___hscore_f_getfl ffi___hscore_f_setfd ffi___hscore_f_setfl ffi___hscore_fstat ffi___hscore_ftruncate ffi___hscore_get_errno ffi___hscore_get_saved_termios ffi___hscore_icanon ffi___hscore_lflag ffi___hscore_lstat ffi___hscore_o_append ffi___hscore_o_binary ffi___hscore_o_creat ffi___hscore_o_excl ffi___hscore_o_noctty ffi___hscore_o_nonblock ffi___hscore_open ffi___hscore_o_rdonly ffi___hscore_o_rdwr ffi___hscore_o_trunc ffi___hscore_o_wronly ffi___hscore_poke_lflag ffi___hscore_ptr_c_cc ffi___hscore_set_errno ffi___hscore_set_saved_termios ffi___hscore_sig_block ffi___hscore_sig_setmask ffi___hscore_sigttou ffi___hscore_sizeof_siginfo_t ffi___hscore_sizeof_sigset_t ffi___hscore_sizeof_stat ffi___hscore_sizeof_termios ffi___hscore_stat ffi___hscore_st_dev ffi___hscore_st_ino ffi___hscore_st_mode ffi___hscore_st_mtime ffi___hscore_st_size ffi___hscore_tcsanow ffi___hscore_vmin ffi___hscore_vtime ffi_hs_free_stable_ptr ffi_hs_iconv ffi_hs_iconv_close ffi_hs_iconv_open ffi_hs_spt_key_count ffi_hs_spt_keys ffi_hs_spt_lookup ffi_integer_gmp_gcdext ffi_integer_gmp_gcd_word ffi_integer_gmp_invert ffi_integer_gmp_invert_word ffi_integer_gmp_mpn_and_n ffi_integer_gmp_mpn_andn_n ffi_integer_gmp_mpn_export ffi_integer_gmp_mpn_export1 ffi_integer_gmp_mpn_gcd ffi_integer_gmp_mpn_gcd_1 ffi_integer_gmp_mpn_get_d ffi_integer_gmp_mpn_import ffi_integer_gmp_mpn_ior_n ffi_integer_gmp_mpn_lshift ffi_integer_gmp_mpn_rshift ffi_integer_gmp_mpn_rshift_2c ffi_integer_gmp_mpn_sizeinbase ffi_integer_gmp_mpn_sizeinbase1 ffi_integer_gmp_mpn_tdiv_q ffi_integer_gmp_mpn_tdiv_r ffi_integer_gmp_mpn_xor_n ffi_integer_gmp_next_prime ffi_integer_gmp_next_prime1 ffi_integer_gmp_powm ffi_integer_gmp_powm1 ffi_integer_gmp_powm_word ffi_integer_gmp_rscan_nzbyte ffi_integer_gmp_scan_nzbyte ffi_integer_gmp_test_prime ffi_integer_gmp_test_prime1 ffi___int_encodeDouble ffi_isatty ffi_isDoubleDenormalized ffi_isDoubleFinite ffi_isDoubleInfinite ffi_isDoubleNaN ffi_isDoubleNegativeZero ffi_isFloatDenormalized ffi_isFloatFinite ffi_isFloatInfinite ffi_isFloatNaN ffi_isFloatNegativeZero ffi_libdwGetBacktrace ffi_libdwLookupLocation ffi_libdwPoolClear ffi_libdwPoolTake ffi_link ffi_localeEncoding ffi_lockFile ffi_malloc ffi_memcpy ffi_memmove ffi_memset ffi_performGC ffi_performMajorGC ffi_pipe ffi_poll ffi_putenv ffi_readlink ffi_realloc ffi_rintDouble ffi_rintFloat ffi_rts_disableThreadAllocationLimit ffi_rts_enableThreadAllocationLimit ffi_rts_getThreadAllocationCounter ffi_rts_getThreadId ffi_rts_setThreadAllocationCounter ffi_rtsSupportsBoundThreads ffi_setIOManagerControlFd ffi_setIOManagerWakeupFd ffi_setNumCapabilities ffi_setProgArgv ffi_setTimerManagerControlFd ffi_shutdownHaskellAndExit ffi_shutdownHaskellAndSignal ffi_stackOverflow ffi_startProfTimer ffi_stg_sig_install ffi_stopProfTimer ffi_strerror ffi_u_gencat ffi_u_iswalnum ffi_u_iswalpha ffi_u_iswcntrl ffi_u_iswlower ffi_u_iswprint ffi_u_iswspace ffi_u_iswupper ffi_umask ffi_unlink ffi_unlockFile ffi_u_towlower ffi_u_towtitle ffi_u_towupper ffi_waitpid" 
