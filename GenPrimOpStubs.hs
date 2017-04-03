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
    (dc, fill) <- allocateDataCon 1 2
    fill [ s , x ]
    return dc

primOpBody :: PrimOp -> Maybe (LG ())
primOpBody MakeStablePtrOp = Just $ do
    ret <- genReturnIO (paramIdents !! 1) nullPtrBoxIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody PutMVarOp = Just $ do
    ret <- genReturnIO (paramIdents !! 2) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody NewMVarOp = Just $ do
    ret <- genReturnIO (paramIdents !! 0) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody NewArrayOp = Just $ do
    ret <- genReturnIO (paramIdents !! 2) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody NoDuplicateOp = Just $ do
    emitTerm $ TERM_Ret (hsTyP, ident (paramIdents !! 0))

primOpBody MaskAsyncExceptionsOp = Just $ do
   -- apply first argument to the second argument
    evaledFun <- genEnterAndEval (paramIdents !! 0)
    ret <- genFunctionCall evaledFun [(paramIdents !! 1)]
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody MaskStatus = Just $ do
    zero <- liftG $ genIntegerLit 0
    ret <- genReturnIO (paramIdents !! 0) zero
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody MkWeakNoFinalizerOp = Just $ do
    ret <- genReturnIO (paramIdents !! 2) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody MyThreadIdOp = Just $ do
    ret <- genReturnIO (paramIdents !! 0) voidIdent
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody CatchOp = Just $ do
   -- apply first argument to the third argument
    evaledFun <- genEnterAndEval (paramIdents !! 0)
    ret <- genFunctionCall evaledFun [(paramIdents !! 2)]
    emitTerm $ TERM_Ret (hsTyP, ident ret)

primOpBody _ = Nothing

ffiBody :: String -> Maybe (Int, LG ())
ffiBody "ffi_getOrSetGHCConcSignalSignalHandlerStore"
    = Just (2, do
        ret <- genReturnIO (paramIdents !! 1) (paramIdents !! 0)
        emitTerm $ TERM_Ret (hsTyP, ident ret)
      )
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

supportedPrimOps :: [PrimOp]
supportedPrimOps =
    [ IntAddOp
    , IntSubOp
    , IntMulOp
    , WordAddOp
    , WordSubOp
    , WordMulOp
    ]

primModule :: Coq_modul
primModule = mkCoqModul "GHC.Prim" $ runG $ do
    mapM_ emitTL defaultTyDecls
    genStaticIntLits
    genNullPtrBox

    mapM_ genPrimOp (allThePrimOps \\ supportedPrimOps)
    mapM_ genPrimVal ["void#", "realWorld#", "proxy#"]
    mapM_ genFFIFunc ffi_fuction_calls

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


ffi_fuction_calls :: [String]
ffi_fuction_calls = words "ffi_access ffi_calloc ffi_chmod ffi_clk_tck ffi_close ffi_cmp_thread ffi_creat ffi_debugBelch2 ffi_debugErrLn ffi_debugLn ffi_dup ffi_dup2 ffi_epoll_create ffi_epoll_ctl ffi_epoll_wait ffi_errorBelch2 ffi_eventfd ffi_eventfd_write ffi_fdReady ffi_fork ffi_forkOS_createThread ffi_forkOS_entry ffi_free ffi_freeHaskellFunctionPtr ffi_getCcFlags ffi_getConcFlags ffi_getDebugFlags ffi_getenv ffi_getFullProgArgv ffi_getGcFlags ffi_getGCStats ffi_getGCStatsEnabled ffi_getMiscFlags ffi_getMonotonicNSec ffi_getNumberOfProcessors ffi_getOrSetGHCConcSignalSignalHandlerStore ffi_getOrSetSystemEventThreadEventManagerStore ffi_getOrSetSystemEventThreadIOManagerThreadStore ffi_getOrSetSystemTimerThreadEventManagerStore ffi_getOrSetSystemTimerThreadIOManagerThreadStore ffi_getpid ffi_getProfFlags ffi_getProgArgv ffi_getTickyFlags ffi_getTraceFlags ffi_ghczuwrapperZC0ZCbaseZCGHCziFloatZCexpm1f ffi_ghczuwrapperZC0ZCbaseZCSystemziCPUTimeZCgetrusage ffi_ghczuwrapperZC0ZCbaseZCSystemziIOZCrand ffi_ghczuwrapperZC0ZCbaseZCSystemziPosixziInternalsZCSEEKzuEND ffi_ghczuwrapperZC10ZCbaseZCSystemziPosixziInternalsZCtcgetattr ffi_ghczuwrapperZC11ZCbaseZCSystemziPosixziInternalsZCsigprocmask ffi_ghczuwrapperZC12ZCbaseZCSystemziPosixziInternalsZCsigaddset ffi_ghczuwrapperZC13ZCbaseZCSystemziPosixziInternalsZCsigemptyset ffi_ghczuwrapperZC14ZCbaseZCSystemziPosixziInternalsZCmkfifo ffi_ghczuwrapperZC15ZCbaseZCSystemziPosixziInternalsZCfcntl ffi_ghczuwrapperZC16ZCbaseZCSystemziPosixziInternalsZCfcntl ffi_ghczuwrapperZC17ZCbaseZCSystemziPosixziInternalsZCfcntl ffi_ghczuwrapperZC18ZCbaseZCSystemziPosixziInternalsZCutime ffi_ghczuwrapperZC19ZCbaseZCSystemziPosixziInternalsZCwrite ffi_ghczuwrapperZC1ZCbaseZCGHCziFloatZClog1pf ffi_ghczuwrapperZC1ZCbaseZCSystemziPosixziInternalsZCSEEKzuSET ffi_ghczuwrapperZC20ZCbaseZCSystemziPosixziInternalsZCwrite ffi_ghczuwrapperZC21ZCbaseZCSystemziPosixziInternalsZCread ffi_ghczuwrapperZC22ZCbaseZCSystemziPosixziInternalsZCread ffi_ghczuwrapperZC23ZCbaseZCSystemziPosixziInternalsZClseek ffi_ghczuwrapperZC2ZCbaseZCGHCziFloatZCexpm1 ffi_ghczuwrapperZC2ZCbaseZCSystemziPosixziInternalsZCSEEKzuCUR ffi_ghczuwrapperZC3ZCbaseZCGHCziFloatZClog1p ffi_ghczuwrapperZC3ZCbaseZCSystemziPosixziInternalsZCSzuISSOCK ffi_ghczuwrapperZC4ZCbaseZCSystemziPosixziInternalsZCSzuISFIFO ffi_ghczuwrapperZC5ZCbaseZCSystemziPosixziInternalsZCSzuISDIR ffi_ghczuwrapperZC6ZCbaseZCSystemziPosixziInternalsZCSzuISBLK ffi_ghczuwrapperZC7ZCbaseZCSystemziPosixziInternalsZCSzuISCHR ffi_ghczuwrapperZC8ZCbaseZCSystemziPosixziInternalsZCSzuISREG ffi_ghczuwrapperZC9ZCbaseZCSystemziPosixziInternalsZCtcsetattr ffi___gmpn_add ffi___gmpn_add_1 ffi___gmpn_cmp ffi___gmpn_divrem_1 ffi___gmpn_mod_1 ffi___gmpn_mul ffi___gmpn_mul_1 ffi___gmpn_popcount ffi___gmpn_sub ffi___gmpn_sub_1 ffi___gmpn_tdiv_qr ffi___hsbase_MD5Final ffi___hsbase_MD5Init ffi___hsbase_MD5Update ffi___hsbase_unsetenv ffi___hscore_bufsiz ffi___hscore_echo ffi___hscore_environ ffi___hscore_fd_cloexec ffi___hscore_f_getfl ffi___hscore_f_setfd ffi___hscore_f_setfl ffi___hscore_fstat ffi___hscore_ftruncate ffi___hscore_get_errno ffi___hscore_get_saved_termios ffi___hscore_icanon ffi___hscore_lflag ffi___hscore_lstat ffi___hscore_o_append ffi___hscore_o_binary ffi___hscore_o_creat ffi___hscore_o_excl ffi___hscore_o_noctty ffi___hscore_o_nonblock ffi___hscore_open ffi___hscore_o_rdonly ffi___hscore_o_rdwr ffi___hscore_o_trunc ffi___hscore_o_wronly ffi___hscore_poke_lflag ffi___hscore_ptr_c_cc ffi___hscore_set_errno ffi___hscore_set_saved_termios ffi___hscore_sig_block ffi___hscore_sig_setmask ffi___hscore_sigttou ffi___hscore_sizeof_siginfo_t ffi___hscore_sizeof_sigset_t ffi___hscore_sizeof_stat ffi___hscore_sizeof_termios ffi___hscore_stat ffi___hscore_st_dev ffi___hscore_st_ino ffi___hscore_st_mode ffi___hscore_st_mtime ffi___hscore_st_size ffi___hscore_tcsanow ffi___hscore_vmin ffi___hscore_vtime ffi_hs_free_stable_ptr ffi_hs_iconv ffi_hs_iconv_close ffi_hs_iconv_open ffi_hs_spt_key_count ffi_hs_spt_keys ffi_hs_spt_lookup ffi_integer_gmp_gcdext ffi_integer_gmp_gcd_word ffi_integer_gmp_invert ffi_integer_gmp_invert_word ffi_integer_gmp_mpn_and_n ffi_integer_gmp_mpn_andn_n ffi_integer_gmp_mpn_export ffi_integer_gmp_mpn_export1 ffi_integer_gmp_mpn_gcd ffi_integer_gmp_mpn_gcd_1 ffi_integer_gmp_mpn_get_d ffi_integer_gmp_mpn_import ffi_integer_gmp_mpn_ior_n ffi_integer_gmp_mpn_lshift ffi_integer_gmp_mpn_rshift ffi_integer_gmp_mpn_rshift_2c ffi_integer_gmp_mpn_sizeinbase ffi_integer_gmp_mpn_sizeinbase1 ffi_integer_gmp_mpn_tdiv_q ffi_integer_gmp_mpn_tdiv_r ffi_integer_gmp_mpn_xor_n ffi_integer_gmp_next_prime ffi_integer_gmp_next_prime1 ffi_integer_gmp_powm ffi_integer_gmp_powm1 ffi_integer_gmp_powm_word ffi_integer_gmp_rscan_nzbyte ffi_integer_gmp_scan_nzbyte ffi_integer_gmp_test_prime ffi_integer_gmp_test_prime1 ffi___int_encodeDouble ffi_isatty ffi_isDoubleDenormalized ffi_isDoubleFinite ffi_isDoubleInfinite ffi_isDoubleNaN ffi_isDoubleNegativeZero ffi_isFloatDenormalized ffi_isFloatFinite ffi_isFloatInfinite ffi_isFloatNaN ffi_isFloatNegativeZero ffi_libdwGetBacktrace ffi_libdwLookupLocation ffi_libdwPoolClear ffi_libdwPoolTake ffi_link ffi_localeEncoding ffi_lockFile ffi_malloc ffi_memcpy ffi_memmove ffi_memset ffi_performGC ffi_performMajorGC ffi_pipe ffi_poll ffi_putenv ffi_readlink ffi_realloc ffi_rintDouble ffi_rintFloat ffi_rts_disableThreadAllocationLimit ffi_rts_enableThreadAllocationLimit ffi_rts_getThreadAllocationCounter ffi_rts_getThreadId ffi_rts_setThreadAllocationCounter ffi_rtsSupportsBoundThreads ffi_setIOManagerControlFd ffi_setIOManagerWakeupFd ffi_setNumCapabilities ffi_setProgArgv ffi_setTimerManagerControlFd ffi_shutdownHaskellAndExit ffi_shutdownHaskellAndSignal ffi_stackOverflow ffi_startProfTimer ffi_stg_sig_install ffi_stopProfTimer ffi_strerror ffi_u_gencat ffi_u_iswalnum ffi_u_iswalpha ffi_u_iswcntrl ffi_u_iswlower ffi_u_iswprint ffi_u_iswspace ffi_u_iswupper ffi_umask ffi_unlink ffi_unlockFile ffi_u_towlower ffi_u_towtitle ffi_u_towupper ffi_waitpid" 
