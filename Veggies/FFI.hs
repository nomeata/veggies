module Veggies.FFI where

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


mkFFICall :: String -> [Coq_ident] -> LG Coq_ident
mkFFICall "getOrSetGHCConcSignalSignalHandlerStore" args = do
    genReturnIO (args !! 1) (args !! 0)
mkFFICall "hs_free_stable_ptr" args = do
    genUnboxedUnitTuple (args !! 1)
mkFFICall "stg_sig_install" args = do
    genReturnIO (args !! 3) (args !! 1)
mkFFICall "localeEncoding" args = do
    res <- liftG $ genStringLit "UTF-8"
    genReturnIO (args !! 0) res
mkFFICall "hs_iconv_open" args = do
    ptr1 <- unboxPrimValue ptrTy ptrBoxTy (args !! 0)
    ptr2 <- unboxPrimValue ptrTy ptrBoxTy (args !! 1)
    let iconv_open_ty = TYPE_Function ptrTy [ptrTy, ptrTy]
        iconv_open_ident = ID_Global (Name "iconv_open")
    ptr <- emitInstr $ INSTR_Call (iconv_open_ty, iconv_open_ident)
        [(ptrTy, ident ptr1), (ptrTy, ident ptr2)]
    res <- boxPrimValue ptrTy ptrBoxTy (ident ptr)
    genReturnIO (args !! 2) res
{-
size_t hs_iconv(iconv_t cd,
                const char* * inbuf, size_t * inbytesleft,
                char* * outbuf, size_t * outbytesleft)
{ return iconv(cd, (void*)inbuf, inbytesleft, outbuf, outbytesleft); }
-}
mkFFICall "hs_iconv" args = do
    ptr1 <- unboxPrimValue ptrTy ptrBoxTy (args !! 0)
    ptr2 <- unboxPrimValue ptrTy ptrBoxTy (args !! 1)
    ptr3 <- unboxPrimValue ptrTy ptrBoxTy (args !! 2)
    ptr4 <- unboxPrimValue ptrTy ptrBoxTy (args !! 3)
    ptr5 <- unboxPrimValue ptrTy ptrBoxTy (args !! 4)
    let iconv_ty = TYPE_Function i64 [ptrTy, ptrTy, ptrTy, ptrTy, ptrTy]
        iconv_ident = ID_Global (Name "iconv")
    ret <- emitInstr $ INSTR_Call (iconv_ty, iconv_ident)
        [ (ptrTy, ident ptr1)
        , (ptrTy, ident ptr2)
        , (ptrTy, ident ptr3)
        , (ptrTy, ident ptr4)
        , (ptrTy, ident ptr5)
        ]
    retBox <- boxPrimValue i64 intBoxTy (ident ret)
    genReturnIO (args !! 5) retBox
{-
int hs_iconv_close(iconv_t cd) {
        return iconv_close(cd);
-}
mkFFICall "hs_iconv_close" args = do
    ptr1 <- unboxPrimValue ptrTy ptrBoxTy (args !! 0)
    let iconv_close_ty = TYPE_Function i64 [ptrTy]
        iconv_close_ident = ID_Global (Name "iconv_close")
    ret <- emitInstr $ INSTR_Call (iconv_close_ty, iconv_close_ident)
        [ (ptrTy, ident ptr1)
        ]
    retBox <- boxPrimValue i64 intBoxTy (ident ret)
    genReturnIO (args !! 1) retBox
mkFFICall "isatty" args = do
    int <- unboxPrimValue i64 intBoxTy (args !! 0)
    let isatty_ty = TYPE_Function i64 [i64]
        isatty_ident = ID_Global (Name "isatty")
    ret <- emitInstr $ INSTR_Call (isatty_ty, isatty_ident)
        [ (i64, ident int)
        ]
    retBox <- boxPrimValue i64 intBoxTy (ident ret)
    genReturnIO (args !! 1) retBox
mkFFICall "u_towupper" args = do
    int <- unboxPrimValue i64 intBoxTy (args !! 0)
    let u_towupper_ty = TYPE_Function i64 [i64]
        u_towupper_ident = ID_Global (Name "u_towupper")
    ret <- emitInstr $ INSTR_Call (u_towupper_ty, u_towupper_ident)
        [ (i64, ident int)
        ]
    retBox <- boxPrimValue i64 intBoxTy (ident ret)
    genReturnIO (args !! 1) retBox
-- extern int fdReady(int fd, int write, int msecs, int isSock);
mkFFICall "fdReady" args = do
    int1 <- unboxPrimValue i64 intBoxTy (args !! 0)
    int2 <- unboxPrimValue i64 intBoxTy (args !! 1)
    int3 <- unboxPrimValue i64 intBoxTy (args !! 2)
    int4 <- unboxPrimValue i64 intBoxTy (args !! 3)
    let fdReady_ty = TYPE_Function i64 [i64, i64, i64, i64]
        fdReady_ident = ID_Global (Name "fdReady")
    ret <- emitInstr $ INSTR_Call (fdReady_ty, fdReady_ident)
        [ (i64, ident int1)
        , (i64, ident int2)
        , (i64, ident int3)
        , (i64, ident int4)
        ]
    retBox <- boxPrimValue i64 intBoxTy (ident ret)
    genReturnIO (args !! 4) retBox
--   c_write :: CInt -> Ptr Word8 -> CSize -> IO CSsize
mkFFICall "ghczuwrapperZC20ZCbaseZCSystemziPosixziInternalsZCwrite" args = do
    a1 <- unboxPrimValue i64 intBoxTy (args !! 0)
    a2 <- unboxPrimValue ptrTy ptrBoxTy (args !! 1)
    a3 <- unboxPrimValue i64 intBoxTy (args !! 2)
    let fun_ty = TYPE_Function i64 [i64, ptrTy, i64]
        fun_ident = ID_Global (Name "ghczuwrapperZC20ZCbaseZCSystemziPosixziInternalsZCwrite")
    ret <- emitInstr $ INSTR_Call (fun_ty, fun_ident)
        [ (i64, ident a1)
        , (ptrTy, ident a2)
        , (i64, ident a3)
        ]
    retBox <- boxPrimValue i64 intBoxTy (ident ret)
    genReturnIO (args !! 3) retBox
mkFFICall "debugBelch2" args = do
    a1 <- unboxPrimValue ptrTy ptrBoxTy (args !! 0)
    a2 <- unboxPrimValue ptrTy ptrBoxTy (args !! 1)
    let fun_ty = TYPE_Function TYPE_Void [ptrTy, ptrTy]
        fun_ident = ID_Global (Name "debugBelch2")
    emitVoidInstr $ INSTR_Call (fun_ty, fun_ident)
        [ (ptrTy, ident a1)
        , (ptrTy, ident a2)
        ]
    return (args !! 2)
mkFFICall "errorBelch2" args = do
    a1 <- unboxPrimValue ptrTy ptrBoxTy (args !! 0)
    a2 <- unboxPrimValue ptrTy ptrBoxTy (args !! 1)
    let fun_ty = TYPE_Function TYPE_Void [ptrTy, ptrTy]
        fun_ident = ID_Global (Name "errorBelch2")
    emitVoidInstr $ INSTR_Call (fun_ty, fun_ident)
        [ (ptrTy, ident a1)
        , (ptrTy, ident a2)
        ]
    return (args !! 2)
mkFFICall "rtsSupportsBoundThreads" args = do
    res <- liftG $ genIntegerLit 0
    genReturnIO (args !! 0) res

mkFFICall name _ = printAndExit $ "Unsupported FFI call: " ++ name
