{-# LANGUAGE TupleSections #-}
module Veggies.FFI where

import PrimOp
import Encoding
import OccName
import Type
import TyCon
import TysPrim
import Outputable
import Util

import Data.List
import qualified Data.ByteString.Lazy as B
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as T

import Ollvm_ast
import Veggies.GenMonad
import Veggies.CodeGenTypes
import Veggies.ASTUtils
import Veggies.Common

llvmTypes :: Type -> Maybe (Coq_typ, Coq_typ)
llvmTypes t | isPtrLike (tyConAppTyCon t) = Just (ptrTy, ptrBoxTy)
            | isIntLike (tyConAppTyCon t) = Just (i64, intBoxTy)
            | otherwise                   = Nothing

unpackFFI :: ((Coq_typ, Coq_typ), Coq_ident) -> LG (Coq_typ, Coq_value)
unpackFFI ((unpackedTy, packedTy),a) = do
    v <- unboxPrimValue unpackedTy packedTy a
    return (unpackedTy, ident v)

isPtrLike tc = tc `elem`
    [ mutableByteArrayPrimTyCon
    , byteArrayPrimTyCon
    , addrPrimTyCon
    , stablePtrPrimTyCon
    ]

isIntLike tc = tc `elem`
    [ intPrimTyCon
    , wordPrimTyCon
    ]

mkVoidIOCall :: String -> [((Coq_typ, Coq_typ), Coq_ident)] -> Coq_ident -> LG Coq_ident
mkVoidIOCall name typed_args state_token = do
    unpacked_args <- mapM unpackFFI typed_args
    let fun_type = TYPE_Function TYPE_Void (map (fst.fst) typed_args)
    emitVoidInstr $ INSTR_Call (fun_type, ID_Global (Name name)) unpacked_args
    genUnboxedUnitTuple state_token

mkIOCall :: String -> (Coq_typ, Coq_typ) -> [((Coq_typ, Coq_typ), Coq_ident)] -> Coq_ident -> LG Coq_ident
mkIOCall name (res_ty, res_box_ty) typed_args state_token = do
    unpacked_args <- mapM unpackFFI typed_args
    let fun_type = TYPE_Function res_ty (map (fst.fst) typed_args)
    r <- emitInstr $ INSTR_Call (fun_type, ID_Global (Name name)) unpacked_args
    rBox <- boxPrimValue res_ty res_box_ty (ident r)
    genReturnIO  state_token rBox

isStateToken :: Type -> Bool
isStateToken t | Just (tc, [_]) <- splitTyConApp_maybe t
               , tc == statePrimTyCon
               = True
               | otherwise = False

isUnboxedTuple_maybe :: Type -> Maybe [Type]
isUnboxedTuple_maybe t | Just (tc, args) <- splitTyConApp_maybe t
                       , isUnboxedTupleTyCon tc
                       = Just (dropRuntimeRepArgs args)
                       | otherwise = Nothing


explicitlyUnsupported =
    [ "__hscore_get_saved_termios"
    , "__hscore_set_saved_termios"
    , "setIOManagerWakeupFd"
    , "getMonotonicNSec"
    , "getOrSetSystemEventThreadEventManagerStore"
    , "getOrSetSystemEventThreadIOManagerThreadStore"
    , "getOrSetSystemTimerThreadIOManagerThreadStore"
    , "getOrSetSystemTimerThreadEventManagerStore"
    , "setIOManagerControlFd"
    , "setTimerManagerControlFd"
    , "lockFile"
    , "unlockFile"
    ]

mkFFICall :: String -> Type -> [Coq_ident] -> LG Coq_ident

mkFFICall "getOrSetGHCConcSignalSignalHandlerStore" _ args = do
    genReturnIO (args !! 1) (args !! 0)
mkFFICall "hs_free_stable_ptr" _ args = do
    genUnboxedUnitTuple (args !! 1)
mkFFICall "stg_sig_install" _ args = do
    genReturnIO (args !! 3) (args !! 1)
mkFFICall "localeEncoding" _ args = do
    res <- liftG $ genStringLit "UTF-8"
    genReturnIO (args !! 0) res
mkFFICall "shutdownHaskellAndExit" _ args = do
    v <- unboxPrimValue i64 intBoxTy (args !! 0)
    emitVoidInstr $ INSTR_Call (exitTy, exitIdent) [(i64, ident v)]
    genUnboxedUnitTuple (args !! 2) -- should be unreachable
mkFFICall "shutdownHaskellAndSignal" _ args = do
    v <- unboxPrimValue i64 intBoxTy (args !! 0)
    emitVoidInstr $ INSTR_Call (exitTy, exitIdent) [(i64, ident v)]
    genUnboxedUnitTuple (args !! 2) -- should be unreachable
mkFFICall "rtsSupportsBoundThreads" _ args = do
    res <- liftG $ genIntegerLit 0
    genReturnIO (args !! 0) res
mkFFICall "getNumberOfProcessors" _ args = do
    res <- liftG $ genIntegerLit 1
    genReturnIO (args !! 0) res
mkFFICall "setNumCapabilities" _ args = do
    genUnboxedUnitTuple (args !! 1)

mkFFICall fun_name ty args | fun_name `elem` explicitlyUnsupported=
    printAndExit $ showSDocUnsafe $ msg
  where
    msg = text  "Explicitly unsupported FFI call:" $$
          text fun_name <+> text "::" <+> ppr ty

-- Now we find out the shape of the call (IO or no IO, return value or not) and
-- call the appropriate helper.

-- Look through foralls
mkFFICall name t args | isForAllTy t
    = mkFFICall name (snd (splitForAllTys t)) args

mkFFICall name typ args
    | (args_ty, res_ty) <- splitFunTys typ
    , Just [res_ty'] <- isUnboxedTuple_maybe res_ty
    , isStateToken res_ty'
    , isStateToken (last args_ty)
    , Just llvm_arg_tys <- mapM llvmTypes (init args_ty)
    = mkVoidIOCall name (zipEqual "mkVoidIOCall" llvm_arg_tys args) (last args)

    | (args_ty, res_ty) <- splitFunTys typ
    , Just [res_ty1, res_ty2] <- isUnboxedTuple_maybe res_ty
    , isStateToken res_ty1
    , isStateToken (last args_ty)
    , Just llvm_arg_tys <- mapM llvmTypes (init args_ty)
    , Just llvm_res_ty <- llvmTypes res_ty2
    = mkIOCall name llvm_res_ty (zipEqual "mkIOCall" llvm_arg_tys args) (last args)


mkFFICall fun_name ty args =
    pprTrace "mkFFICall" msg $
    printAndExit $ showSDocUnsafe $ msg
  where
    msg = text  "Unsupported FFI call type:" $$
          text fun_name <+> text "::" <+> ppr ty
