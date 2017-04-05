module Veggies.Common where

import qualified Data.ByteString.Char8 as B

import Control.Monad

import Ollvm_ast

import Veggies.GenMonad
import Veggies.ASTUtils
import Veggies.CodeGenTypes

genEnterAndEval :: Coq_ident -> LG Coq_ident
genEnterAndEval v = do
    codePtr <- emitInstr $ getElemPtr hsTyP v [0,0]
    code <- emitInstr $ INSTR_Load False enterFunTyP (TYPE_Pointer enterFunTyP, ident codePtr) Nothing
    emitInstr $ INSTR_Call (enterFunTy, code) [(hsTyP, ident v)]

storeEnv :: Integer -> Coq_ident -> [Coq_ident] -> LG ()
storeEnv s envIdent names = do
    forM_ (zip [0..] names) $ \(i,n) -> do
        p <- emitInstr $ getElemPtr (envTyP s) envIdent [0,i]
        emitVoidInstr $ INSTR_Store False (TYPE_Pointer hsTyP, ident p) (hsTyP, ident n) Nothing

loadEnv :: Coq_ident -> [Coq_raw_id] -> LG ()
loadEnv envIdent names = do
    forM_ (zip [0..] names) $ \(i,n) -> do
        p <- emitInstr $ getElemPtr (envTyP 0) envIdent [0,i]
        emitNamedInstr n $ INSTR_Load False hsTyP (TYPE_Pointer hsTyP, ident p) Nothing

emitHsFun :: Coq_linkage -> Coq_raw_id -> [Coq_raw_id] -> [Coq_raw_id] -> LG Coq_ident -> G ()
emitHsFun linkage fun_name fv_names arg_names body = do
    blocks <- runLG $ do
        casted <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident closIdent) (mkFunClosureTyP 0)))
        fv_env <- emitInstr $ getElemPtr (mkFunClosureTyP 0) casted [0,3]
        loadEnv fv_env fv_names
        loadEnv argsIdent arg_names
        ret <- body
        emitTerm $ TERM_Ret (hsTyP, ident ret)
    emitTL $ TLDef $ mkHsFunDefinition linkage fun_name blocks
  where
    mkHsFunDefinition :: Coq_linkage -> Coq_raw_id -> [Coq_block] -> Coq_definition
    mkHsFunDefinition linkage n blocks = Coq_mk_definition
        (mkHsFunDeclaration linkage n)
        [closRawId, argsRawId]
        blocks

    mkHsFunDeclaration :: Coq_linkage -> Coq_raw_id -> Coq_declaration
    mkHsFunDeclaration linkage n = Coq_mk_declaration
        n
        hsFunTy
        ([],[[],[]])
        (Just linkage)
        Nothing
        Nothing
        Nothing
        []
        Nothing
        Nothing
        Nothing


genFunctionCall :: Coq_ident -> [Coq_ident] -> LG Coq_ident
genFunctionCall f [] = error $ "genFunctionCall" -- ++ show f
genFunctionCall evaledFun args_locals = do
    let arity = fromIntegral (length args_locals)

    argsRawPtr <- emitInstr $ INSTR_Alloca hsTyP (Just (i64, SV (VALUE_Integer arity))) Nothing
    argsPtr <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast (TYPE_Pointer hsTyP) (ident argsRawPtr) (envTyP 0)))
    storeEnv 0 argsPtr args_locals

    emitInstr $ INSTR_Call (callTy, callIdent)
        [(hsTyP, ident evaledFun), (arityTy, SV (VALUE_Integer arity)), (envTyP 0, ident argsPtr)]

genMalloc :: Coq_typ -> LG Coq_ident
genMalloc t = do
    -- http://stackoverflow.com/a/30830445/946226
    offset <- emitInstr $ INSTR_Op (SV (OP_GetElementPtr t (t, SV VALUE_Null) [(TYPE_I 32, SV (VALUE_Integer 1))]))
    size <- emitInstr $ INSTR_Op (SV (OP_Conversion Ptrtoint t (ident offset) (TYPE_I 64)))
    emitInstr $ INSTR_Call (mallocTy, mallocIdent) [(TYPE_I 64, ident size)]


allocateDataCon :: Integer -> Integer -> (LG (Coq_ident, [Coq_ident] ->  LG ()))
allocateDataCon tag arity = alloc
  where
    alloc = do
        dcRawPtr <- genMalloc thisDataConTyP
        dc <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast mallocRetTy (ident dcRawPtr) hsTyP))
        return (dc, fill dc)

    fill dcClosure args = do
        dcCasted <- emitInstr $
            INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident dcClosure) thisDataConTyP))

        codePtr <- emitInstr $ getElemPtr thisDataConTyP dcCasted [0,0]
        emitVoidInstr $ INSTR_Store False (TYPE_Pointer enterFunTyP, ident codePtr) (enterFunTyP, ident returnArgIdent) Nothing

        tagPtr <- emitInstr $ getElemPtr thisDataConTyP dcCasted [0,1]
        emitVoidInstr $ INSTR_Store False (tagTyP, ident tagPtr) (tagTy, SV (VALUE_Integer tag)) Nothing

        forM_ (zip [0..] args) $ \(n, arg) -> do
            p <- emitInstr $ getElemPtr thisDataConTyP dcCasted [0,2,n]
            emitVoidInstr $ INSTR_Store False (TYPE_Pointer hsTyP, ident p) (hsTyP, ident arg) Nothing

    thisDataConTy = mkDataConTy arity
    thisDataConTyP = TYPE_Pointer thisDataConTy

boxPrimValue :: Coq_typ -> Coq_typ -> Coq_value -> LG Coq_ident
boxPrimValue valTy boxTy v = do
    boxRawPtr <- genMalloc boxTyP
    box <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast mallocRetTy (ident boxRawPtr) hsTyP))

    casted <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident box) boxTyP))
    codePtr <- emitInstr $ getElemPtr boxTyP casted [0,0]
    emitVoidInstr $ INSTR_Store False (TYPE_Pointer enterFunTyP, ident codePtr) (enterFunTyP, ident returnArgIdent) Nothing

    setPrimValue valTy boxTy box v

    return box
  where boxTyP = TYPE_Pointer boxTy
        valTyP = TYPE_Pointer valTy

setPrimValue :: Coq_typ -> Coq_typ -> Coq_ident -> Coq_value -> LG ()
setPrimValue valTy boxTy box v = do
    casted <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident box) boxTyP))

    valPtr <- emitInstr $ getElemPtr boxTyP casted [0,1]
    emitVoidInstr $ INSTR_Store False (valTyP, ident valPtr) (valTy, v) Nothing
  where boxTyP = TYPE_Pointer boxTy
        valTyP = TYPE_Pointer valTy



unboxPrimValue :: Coq_typ -> Coq_typ -> Coq_ident -> LG Coq_ident
unboxPrimValue valTy boxTy v = do
    casted <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident v) boxTyP))
    valPtr <- emitInstr $ getElemPtr boxTyP casted [0,1]
    emitInstr $ INSTR_Load False valTy (valTyP, ident valPtr) Nothing
  where boxTyP = TYPE_Pointer boxTy
        valTyP = TYPE_Pointer valTy


staticIntLits :: [(Integer, String)]
staticIntLits = [ (n, "static_int_" ++ show n) | n <- [0,1] ]

genStaticIntLits :: G ()
genStaticIntLits = sequence_ [ genIntegerLitForReal n (Name name) | (n,name) <- staticIntLits ]

genIntegerLit :: Integer -> G Coq_ident
genIntegerLit l | Just n <- lookup l staticIntLits = return $ ID_Global (Name n)
genIntegerLit l = do
    litName <- freshGlobal
    genIntegerLitForReal l litName
    return (ID_Global litName)

genIntegerLitForReal l litName = do
    emitAliasedGlobal LINKAGE_Private litName hsTy intBoxTy $
        SV $ VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                          , (TYPE_I 64, SV (VALUE_Integer (fromIntegral l)))
                          ]


genByteStringLit :: B.ByteString -> G Coq_ident
genByteStringLit s = genStringLit (B.unpack s ++ "\0")

genStringLit :: String -> G Coq_ident
genStringLit msg = do
    strName <- freshGlobal
    litName <- freshGlobal

    emitTL $ TLGlobal $ Coq_mk_global
        strName
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

    emitAliasedGlobal LINKAGE_External litName hsTy ptrBoxTy $
        SV $ VALUE_Struct [ (enterFunTyP, ident printAndExitIdent)
                          , (ptrTy, SV (OP_Conversion Bitcast msgTyP (ident (ID_Global strName)) ptrTy))
                          ]
    return (ID_Global litName)
  where
    msgTy = TYPE_Array (fromIntegral (length msg)) (TYPE_I 8)
    msgTyP = TYPE_Pointer msgTy

genPrintAndExitClosure :: String -> String -> G ()
genPrintAndExitClosure name msg = do
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

    emitAliasedGlobal LINKAGE_External raw_ident hsTy printAndExitClosureTy $
        SV $ VALUE_Struct [ (enterFunTyP, ident printAndExitIdent)
                          , (ptrTy, SV (OP_Conversion Bitcast msgTyP (ident (ID_Global str_ident)) ptrTy))
                          ]

  where
    raw_ident = Name ident_str
    ident_str = name

    tmp_ident = Name tmp_str
    tmp_str = name ++ "_tmp"

    str_ident = Name str_str
    str_str = name ++ "_str"

    msgTy = TYPE_Array (fromIntegral (length msg)) (TYPE_I 8)
    msgTyP = TYPE_Pointer msgTy

