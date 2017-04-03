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

genFunctionCall :: Coq_ident -> [Coq_ident] -> LG Coq_ident
genFunctionCall f [] = error $ "genFunctionCall" -- ++ show f
genFunctionCall evaledFun args_locals = do
    let arity = fromIntegral (length args_locals)
    let thisFunClosTyP = TYPE_Pointer (mkFunClosureTy arity 0)
    let thisFunTy = hsFunTy arity 0
    let thisFunTyP = TYPE_Pointer thisFunTy

    castedFun <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident evaledFun) thisFunClosTyP))
    funPtr <- emitInstr $ getElemPtr thisFunClosTyP castedFun [0,1]
    fun <- emitInstr $ INSTR_Load False thisFunTyP (TYPE_Pointer thisFunTyP, ident funPtr) Nothing

    arityPtr <- emitInstr $ getElemPtr thisFunClosTyP castedFun [0,2]
    actualArity <- emitInstr $ INSTR_Load False arityTy (arityTyP, ident arityPtr) Nothing

    n <- instrNumber
    let localLabel x = Name $ "if_" ++ show n ++ "_" ++ x
        okLabel = localLabel "ok"
        okRetLabel = localLabel "ok_ret"
        badLabel = localLabel "bad"
        badRetLabel = localLabel "bad_ret"
        joinLabel = localLabel "join"

    emitTerm $ TERM_Switch (arityTy,ident actualArity) (TYPE_Label, ID_Local badLabel)
        [ ((arityTy, SV (VALUE_Integer arity)), (TYPE_Label, ID_Local okLabel)) ]

    startNamedBlock okLabel
    closPtr <- emitInstr $ getElemPtr thisFunClosTyP castedFun [0,3]

    ret <- emitInstr $ INSTR_Call (thisFunTy, fun) $
        (envTyP 0, ident closPtr) : [(hsTyP, ident a) | a <- args_locals ]
    namedBr1Block okRetLabel joinLabel

    startNamedBlock badLabel
    badRet <- emitInstr $ INSTR_Call (badArityTy, badArityIdent) []
    namedBr1Block badRetLabel joinLabel

    namedPhiBlock hsTyP joinLabel [ (ret, okRetLabel) , (badRet, badRetLabel) ] 

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

boxPrimValue :: Coq_typ -> Coq_typ -> Coq_ident -> LG Coq_ident
boxPrimValue valTy boxTy v = do
    boxRawPtr <- genMalloc boxTyP

    casted <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast mallocRetTy (ident boxRawPtr) boxTyP))

    codePtr <- emitInstr $ getElemPtr boxTy casted [0,0]
    emitVoidInstr $ INSTR_Store False (TYPE_Pointer enterFunTyP, ident codePtr) (enterFunTyP, ident returnArgIdent) Nothing

    valPtr <- emitInstr $ getElemPtr boxTy casted [0,1]
    emitVoidInstr $ INSTR_Store False (valTyP, ident valPtr) (valTy, ident v) Nothing

    box <- emitInstr $
        INSTR_Op (SV (OP_Conversion Bitcast mallocRetTy (ident boxRawPtr) hsTyP))
    return box
  where boxTyP = TYPE_Pointer boxTy
        valTyP = TYPE_Pointer valTy

unboxPrimValue :: Coq_typ -> Coq_typ -> Coq_ident -> LG Coq_ident
unboxPrimValue valTy boxTy v = do
    casted <- emitInstr $ INSTR_Op (SV (OP_Conversion Bitcast hsTyP (ident v) boxTyP))
    valPtr <- emitInstr $ getElemPtr boxTy casted [0,1]
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

