module Veggies.Common where

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
    litNameTmp <- freshGlobal

    let val = SV $ VALUE_Struct [ (enterFunTyP, ident returnArgIdent)
                                , (TYPE_I 64, SV (VALUE_Integer (fromIntegral l)))
                                ]

    emitTL $ TLGlobal $ Coq_mk_global
         litNameTmp
         intBoxTy
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
         litName
         hsTy
         (SV (OP_Conversion Bitcast intBoxTyP (ident (ID_Global litNameTmp)) hsTyP))
         (Just LINKAGE_Private)
         Nothing
         Nothing
         Nothing
         False
    return ()
