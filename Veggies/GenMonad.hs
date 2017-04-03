{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
module Veggies.GenMonad where

import Data.List
import Data.Maybe
import Data.Bifunctor
import Control.Arrow ((&&&))
import Data.Either
import Data.Function
import Control.Monad.State
import Control.Monad.Writer

import Ollvm_ast

import Debug.Trace
import GHC.Stack

import Veggies.ASTUtils

-- Generating top-level definitions
type G = WriterT [TopLevelThing] (State Integer)
-- Also generting instructions
type PartialBlock = (Coq_block_id, [(Coq_instr_id, Coq_instr)])
type LG = StateT (Maybe PartialBlock) (WriterT [Coq_block] (StateT Integer G))

runG :: G () -> [TopLevelThing]
runG g = addExternalDeclarations $ evalState (execWriterT g) 0

runLG :: LG () -> G ([Coq_block])
runLG lg = evalStateT (execWriterT (evalStateT lg' Nothing)) 0
  where
    lg' = do
        startNamedBlock (Name "start")
        lg
        ensureNoBlock

ensureNoBlock :: HasCallStack => LG ()
ensureNoBlock = do
    s <- get
    case s of
        Nothing -> return ()
        Just (n,_) -> error $ "Unfinished block"

liftG :: G a -> LG a
liftG = lift .  lift . lift

freshGlobal :: G Coq_local_id
freshGlobal = fmap Anon $ lift $ state (id &&& (+1))

freshLocal :: LG Coq_local_id
freshLocal = fmap Anon $ lift $ state (id &&& (+1))

instrNumber :: LG Integer
instrNumber = lift $ get

emitTL :: TopLevelThing -> G ()
emitTL tlt = tell [tlt]

emitTerm :: Coq_terminator -> LG ()
emitTerm t = do
    s <- get
    case s of
        Nothing -> error $ "No block ot finish"
        Just (n,instrs) ->
            lift $ tell [Coq_mk_block n instrs t (IVoid 0)]
    put Nothing

maybeEmitTerm :: Coq_terminator -> LG ()
maybeEmitTerm t = do
    s <- get
    case s of
        Nothing -> return ()
        Just (n,instrs) ->
            lift $ tell [Coq_mk_block n instrs t (IVoid 0)]
    put Nothing

emitInstr :: Coq_instr -> LG Coq_ident
emitInstr instr = do
    instrId <- freshLocal
    emitNamedInstr instrId instr
    return (ID_Local instrId)

emitVoidInstr :: Coq_instr -> LG ()
emitVoidInstr instr = do
    modify $ \s -> case s of
            Nothing -> error $ "No block ot finish"
            Just (n,instrs) -> Just(n, instrs ++ [(IVoid 0, instr)])
    return ()

emitNamedInstr :: Coq_local_id -> Coq_instr -> LG ()
emitNamedInstr instrId instr = do
    modify $ \s -> case s of
            Nothing -> error $ "No block ot finish"
            Just (n,instrs) -> Just(n, instrs ++ [(IId instrId, instr)])

startNamedBlock :: Coq_local_id -> LG ()
startNamedBlock blockId = do
    ensureNoBlock
    put $ Just (blockId, [])

namedBr1Block :: HasCallStack => Coq_local_id -> Coq_local_id -> LG ()
namedBr1Block blockId toBlockId = do
    maybeEmitTerm $ TERM_Br_1 (TYPE_Label, ID_Local blockId)
    startNamedBlock blockId
    emitTerm $ TERM_Br_1 (TYPE_Label, ID_Local toBlockId)

namedPhiBlock :: HasCallStack => Coq_typ -> Coq_block_id -> [(Coq_ident, Coq_block_id)] -> LG Coq_ident
namedPhiBlock ty blockId [] = error "namedPhiBlock"
namedPhiBlock ty blockId pred = do
    ensureNoBlock
    startNamedBlock blockId
    emitInstr $ INSTR_Phi ty [ (i, SV (VALUE_Ident (ID_Local l))) | (i,l) <- pred ]
