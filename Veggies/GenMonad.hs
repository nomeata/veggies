{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
module Veggies.GenMonad where

import Data.List
import Data.Maybe
import Data.Bifunctor
import Control.Arrow ((&&&))
import Data.Either
import Control.Monad.State
import Control.Monad.Writer

import Var (Var)

import Ollvm_ast

import Debug.Trace
import GHC.Stack


data TopLevelThing
    = TLAlias  Coq_alias
    | TLGlobal Coq_global
    | TLTyDef  Coq_type_decl
    | TLDecl   Coq_declaration
    | TLDef    Coq_definition

mkCoqModul :: String -> [TopLevelThing] -> Coq_modul
mkCoqModul name top_level_things
    = Coq_mk_modul name
        (TLE_Target "x86_64-pc-linux")
        (TLE_Source_filename "no data layout here")
        (map ("",) [ x | TLGlobal x <- top_level_things ])
        (map ("",) [ x | TLTyDef x  <- top_level_things ])
        (map ("",) [ x | TLDecl x   <- top_level_things ])
        (map ("",) [ x | TLDef x    <- top_level_things ])
        (map ("",) [ x | TLAlias x  <- top_level_things ])

-- Generating top-level definitions
type G = WriterT [TopLevelThing] (WriterT [Var] (State Integer))
-- Also generting instructions
type PartialBlock = (Coq_block_id, [(Coq_instr_id, Coq_instr)])
type LG = StateT (Maybe PartialBlock) (WriterT [Coq_block] (StateT Integer G))

runG :: G () -> ([TopLevelThing], [Var])
runG g = evalState (runWriterT (execWriterT g)) 0

runLG :: LG () -> G ([Coq_block])
runLG lg = evalStateT (execWriterT (evalStateT lg' Nothing)) 0
  where
    lg' = do
        firstBlockId <- freshLocal
        startNamedBlock firstBlockId
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
freshGlobal = fmap Anon $ lift $ lift $ state (id &&& (+1))

freshLocal :: LG Coq_local_id
freshLocal = fmap Anon $ lift $ state (id &&& (+1))

noteExternalVar :: Var -> G ()
noteExternalVar v = lift $ tell [v]

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

emitNamedInstr :: Coq_local_id -> Coq_instr -> LG ()
emitNamedInstr instrId instr = do
    blockId <- freshLocal
    modify $ \s ->
        case s of
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
namedPhiBlock ty blockId pred = do
    ensureNoBlock
    startNamedBlock blockId
    emitInstr $ INSTR_Phi ty [ (i, SV (VALUE_Ident (ID_Local l))) | (i,l) <- pred ]

ident id = SV (VALUE_Ident id)

noop ty val = INSTR_Op (SV (OP_Conversion Bitcast ty val ty))

