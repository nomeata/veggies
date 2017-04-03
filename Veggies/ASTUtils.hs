{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
module Veggies.ASTUtils where

import Data.List
import Data.Maybe
import Data.Bifunctor
import Control.Arrow ((&&&))
import Data.Either
import Control.Monad.State
import Control.Monad.Writer
import Data.Function

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

ident id = SV (VALUE_Ident id)

noop ty val = INSTR_Op (SV (OP_Conversion Bitcast ty val ty))

getElemPtr :: Coq_typ -> Coq_ident -> [Integer] -> Coq_instr
getElemPtr t v path
    = INSTR_Op (SV (OP_GetElementPtr t (t, ident v) [(TYPE_I 32, SV (VALUE_Integer n))| n <- path]))

mallocRetTy = TYPE_Pointer (TYPE_I 8)
mallocTy = TYPE_Function mallocRetTy [TYPE_I 64]
mallocIdent = ID_Global (Name "malloc")

mallocDecl :: TopLevelThing
mallocDecl = TLDecl $ Coq_mk_declaration
    (Name "malloc")
    mallocTy
    ([],[[]])
    Nothing
    Nothing
    Nothing
    Nothing
    []
    Nothing
    Nothing
    Nothing

exitRetTy = TYPE_Void
exitTy = TYPE_Function exitRetTy [TYPE_I 64]
exitIdent = ID_Global (Name "exit")

exitDecl :: TopLevelThing
exitDecl = TLDecl $ Coq_mk_declaration
    (Name "exit")
    exitTy
    ([],[[]])
    Nothing
    Nothing
    Nothing
    Nothing
    []
    Nothing
    Nothing
    Nothing

putsRetTy = TYPE_Void
putsTy = TYPE_Function putsRetTy [TYPE_Pointer (TYPE_I 8)]
putsIdent = ID_Global (Name "puts")

mkAliasedGlobal linkage name tmpName exportedTy realTy val =
    [ TLGlobal $ Coq_mk_global
        tmpName
        realTy
        True
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
    , TLAlias $ Coq_mk_alias
        name
        exportedTy
        (SV (OP_Conversion Bitcast (TYPE_Pointer realTy)
                                   (ident (ID_Global tmpName))
                                   (TYPE_Pointer exportedTy)))
        (Just linkage)
        Nothing
        Nothing
        Nothing
        False
    ]


mkExternalDecl :: String -> Coq_typ -> TopLevelThing
mkExternalDecl n (TYPE_Pointer (t@(TYPE_Function _ argsTy)))
    = TLDecl $ Coq_mk_declaration
        (Name n)
        t
        ([],[] <$ argsTy)
        Nothing
        Nothing
        Nothing
        Nothing
        []
        Nothing
        Nothing
        Nothing
mkExternalDecl n (TYPE_Pointer ty)
    = TLGlobal $ Coq_mk_global
       (Name n)
       ty
       False -- constant
       Nothing
       (Just LINKAGE_External)
       Nothing
       Nothing
       Nothing
       False
       Nothing
       False
       Nothing
       Nothing
mkExternalDecl n ty = error $ "mkExternalDecl " ++ show n

-- | This useful function adds top-level declarations for all referenced global
-- names that are not defined in this module. Such declarations are required by llvm.
addExternalDeclarations :: [TopLevelThing] -> [TopLevelThing]
addExternalDeclarations top_level_things = external_decls ++ top_level_things
  where
    defined_names = mapMaybe getDefinedNames top_level_things
    global_names  = nubBy ((==) `on` fst) $ concatMap glbNames top_level_things
    external_names = [ (n,ty) | (n,ty) <- global_names, n `notElem` defined_names ]
    external_decls = [ mkExternalDecl n ty | (n,ty) <- external_names ]


getGlobalId (TLAlias  a) = Just $ a_ident a
getGlobalId (TLGlobal g) = Just $ g_ident g
getGlobalId (TLTyDef  _) = Nothing
getGlobalId (TLDecl   d) = Just $ dc_name d
getGlobalId (TLDef    d) = Just $ dc_name (df_prototype d)

stringFromRawID (Name s) = Just s
stringFromRawID _        = Nothing

getDefinedNames tlt = getGlobalId tlt >>= stringFromRawID

class HasGlobalNames a where
    glbNames :: a -> [(String, Coq_typ)]

class HasGlobalNames' a where
    glbNames' :: Coq_typ -> a -> [(String, Coq_typ)]

instance HasGlobalNames' Coq_ident where
    glbNames' t (ID_Global (Name s)) = [(s,t)]
    glbNames' _ _                    = mzero

instance HasGlobalNames' e => HasGlobalNames (Coq_typ, e) where
    glbNames (t,v) = glbNames' t v

instance HasGlobalNames e => HasGlobalNames [e] where
    glbNames xs = foldMap glbNames xs

instance HasGlobalNames e => HasGlobalNames (Maybe e) where
    glbNames xs = foldMap glbNames xs
instance HasGlobalNames' e => HasGlobalNames' (Maybe e) where
    glbNames' t xs = foldMap (glbNames' t) xs

instance HasGlobalNames' e => HasGlobalNames' (Expr e) where
    glbNames' t (VALUE_Ident i)             = glbNames' t i
    glbNames' _ e = glbNames e

instance HasGlobalNames' e => HasGlobalNames (Expr e) where
    glbNames (VALUE_Ident i)             = error "glbNames' ident"
    glbNames (VALUE_Struct xs)           = mconcat [ glbNames' t o | (t,o) <- xs]
    glbNames (VALUE_Packed_struct xs)    = mconcat [ glbNames' t o | (t,o) <- xs]
    glbNames (VALUE_Array xs)            = mconcat [ glbNames' t o | (t,o) <- xs]
    glbNames (VALUE_Vector xs)           = mconcat [ glbNames' t o | (t,o) <- xs]
    glbNames (OP_IBinop _   t o1 o2)     = glbNames' t o1 <> glbNames' t o2
    glbNames (OP_ICmp   _   t o1 o2)     = glbNames' t o1 <> glbNames' t o2
    glbNames (OP_FBinop _ _ t o1 o2)     = glbNames' t o1 <> glbNames' t o2
    glbNames (OP_FCmp   _ t   o1 o2)     = glbNames' t o1 <> glbNames' t o2
    glbNames (OP_Conversion _ t o _)     = glbNames' t o
    glbNames (OP_GetElementPtr _ o p)    = glbNames o <> glbNames p
    glbNames (OP_ExtractElement o1 o2)   = glbNames o1 <> glbNames o2
    glbNames (OP_InsertElement o1 o2 o3) = glbNames o1 <> glbNames o2 <> glbNames o3
    glbNames (OP_ShuffleVector o1 o2 o3) = glbNames o1 <> glbNames o2 <> glbNames o3
    glbNames (OP_ExtractValue o _)       = glbNames o
    glbNames (OP_InsertValue o1 o2 _)    = glbNames o1 <> glbNames o2
    glbNames (OP_Select o1 o2 o3)        = glbNames o1 <> glbNames o2 <> glbNames o3
    glbNames _ = mzero


instance HasGlobalNames' Coq_value where
    glbNames' t (SV e) = glbNames' t e
instance HasGlobalNames Coq_value where
    glbNames (SV e) = glbNames e

instance HasGlobalNames Coq_alias where
    glbNames a = glbNames' (a_typ a) (a_value a)

instance HasGlobalNames Coq_global where
    glbNames g = glbNames' (g_typ g) (g_value g)

instance HasGlobalNames Coq_instr where
    glbNames (INSTR_Op v)            = glbNames v
    glbNames (INSTR_Call (t,f) ops)  = glbNames' funTy f <> foldMap glbNames ops
        where funTy | TYPE_Function {} <- t = TYPE_Pointer t
                    | otherwise             = TYPE_Pointer (TYPE_Function t (map fst ops))
    glbNames (INSTR_Phi t preds)     = foldMap (glbNames' t . fst) preds
    glbNames (INSTR_Alloca _ mbn _)  = glbNames mbn
    glbNames (INSTR_Load _ _ o _)    = glbNames o
    glbNames (INSTR_Store _ o1 o2 _) = glbNames o1 <> glbNames o2
    glbNames _                       = mzero

instance HasGlobalNames Coq_terminator where
    glbNames (TERM_Ret o)            = glbNames o
    glbNames (TERM_Br cond l1 l2)    = glbNames cond <> glbNames l1 <> glbNames l2
    glbNames (TERM_Br_1 l)           = glbNames l
    glbNames (TERM_Switch s d ls)
        = glbNames s <> glbNames d <> mconcat [ glbNames a <> glbNames b | (a,b) <- ls ]
    glbNames (TERM_IndirectBr s ls)  = glbNames s <> foldMap glbNames ls
    glbNames (TERM_Resume v)         = glbNames v
    glbNames (TERM_Invoke f as o1 o2)
        = glbNames f <> foldMap glbNames as <> glbNames o1 <> glbNames o2
    glbNames _                       = mzero

instance HasGlobalNames Coq_block where
    glbNames b = glbNames (map snd (blk_instrs b)) <> glbNames (blk_term b)

instance HasGlobalNames Coq_definition where
    glbNames = glbNames . df_instrs

instance HasGlobalNames TopLevelThing where
    glbNames (TLAlias a)  = glbNames a
    glbNames (TLGlobal g) = glbNames g
    glbNames (TLTyDef _)  = []
    glbNames (TLDecl _)   = []
    glbNames (TLDef d)    = glbNames d

