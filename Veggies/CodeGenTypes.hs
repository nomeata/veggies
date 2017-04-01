{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
module Veggies.CodeGenTypes where

import Data.List
import Data.Maybe
import Data.Bifunctor
import Control.Arrow ((&&&))
import Data.Either
import Control.Monad.State
import Control.Monad.Writer

import Var
import Id
import MkId
import Module
import Type
import TyCon
import DataCon
import Name
import OccName
import CoreSyn
import CoreUtils
import CoreFVs
import Encoding
import Outputable
import PrelNames
import TysWiredIn
import TysPrim
import BasicTypes
import VarSet
import VarEnv
import Literal

import Ollvm_ast

import Debug.Trace
import GHC.Stack
import Veggies.ASTUtils



mkClosureTy :: Coq_typ
mkClosureTy = TYPE_Struct [ enterFunTyP ]

hsTy :: Coq_typ
hsTy = TYPE_Identified (ID_Global (Name "hs"))

hsTyP :: Coq_typ
hsTyP = TYPE_Pointer (TYPE_Identified (ID_Global (Name "hs")))

-- An explicit, global function to call
hsFunTy :: Integer -> Integer -> Coq_typ
hsFunTy n m = TYPE_Function hsTyP (envTyP m : replicate (fromIntegral n) hsTyP)

-- Entering a closure
enterFunTy  = TYPE_Function hsTyP [hsTyP]
enterFunTyP = TYPE_Pointer enterFunTy

mkThunkTy :: Integer -> Coq_typ
mkThunkTy n = TYPE_Struct [ enterFunTyP, envTy n' ]
  where n' = max 1 n

-- space for at least one element!
mkThunkArray :: [Coq_tvalue] -> Coq_value
mkThunkArray [] = SV (VALUE_Array [(hsTyP, SV VALUE_Null)])
mkThunkArray xs = SV (VALUE_Array xs)

thunkTy :: Coq_typ
thunkTy = TYPE_Identified (ID_Global (Name "thunk"))

thunkTyP :: Coq_typ
thunkTyP = TYPE_Pointer thunkTy

tagTy = TYPE_I 64
tagTyP = TYPE_Pointer tagTy

arityTy = TYPE_I 64
arityTyP = TYPE_Pointer arityTy

mkDataConTy n = TYPE_Struct [ enterFunTyP, tagTy, TYPE_Array n hsTyP ]
mkDataConTyP n = TYPE_Pointer (mkDataConTy n)

envTy m = TYPE_Array m hsTyP
envTyP m = TYPE_Pointer (envTy m)

mkFunClosureTy n m =
    TYPE_Struct [ enterFunTyP
                , TYPE_Pointer (hsFunTy n m)
                , arityTy
                , envTy m
                ]
mkFunClosureTyP n m = TYPE_Pointer (mkFunClosureTy n m)

dataConTy = TYPE_Identified (ID_Global (Name "dc"))
dataConTyP = TYPE_Pointer dataConTy

mkIntBoxTy = TYPE_Struct [ enterFunTyP, TYPE_I 64 ]
intBoxTy = TYPE_Identified (ID_Global (Name "int"))
intBoxTyP = TYPE_Pointer intBoxTy

badArityTy = TYPE_Function hsTyP []
badArityIdent = ID_Global (Name "rts_badArity")

badArityDecl :: TopLevelThing
badArityDecl = TLDecl $ Coq_mk_declaration
    (Name "rts_badArity")
    badArityTy
    ([],[])
    Nothing
    Nothing
    Nothing
    Nothing
    []
    Nothing
    Nothing
    Nothing


dummyBody :: [Coq_block]
dummyBody = [ Coq_mk_block (Anon 0)
                [] (TERM_Ret (hsTyP, SV VALUE_Null))
                (IVoid 1)
            ]

mkHsFunDefinition :: Coq_linkage -> Coq_raw_id -> [Coq_raw_id] -> Integer -> [Coq_block] -> Coq_definition
mkHsFunDefinition linkage n param_names env_arity blocks = Coq_mk_definition
    (mkHsFunDeclaration linkage n param_names env_arity)
    (closRawId :  param_names)
    blocks

mkHsFunDeclaration :: Coq_linkage -> Coq_raw_id -> [Coq_raw_id] -> Integer -> Coq_declaration
mkHsFunDeclaration linkage n param_names env_arity = Coq_mk_declaration
    n
    (hsFunTy (fromIntegral (length param_names)) env_arity)
    ([],([] : map (const []) param_names))
    (Just linkage)
    Nothing
    Nothing
    Nothing
    []
    Nothing
    Nothing
    Nothing

mkEnterFunDefinition :: Coq_linkage -> Coq_global_id -> [Coq_block] -> Coq_definition
mkEnterFunDefinition linkage n blocks = Coq_mk_definition
    (mkEnterFunDeclaration linkage n)
    [closRawId]
    blocks

mkEnterFunDeclaration :: Coq_linkage -> Coq_global_id -> Coq_declaration
mkEnterFunDeclaration linkage n = Coq_mk_declaration
    n
    enterFunTy
    ([],[[]])
    (Just linkage)
    Nothing
    Nothing
    Nothing
    []
    Nothing
    Nothing
    Nothing


codeNameStr :: Name -> String
codeNameStr n | isExternalName n =
    intercalate "_" $ map zEncodeString
        [ moduleNameString (moduleName (nameModule n))
        , occNameString (nameOccName n)
        ]
codeNameStr n  =
    intercalate "_" $ map zEncodeString
    [ occNameString (nameOccName n)
    , show (nameUnique n)
    ]


closIdent :: Coq_ident
closIdent = ID_Local closRawId
closRawId :: Coq_raw_id
closRawId = Name "clos"

defaultTyDecls :: [TopLevelThing]
defaultTyDecls =
    [ TLTyDef $ Coq_mk_type_decl (Name "hs")    mkClosureTy
    , TLTyDef $ Coq_mk_type_decl (Name "thunk") (mkThunkTy 0)
    , TLTyDef $ Coq_mk_type_decl (Name "dc")    (mkDataConTy 0)
    , TLTyDef $ Coq_mk_type_decl (Name "int")   mkIntBoxTy
    ]

returnArgIdent :: Coq_ident
returnArgIdent = ID_Global (Name "rts_returnArg")

