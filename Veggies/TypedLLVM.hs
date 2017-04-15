{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances#-}
{-# OPTIONS_GHC -fdefer-typed-holes  #-}
module Veggies.TypedLLVM where

import Data.Tagged
import GHC.TypeLits

import Ollvm_ast
import Veggies.GenMonad (G, LG)
import qualified Veggies.GenMonad as G
import qualified Veggies.ASTUtils as G
import qualified Veggies.Common as G

-- A copy of Coq_typ, for the sole purpose of avoiding the unpromoted Integer argument to TYPE_I

data LLVM_typ
    = I8 | I32 | I64
    | Pointer LLVM_typ
    | Function LLVM_typ [LLVM_typ]
    | Struct [LLVM_typ]
    | Array Nat LLVM_typ
    | Void
    | Named Symbol

type FunClosure = Struct [EnterFunP, HsFunP, I64, Env]
type FunClosureP = Pointer FunClosure

type HsFun = Function HsP [ HsP, EnvP ]
type HsFunP = Pointer HsFun

type Env = Array 0 HsP
type EnvP = Pointer Env

type Hs = Named "hs"
type EnterFun = Function HsP '[HsP]
type EnterFunP = Pointer EnterFun
type HsP = Pointer Hs
type Ptr = Pointer I8

-- General setup

type v ::: (t :: LLVM_typ) = Tagged t v

class GetType (t :: LLVM_typ) where
    typ :: Coq_typ
class GetTypes (t :: [LLVM_typ]) where
    types :: [Coq_typ]

typed :: forall t a. GetType t => a ::: t -> (Coq_typ, a)
typed (Tagged x) = (typ @t, x)

data Many what (tys :: [LLVM_typ]) where
    ManyNil  :: Many what '[]
    ManyCons :: (GetType ty, GetTypes tys) =>
        what ::: ty ->
        Many what tys ->
        Many what (ty : tys)

typeds :: Many what tys -> [(Coq_typ, what)]
typeds ManyNil = []
typeds (ManyCons a as) = typed a : typeds as

-- Boiler plate

instance GetType I8 where
    typ = TYPE_I 8
instance GetType I32 where
    typ = TYPE_I 32
instance GetType I64 where
    typ = TYPE_I 64
instance GetType Void where
    typ = TYPE_Void
instance GetType t => GetType (Pointer t) where
    typ = TYPE_Pointer (typ @t)
instance (KnownNat n, GetType t) => GetType (Array n t) where
    typ = TYPE_Array (natVal @n undefined) (typ @t)
instance (GetType ret, GetTypes args) => GetType (Function ret args) where
    typ = TYPE_Function (typ @ret) (types @args)
instance GetTypes tys => GetType (Struct tys) where
    typ = TYPE_Struct (types @tys)
instance KnownSymbol s => GetType (Named s) where
    typ = TYPE_Identified (ID_Global (Name (symbolVal @s undefined)))

instance GetTypes '[] where
    types = []
instance (GetType t, GetTypes tys) => GetTypes (t:tys) where
    types = (typ @t) : (types @tys)

-- Literals

mkI64 :: Integer -> Coq_value ::: I64
mkI64 i = Tagged (SV (VALUE_Integer i))

-- Idents and values

ident :: Coq_ident ::: t -> Coq_value ::: t
ident (Tagged v) = Tagged (G.ident v)

-- Emit commands

emitInstr :: Coq_instr ::: t -> LG (Coq_ident ::: t)
emitInstr (Tagged i) = Tagged <$> G.emitInstr i

emitVoidInstr :: Coq_instr ::: Void -> LG ()
emitVoidInstr (Tagged i) = G.emitVoidInstr i

-- Instructions

bitCast :: forall t1 t2. (GetType t1, GetType t2) =>
    Coq_ident ::: Pointer t1 -> Coq_instr ::: Pointer t2
bitCast (Tagged v) = Tagged $ G.bitCast (typ @(Pointer t1)) v (typ @(Pointer t2))

data GEP_Arg where
    Known   :: Nat -> GEP_Arg
    Unknown :: GEP_Arg

data GEP_Args (args :: [GEP_Arg])  where
    None     :: GEP_Args '[]
    AKnown   :: KnownNat n => proxy n -> GEP_Args xs -> GEP_Args (Known n : xs)
    AUnknown :: Coq_value ::: I64 -> GEP_Args xs -> GEP_Args (Unknown : xs)

class AllKnown (nats :: [Nat]) where
    allKnown :: GEP_Args (OnlyKnows nats)

type family OnlyKnows (nats :: [Nat])  = (r :: [GEP_Arg]) | r -> nats where
    OnlyKnows '[] = '[]
    OnlyKnows (n:ns) = Known n : OnlyKnows ns

instance AllKnown '[] where
    allKnown = None
instance (KnownNat n, AllKnown ns) => AllKnown (n:ns) where
    allKnown = AKnown undefined allKnown

type family GEP_Res (t :: LLVM_typ) (as :: [GEP_Arg]) :: LLVM_typ where
    GEP_Res t2 '[] = t2
    GEP_Res (Struct ts)  (Known n : as) = GEP_Res (Nth ts n) as
    GEP_Res (Pointer t2) (_ : as) = GEP_Res t2 as
    GEP_Res (Array _ t2) (_ : as) = GEP_Res t2 as

type family Nth (xs :: [a]) n :: a where
    Nth '[] 0 = TypeError (Text "empty list")
    Nth (x:xs) 0 = x
    Nth (x:xs) n = Nth xs (n-1)

getGEPArgs :: GEP_Args args -> [Coq_tvalue]
getGEPArgs None = []
getGEPArgs (AKnown p as) = (G.i32, SV (VALUE_Integer (natVal p))) : getGEPArgs as
    -- How do I pattern match on AKnown and bind n to pass it to NatVal without
    -- having a proxy field in AKnown
getGEPArgs (AUnknown v as) = typed v : getGEPArgs as

getElemPtr ::
    forall (t :: LLVM_typ) (args :: [GEP_Arg]).
    GetType t =>
    Coq_ident ::: Pointer t ->
    GEP_Args args ->
    Coq_instr ::: Pointer (GEP_Res (Pointer t) args)
getElemPtr p args
    = Tagged $ INSTR_Op (SV (OP_GetElementPtr (typ @t) (typed (ident p)) (getGEPArgs args)))


load :: forall t. GetType t => Coq_ident ::: Pointer t -> Coq_instr ::: t
load v = Tagged $ INSTR_Load False (typ @t) (typed (ident v)) Nothing

call :: forall ret_ty arg_tys.
    (GetType ret_ty, GetTypes arg_tys) =>
    Coq_ident ::: (Pointer (Function ret_ty arg_tys)) ->
    Many Coq_value arg_tys ->
    Coq_instr ::: ret_ty
call f args = Tagged $ INSTR_Call (typed f) (typeds args)

ibinop :: forall t. GetType t =>
    Coq_ibinop ->
    Coq_value ::: t ->
    Coq_value ::: t ->
    Coq_instr ::: t
ibinop op o1 o2 = Tagged $ INSTR_Op (SV (OP_IBinop op (typ @t) (unTagged o1) (unTagged o2)))

genMallocWords :: Coq_value ::: I64 -> LG (Coq_ident ::: Ptr)
genMallocWords (Tagged v) = Tagged <$> G.genMallocWords v

genMemcopy ::
    Coq_value ::: EnvP ->
    Coq_value ::: EnvP ->
    Coq_value ::: I64 ->
    Coq_value ::: I64 ->
    Coq_value ::: I64 ->
    LG ()
genMemcopy from to from_offset to_offset n
    = G.genMemcopy (unTagged from) (unTagged to) (unTagged from_offset) (unTagged to_offset) (unTagged n)

genFree :: Coq_value ::: Ptr -> LG ()
genFree ptr = G.genFree (unTagged ptr)
