{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Datatypes where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified GHC.Prim
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Prim.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

type Empty_set = () -- empty inductive

coq_Empty_set_rect :: Empty_set -> a1
coq_Empty_set_rect _ =
  Prelude.error "absurd case"

coq_Empty_set_rec :: Empty_set -> a1
coq_Empty_set_rec =
  coq_Empty_set_rect

data Coq_unit =
   Coq_tt

unit_rect :: a1 -> Coq_unit -> a1
unit_rect f _ =
  f

unit_rec :: a1 -> Coq_unit -> a1
unit_rec =
  unit_rect

bool_rect :: a1 -> a1 -> Prelude.Bool -> a1
bool_rect f f0 b =
  case b of {
   False -> f;
   True -> f0}

bool_rec :: a1 -> a1 -> Prelude.Bool -> a1
bool_rec =
  bool_rect

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   False -> b2;
   True -> True}

orb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
orb b1 b2 =
  case b1 of {
   False -> False;
   True -> b2}

implb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
implb b1 b2 =
  case b1 of {
   False -> b2;
   True -> False}

xorb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
xorb b1 b2 =
  case b1 of {
   False ->
    case b2 of {
     False -> True;
     True -> False};
   True -> b2}

negb :: Prelude.Bool -> Prelude.Bool
negb b =
  case b of {
   False -> True;
   True -> False}

eq_true_rect :: a1 -> Prelude.Bool -> a1
eq_true_rect f _ =
  f

eq_true_rec :: a1 -> Prelude.Bool -> a1
eq_true_rec f b =
  eq_true_rect f b

eq_true_rec_r :: Prelude.Bool -> a1 -> a1
eq_true_rec_r _ h =
  h

eq_true_rect_r :: Prelude.Bool -> a1 -> a1
eq_true_rect_r _ h =
  h

data Coq_nat =
   O
 | S Coq_nat

nat_rect :: a1 -> (Coq_nat -> a1 -> a1) -> Coq_nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Coq_nat -> a1 -> a1) -> Coq_nat -> a1
nat_rec =
  nat_rect

option_rect :: (a1 -> a2) -> a2 -> (Prelude.Maybe a1) -> a2
option_rect f f0 o =
  case o of {
   Nothing x -> f x;
   Just -> f0}

option_rec :: (a1 -> a2) -> a2 -> (Prelude.Maybe a1) -> a2
option_rec =
  option_rect

option_map :: (a1 -> a2) -> (Prelude.Maybe a1) -> Prelude.Maybe a2
option_map f o =
  case o of {
   Nothing a -> Nothing (f a);
   Just -> Just}

data Coq_sum a b =
   Coq_inl a
 | Coq_inr b

sum_rect :: (a1 -> a3) -> (a2 -> a3) -> (Coq_sum a1 a2) -> a3
sum_rect f f0 s =
  case s of {
   Coq_inl x -> f x;
   Coq_inr x -> f0 x}

sum_rec :: (a1 -> a3) -> (a2 -> a3) -> (Coq_sum a1 a2) -> a3
sum_rec =
  sum_rect

prod_rect :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
prod_rect f p =
  case p of {
   (,) x x0 -> f x x0}

prod_rec :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
prod_rec =
  prod_rect

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

prod_uncurry :: (((,) a1 a2) -> a3) -> a1 -> a2 -> a3
prod_uncurry f x y =
  f ((,) x y)

prod_curry :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
prod_curry f p =
  case p of {
   (,) x y -> f x y}

list_rect :: a2 -> (a1 -> ([] a1) -> a2 -> a2) -> ([] a1) -> a2
list_rect f f0 l =
  case l of {
   [] -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> ([] a1) -> a2 -> a2) -> ([] a1) -> a2
list_rec =
  list_rect

length :: ([] a1) -> Coq_nat
length l =
  case l of {
   [] -> O;
   (:) _ l' -> S (length l')}

app :: ([] a1) -> ([] a1) -> [] a1
app l m =
  case l of {
   [] -> m;
   (:) a l1 -> (:) a (app l1 m)}

data Coq_comparison =
   Eq
 | Lt
 | Gt

comparison_rect :: a1 -> a1 -> a1 -> Coq_comparison -> a1
comparison_rect f f0 f1 c =
  case c of {
   Eq -> f;
   Lt -> f0;
   Gt -> f1}

comparison_rec :: a1 -> a1 -> a1 -> Coq_comparison -> a1
comparison_rec =
  comparison_rect

coq_CompOpp :: Coq_comparison -> Coq_comparison
coq_CompOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

coq_CompareSpecT_rect :: (() -> a1) -> (() -> a1) -> (() -> a1) ->
                         Coq_comparison -> CompareSpecT -> a1
coq_CompareSpecT_rect f f0 f1 _ c =
  case c of {
   CompEqT -> f __;
   CompLtT -> f0 __;
   CompGtT -> f1 __}

coq_CompareSpecT_rec :: (() -> a1) -> (() -> a1) -> (() -> a1) ->
                        Coq_comparison -> CompareSpecT -> a1
coq_CompareSpecT_rec =
  coq_CompareSpecT_rect

coq_CompareSpec2Type :: Coq_comparison -> CompareSpecT
coq_CompareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

coq_CompSpec2Type :: a1 -> a1 -> Coq_comparison -> CompSpecT a1
coq_CompSpec2Type _ _ c =
  coq_CompareSpec2Type c

identity_rect :: a1 -> a2 -> a1 -> a2
identity_rect _ f _ =
  f

identity_rec :: a1 -> a2 -> a1 -> a2
identity_rec a f y =
  identity_rect a f y

type ID = () -> Any -> Any

id :: a1 -> a1
id x =
  x

