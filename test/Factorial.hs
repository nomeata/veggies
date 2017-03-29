{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnboxedTuples #-}
-- module Factorial where

import GHC.Types (IO(..))

data Nat = Z | S Nat

pred Z = Z
pred (S a) = a
{-# NOINLINE pred #-}

plus Z     b = b
plus (S a) b = S (plus a b)
{-# NOINLINE plus #-}

mul Z     b = Z
mul (S a) b = plus b (mul a b)
{-# NOINLINE mul #-}

fac Z     = S Z
fac (S n) = S n `mul` fac n
{-# NOINLINE fac #-}

sub :: Nat -> Nat -> Nat
sub Z      _ = Z
sub (S n)  Z = n
sub (S n) (S m) = sub n m
{-# NOINLINE sub #-}

eq :: Nat -> Nat -> Nat
eq Z     Z = S Z
eq Z     _ = Z
eq (S n) Z = Z
eq (S n) (S m) = eq n m
{-# NOINLINE eq #-}

natToWord :: Nat -> Word
natToWord Z = 0
natToWord (S n) = 1 + natToWord n
{-# NOINLINE natToWord #-}

intToNat :: Word -> Nat
intToNat 0 = Z
intToNat n = S (intToNat (n-1))
{-# NOINLINE intToNat #-}

fac' :: Word -> Word
fac' = go
  where
    go 0     = 1
    go n     = n * fac' (n-1)

genFac :: (Word -> Word -> Word) -> Word -> Word
genFac foo = go
  where
    go 0     = 1
    go n     = foo n (fac' (n-1))
{-# NOINLINE genFac #-}

returnLambda :: Word -> (Word -> Word -> Word)
returnLambda n | fac' n == 0 = (*)
returnLambda n = \x y -> x * n * y
{-# NOINLINE returnLambda #-}


main :: IO Nat
-- main = IO (\s -> (# s, Z #))
main = IO (\s ->
    let n = 10 in
    let x = intToNat (genFac (returnLambda 1) n) `eq` fac (intToNat n) in x `seq`
    (# s, x #))

returnIO :: b -> IO b
returnIO b = IO (\s -> (# s , b #))
{-# NOINLINE returnIO #-}

traceIO :: a -> b -> IO b
traceIO a b = IO (\s -> a `seq` (# s , b #))
{-# NOINLINE traceIO #-}

traceTag ::  a -> b -> b
traceTag !a b = b
{-# NOINLINE traceTag #-}
