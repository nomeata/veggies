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

eq :: Nat -> Int -> Nat
eq Z     0 = S Z
eq Z     _ = Z
eq (S n) m = eq n (m - 1)
{-# NOINLINE eq #-}

main :: IO Nat
-- main = IO (\s -> (# s, Z #))
main = IO (\s ->
    let x = fac (S (S (S Z))) `eq` 6 in
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
