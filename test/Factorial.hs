{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnboxedTuples #-}
-- module Factorial where

import GHC.Types (IO(..))
import GHC.Prim (seq)

data Nat = Z | S Nat

pred Z = Z
pred (S a) = a

plus Z     b = b
plus (S a) b = S (plus a b)

mul Z     b = Z
mul (S a) b = plus b (mul a b)

fac Z     = S Z
fac (S n) = n `mul` fac n

foo Z = fac (S (S Z))
foo (S n) = n

main :: IO Nat
-- main = IO (\s -> (# s, Z #))
main = traceIO (foo Z) Z

traceIO :: a -> b -> IO b
traceIO a b = IO (\s -> a `seq` (# s , b #))
{-# NOINLINE traceIO #-}

traceTag ::  a -> b -> b
traceTag !a b = b
{-# NOINLINE traceTag #-}
