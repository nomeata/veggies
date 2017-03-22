{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}
module Factorial where

data Nat = Z | S Nat

pred Z = Z
pred (S a) = a

plus Z     b = b
plus (S a) b = S (plus a b)

mul Z     b = Z
mul (S a) b = plus b (mul a b)

fac Z     = S Z
fac (S n) = n `mul` fac n
