{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnboxedTuples #-}
-- module Factorial where

data Nat = Z | S Nat deriving Show

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

returnLambda1 :: Word -> (Word -> Word -> Word)
returnLambda1 n x | fac' n == 0 = (x*)
returnLambda1 n x = \y -> x * n * y
{-# NOINLINE returnLambda1 #-}

returnLambda2 :: Word -> (Word -> Word -> Word)
returnLambda2 n | fac' n == 0 = (*)
returnLambda2 n = \x y -> x * n * y
{-# NOINLINE returnLambda2 #-}


main :: IO ()
-- main = IO (\s -> (# s, Z #))
main = do
    let n = 7
    let x = intToNat (genFac (returnLambda2 1) n)
    let y = fac (intToNat n)
    print (natToWord x)
    print (natToWord y)
