{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
module Main where
import GHC.Types

data Unit = Unit


return :: a -> IO a
return x = IO (\s -> (# s, x #))

main :: IO ()
main = return ()
