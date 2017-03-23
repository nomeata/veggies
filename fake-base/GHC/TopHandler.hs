{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
module GHC.TopHandler where

import GHC.Types

runMainIO :: IO a -> IO a
runMainIO (IO main) = IO (\s -> main s)
