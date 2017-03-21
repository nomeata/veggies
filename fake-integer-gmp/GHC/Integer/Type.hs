{-# LANGUAGE NoImplicitPrelude, MagicHash #-}

module GHC.Integer.Type where

import GHC.Prim

data Integer = S# Int#

mkInteger = S#
