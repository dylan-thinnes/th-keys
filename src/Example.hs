{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Example where

import Data.THKeys
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

data X b a
  = A a (Maybe a)
  | B a Int
  | C (Either a a, Either a b, [[[a]]])
  | D
  | E (a, a, a) (Int, a, Int, a, Int, a, Int)
  deriving (Show, Eq, Ord)

deriveKeyBy ''X
