{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Example where

import Data.THKeys
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

data X a
  = A a (Maybe a)
  | B a Int
  | C (Either a a, [[[a]]])
  | D
  | E (Int, Int, Int, a, Int, Int, Int)
  deriving (Show, Eq, Ord)

deriveKeyBy ''X
