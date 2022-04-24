{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Data.THKeys
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Data.Functor.Foldable
import Data.Functor.Foldable.TH

main :: IO ()
main = pure ()

data X b a
  = A a (Maybe a)
  | B a Int
  | C (Either a a, Either a b, [[[a]]])
  | D
  | E (a, a, a) (Int, a, Int, a, Int, a, Int)
  deriving (Show, Eq, Ord)

deriveKeyBy ''X

makeBaseFunctor ''Exp
deriveKeyBy ''ExpF
