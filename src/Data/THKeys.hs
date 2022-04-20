{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
module Data.THKeys where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Datatype

import Data.Bitraversable
import Data.Maybe

import Data.Functor.Identity
import Data.Functor.Const
import Data.Monoid (First (..))

import Control.Monad.State (State (..), get, modify, evalState)

import LiftTH

class KeyBy f where
  data Key f :: *
  traverseByKey :: Applicative m => Key f -> (a -> m a) -> f a -> m (f a)
  attachKey :: f a -> f (Key f, a)

setByKey :: KeyBy f => Key f -> (a -> a) -> f a -> f a
setByKey key handler = runIdentity . traverseByKey key (Identity . handler)

getByKey :: KeyBy f => Key f -> f a -> Maybe a
getByKey key = getFirst . getConst . traverseByKey key (Const . First . Just)

appEs :: Exp -> [Exp] -> Exp
appEs = foldl AppE

flattenAppT :: Type -> (Type, [Type])
flattenAppT type_ = go type_ []
  where
    go (AppT f arg) args = go f (arg:args)
    go func args = (func, args)

data KeySpecG extra =
  KeySpec
    { typeName :: Name
    , conName :: Name
    , conFieldCount :: Int
    , x :: extra
    }
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

type KeySpec = KeySpecG FieldedTargetSpecs
type FieldedTargetSpecs = [(Int, TargetSpecs)]

conInfoToKeySpecMulti :: Name -> Name -> ConstructorInfo -> KeySpec
conInfoToKeySpecMulti typeName targetVarName ConstructorInfo { constructorName, constructorFields } =
  KeySpec
    { typeName
    , conName = constructorName
    , conFieldCount = length constructorFields
    , x = mapMaybe sequence $ zip [0..] $ map (getTargetSpecs targetVarName) constructorFields
    }

divideFieldedTargetSpecs :: FieldedTargetSpecs -> [FieldedTargetSpec]
divideFieldedTargetSpecs fieldSpecs = do
  (fieldPosition, specs) <- fieldSpecs
  (targetPosition, spec) <- divideSpecsWithIdx specs
  pure $ FieldedTargetSpec
    { fieldPosition = fieldPosition
    , targetSpec = spec
    , targetPosition = targetPosition
    }

type KeySpecSingle = KeySpecG FieldedTargetSpec

data FieldedTargetSpec =
  FieldedTargetSpec
    { fieldPosition :: Int
    , targetSpec :: TargetSpec
    , targetPosition :: Int
    }

occName :: Name -> String
occName (Name (OccName str) _) = str

keySpecSingleName :: KeySpecSingle -> Name
keySpecSingleName KeySpec { conName, x = FieldedTargetSpec { fieldPosition, targetPosition } } =
  keyName conName fieldPosition targetPosition

keyName :: Name -> Int -> Int -> Name
keyName conName fieldPosition targetPosition =
  mkName $ "Key" ++ occName conName ++ "F" ++ show fieldPosition ++ "T" ++ show targetPosition

keySpecToTraversalHandler :: KeySpecSingle -> Clause
keySpecToTraversalHandler spec@KeySpec { conFieldCount, conName, x = FieldedTargetSpec { targetSpec, fieldPosition } } =
  let handlerName = mkName "handler"

      fieldName i = mkName $ "field" ++ show i
      targetFieldName = fieldName fieldPosition
      fieldNames = map fieldName [0..conFieldCount - 1]

      conPat = ConP conName (map VarP fieldNames)
      rewrapField = LamE [VarP targetFieldName] (ConE conName `appEs` map VarE fieldNames)
      traverseHandler = targetSpecToTraversal (VarE handlerName) targetSpec
      body =
        appEs (VarE 'fmap) [rewrapField, traverseHandler `AppE` VarE targetFieldName]
  in
  Clause
    [ConP (keySpecSingleName spec) [], VarP handlerName, conPat]
    (NormalB body)
    []

keySpecsToAttachmentHandler :: [KeySpecSingle] -> Maybe Clause
keySpecsToAttachmentHandler [] = Nothing
keySpecsToAttachmentHandler specs = Just $
  let KeySpec { conFieldCount, conName } = head specs

      fieldName i = mkName $ "field" ++ show i
      fieldNames = map fieldName [0..conFieldCount - 1]

      makeTuple fieldName keyName = TupE [Just (VarE fieldName), Just (ConE keyName)]
  in
  Clause
    [ConP conName (map VarP fieldNames)]
    (NormalB $ ConE conName `appEs` zipWith makeTuple fieldNames (map keySpecSingleName specs))
    []

data TargetSpecsF a
  = Founds a
  | Nests (TargetSpecsF a)
  | NestTupleNs Int [(Int, TargetSpecsF a)]
  | BiLefts (TargetSpecsF a)
  | BiBoths (TargetSpecsF a) (TargetSpecsF a)
  deriving (Show, Eq, Ord, Lift, Functor, Foldable, Traversable)

type TargetSpecs = TargetSpecsF Int

targetSpecsToAttachKey :: Name -> Int -> TargetSpec -> Exp
targetSpecsToAttachKey = undefined

divideSpecsWithIdx :: TargetSpecs -> [(Int, TargetSpec)]
divideSpecsWithIdx = go
  where
    go :: TargetSpecs -> [(Int, TargetSpec)]
    go (Founds a) = pure (a, Found)
    go (Nests subspecs) = (fmap . fmap) Nest (go subspecs)
    go (NestTupleNs n idxedSubspecs) = do
      (idx, subspecs) <- idxedSubspecs
      subspec <- go subspecs
      pure $ NestTupleN n idx <$> subspec
    go (BiLefts subspecs) = (fmap . fmap) BiLeft (go subspecs)
    go (BiBoths lspecs rspecs) =
      (fmap . fmap) BiLeft (go lspecs) ++ (fmap . fmap) Nest (go rspecs)


data TargetSpec
  = Found
  | Nest TargetSpec
  | NestTupleN Int Int TargetSpec
  | BiLeft TargetSpec
  deriving (Show, Eq, Ord, Lift)

targetSpecToTraversal :: Exp -> TargetSpec -> Exp
targetSpecToTraversal f = go
  where
  go Found = f
  go (Nest subspec) =
    AppE (VarE 'traverse) (go subspec)
  go (NestTupleN n matchingIndex subspec) =
    let elementName i = mkName $ "el" ++ show i
        elementNames = map elementName [0..n - 1]
        targetElementName = elementName matchingIndex

        tupPat = TupP (map VarP elementNames)
        rewrapElement = LamE [VarP targetElementName] (TupE $ map (Just . VarE) elementNames)
    in
    LamE [tupPat] $ VarE 'fmap `appEs` [rewrapElement, (go subspec `AppE` VarE targetElementName)]
  go (BiLeft subspec) =
    AppE (AppE (VarE 'bitraverse) (go subspec)) (VarE 'pure)

getTargetSpecs :: Name -> Type -> Maybe TargetSpecs
getTargetSpecs target type_ = flip evalState 0 . traverse withIdx <$> go type_
  where
  withIdx _ = do
    i <- get
    modify succ
    pure i

  go type_ =
    let (typeFunc, typeArgs) = flattenAppT type_
    in
    if | length typeArgs == 0
       -> case typeFunc of
            VarT name | name == target -> pure $ Founds ()
            _ -> Nothing
       | length typeArgs == 1
       -> Nests <$> go (head typeArgs)
       | length typeArgs >= 2
       -> let matchingIndices =
                [ (i, subspec)
                | (i, Just subspec) <- zip [0..] (map go typeArgs)
                ]
          in
          case typeFunc of
            TupleT n ->
              pure $ NestTupleNs n matchingIndices
            _ ->
              if | [(n, specLeft), (m, specRight)] <- matchingIndices
                 , n == length typeArgs - 2
                 , m == length typeArgs - 1
                 -> pure $ BiBoths specLeft specRight
                 | [(m, spec)] <- matchingIndices
                 , m == length typeArgs - 1
                 -> pure $ Nests spec
                 | [(n, spec)] <- matchingIndices
                 , n == length typeArgs - 2
                 -> pure $ BiLefts spec
                 | [] <- matchingIndices
                 -> Nothing
                 | otherwise
                 -> error "Type has traversable type arguments that aren't in the last two positions"

deriveKeyBy :: Name -> Q [Dec]
deriveKeyBy targetName = do
  DatatypeInfo { datatypeName, datatypeCons, datatypeVars } <- reifyDatatype targetName
  let (targetVar, unusedVars) =
        if length datatypeVars == 0
          then error "Cannot derive a key for datatype with no type variables"
          else (last datatypeVars, init datatypeVars)

  let tyVarName tyvar =
        case tyvar of
          KindedTV name kind -> name
          PlainTV name -> name
  let targetVarName = tyVarName targetVar
  let typeWithoutLastVar = foldl AppT (ConT targetName) (VarT . tyVarName <$> unusedVars)

  let enumerateKeySpecs :: ConstructorInfo -> [KeySpecSingle]
      enumerateKeySpecs =
        traverse divideFieldedTargetSpecs . conInfoToKeySpecMulti targetName targetVarName

  let allKeySpecs = map enumerateKeySpecs datatypeCons

  let keyDecl =
        let datatypeName = AppT (ConT ''Key) typeWithoutLastVar
            conNames = map (\spec -> NormalC (keySpecSingleName spec) []) $ concat allKeySpecs
        in
        DataInstD [] Nothing datatypeName Nothing conNames []

  let traverseByKeyDecl =
        FunD 'traverseByKey (map keySpecToTraversalHandler $ concat allKeySpecs)

  let attachKeyDecl =
        FunD 'attachKey (mapMaybe keySpecsToAttachmentHandler allKeySpecs)

  --pure [InstanceD Nothing [] (ConT ''KeyBy `AppT` typeWithoutLastVar) [keyDecl, traverseByKeyDecl, attachKeyDecl]]
  pure [InstanceD Nothing [] (ConT ''KeyBy `AppT` typeWithoutLastVar) [keyDecl, traverseByKeyDecl]]
