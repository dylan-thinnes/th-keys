{-# LANGUAGE DeriveLift #-}
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

import LiftTH

class KeyBy f where
  data Key f :: *
  traverseByKey :: Applicative m => Key f -> (a -> m a) -> f a -> m (f a)

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

data KeySpec =
  KeySpec
    { typeName :: Name
    , conName :: Name
    , conFieldCount :: Int
    , position :: Int
    , traversalSpec :: TraversalSpec
    }

occName :: Name -> String
occName (Name (OccName str) _) = str

keySpecName :: KeySpec -> Name
keySpecName KeySpec { conName, position } =
  mkName $ "Key" ++ occName conName ++ show position

keySpecToTraversalHandler :: KeySpec -> Clause
keySpecToTraversalHandler spec@KeySpec { traversalSpec, position, conFieldCount, conName } =
  let handlerName = mkName "handler"

      fieldName i = mkName $ "field" ++ show i
      targetFieldName = fieldName position
      fieldNames = map fieldName [0..conFieldCount - 1]

      conPat = ConP conName (map VarP fieldNames)
      rewrapField = LamE [VarP targetFieldName] (ConE conName `appEs` map VarE fieldNames)
      traverseHandler = traversalSpecToCode (VarE handlerName) traversalSpec
      body =
        appEs (VarE 'fmap) [rewrapField, traverseHandler `AppE` VarE targetFieldName]
  in
  Clause
    [ConP (keySpecName spec) [], VarP handlerName, conPat]
    (NormalB body)
    []

data TraversalSpec
  = Found
  | Traverse TraversalSpec
  | TraverseTupleN Int Int TraversalSpec
  | BitraverseLeft TraversalSpec
  | Bitraverse TraversalSpec TraversalSpec
  deriving (Show, Eq, Ord, Lift)

traversalSpecToCode :: Exp -> TraversalSpec -> Exp
traversalSpecToCode f = go
  where
  go Found = f
  go (Traverse subspec) =
    AppE (VarE 'traverse) (go subspec)
  go (TraverseTupleN n matchingIndex subspec) =
    let elementName i = mkName $ "el" ++ show i
        elementNames = map elementName [0..n - 1]
        targetElementName = elementName matchingIndex

        tupPat = TupP (map VarP elementNames)
        rewrapElement = LamE [VarP targetElementName] (TupE $ map (Just . VarE) elementNames)
    in
    LamE [tupPat] $ VarE 'fmap `appEs` [rewrapElement, (go subspec `AppE` VarE targetElementName)]
  go (BitraverseLeft subspec) =
    AppE (AppE (VarE 'bitraverse) (go subspec)) (VarE 'pure)
  go (Bitraverse specL specR) =
    AppE (AppE (VarE 'bitraverse) (go specL)) (go specR)

mkTraversalSpec :: Name -> Type -> Maybe TraversalSpec
mkTraversalSpec target = go
  where
  go type_ =
    let (typeFunc, typeArgs) = flattenAppT type_
    in
    if | length typeArgs == 0
       -> case typeFunc of
            VarT name | name == target -> Just Found
            _ -> Nothing
       | length typeArgs == 1
       -> Traverse <$> go (head typeArgs)
       | length typeArgs >= 2
       -> let matchingIndices =
                [ (i, spec)
                | (i, Just spec) <- zip [0..] (map go typeArgs)
                ]
          in
          case typeFunc of
            TupleT n ->
              if | [(n, specLeft), (m, specRight)] <- matchingIndices
                 , n == length typeArgs - 2
                 , m == length typeArgs - 1
                 -> Just $ Bitraverse specLeft specRight
                 | [(matchingIndex, spec)] <- matchingIndices
                 -> Just $ TraverseTupleN n matchingIndex spec
                 | [] <- matchingIndices
                 -> Nothing
                 | otherwise
                 -> error "Tuple has >= 2 traversable type arguments that aren't in the last two positions"
            _ ->
              if | [(n, specLeft), (m, specRight)] <- matchingIndices
                 , n == length typeArgs - 2
                 , m == length typeArgs - 1
                 -> Just $ Bitraverse specLeft specRight
                 | [(m, spec)] <- matchingIndices
                 , m == length typeArgs - 1
                 -> Just $ Traverse spec
                 | [(n, spec)] <- matchingIndices
                 , n == length typeArgs - 2
                 -> Just $ BitraverseLeft spec
                 | [] <- matchingIndices
                 -> Nothing
                 | otherwise
                 -> error "Type has traversable type arguments that aren't in the last two positions"

deriveKeyBy :: Name -> Q [Dec]
deriveKeyBy targetName = do
  DatatypeInfo { datatypeName, datatypeCons, datatypeVars } <- reifyDatatype targetName
  let targetVar =
        if length datatypeVars == 0
          then error "Cannot derive a key for datatype with no type variables"
          else last datatypeVars
  let targetVarName =
        case targetVar of
          KindedTV name kind -> name
          PlainTV name -> name

  let enumerateKeySpecs :: ConstructorInfo -> [KeySpec]
      enumerateKeySpecs ConstructorInfo { constructorName, constructorFields } = do
        let specs = map (mkTraversalSpec targetVarName) constructorFields
        (position, Just spec) <- zip [0..] specs
        pure $ KeySpec
          { typeName = datatypeName
          , conName = constructorName
          , conFieldCount = length constructorFields
          , position = position
          , traversalSpec = spec
          }

  let allKeySpecs = map enumerateKeySpecs datatypeCons

  let keyDecl =
        let datatypeName = AppT (ConT ''Key) (ConT targetName)
            conNames = map (\spec -> NormalC (keySpecName spec) []) $ concat allKeySpecs
        in
        DataInstD [] Nothing datatypeName Nothing conNames []

  let traverseByKeyDecl =
        FunD 'traverseByKey (map keySpecToTraversalHandler $ concat allKeySpecs)

  pure [InstanceD Nothing [] (ConT ''KeyBy `AppT` ConT targetName) [keyDecl, traverseByKeyDecl]]
