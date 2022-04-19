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
    , fieldPosition :: Int
    , traversalSpec :: TraversalSpec
    , traversalPosition :: Int
    }

occName :: Name -> String
occName (Name (OccName str) _) = str

keySpecName :: KeySpec -> Name
keySpecName KeySpec { conName, fieldPosition, traversalPosition } =
  mkName $ "Key" ++ occName conName ++ "F" ++ show fieldPosition ++ "T" ++ show traversalPosition

keySpecToTraversalHandler :: KeySpec -> Clause
keySpecToTraversalHandler spec@KeySpec { traversalSpec, fieldPosition, conFieldCount, conName } =
  let handlerName = mkName "handler"

      fieldName i = mkName $ "field" ++ show i
      targetFieldName = fieldName fieldPosition
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

  {-
keySpecsToAttachmentHandler :: [KeySpec] -> Maybe Clause
keySpecsToAttachmentHandler [] = Nothing
keySpecsToAttachmentHandler specs = Just $
  let KeySpec { conFieldCount, conName } = head specs

      fieldName i = mkName $ "field" ++ show i
      fieldNames = map fieldName [0..conFieldCount - 1]

      makeTuple fieldName keyName = TupE [Just (VarE fieldName), Just (ConE keyName)]
  in
  Clause
    [ConP conName (map VarP fieldNames)]
    (NormalB $ ConE conName `appEs` zipWith makeTuple fieldNames (map keySpecName specs))
    []
  -}

data TraversalSpec
  = Found
  | Traverse TraversalSpec
  | TraverseTupleN Int Int TraversalSpec
  | BitraverseLeft TraversalSpec
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

getTraversalSpecs :: Name -> Type -> [TraversalSpec]
getTraversalSpecs target = go
  where
  go type_ =
    let (typeFunc, typeArgs) = flattenAppT type_
    in
    if | length typeArgs == 0
       -> case typeFunc of
            VarT name | name == target -> pure Found
            _ -> []
       | length typeArgs == 1
       -> Traverse <$> go (head typeArgs)
       | length typeArgs >= 2
       -> let matchingIndices =
                [ (i, subspec)
                | (i, subspecs) <- zip [0..] (map go typeArgs)
                , subspec <- subspecs
                ]
          in
          case typeFunc of
            TupleT n -> do
              (matchingIndex, subspec) <- matchingIndices
              pure $ TraverseTupleN n matchingIndex subspec
            _ ->
              if | [(n, specLeft), (m, specRight)] <- matchingIndices
                 , n == length typeArgs - 2
                 , m == length typeArgs - 1
                 -> [BitraverseLeft specLeft, Traverse specRight]
                 | [(m, spec)] <- matchingIndices
                 , m == length typeArgs - 1
                 -> pure $ Traverse spec
                 | [(n, spec)] <- matchingIndices
                 , n == length typeArgs - 2
                 -> pure $ BitraverseLeft spec
                 | [] <- matchingIndices
                 -> []
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

  let enumerateKeySpecs :: ConstructorInfo -> [KeySpec]
      enumerateKeySpecs ConstructorInfo { constructorName, constructorFields } = do
        let fieldSpecs = map (getTraversalSpecs targetVarName) constructorFields
        (fieldPosition, specs) <- zip [0..] fieldSpecs
        (traversalPosition, spec) <- zip [0..] specs
        pure $ KeySpec
          { typeName = datatypeName
          , conName = constructorName
          , conFieldCount = length constructorFields
          , fieldPosition = fieldPosition
          , traversalSpec = spec
          , traversalPosition = traversalPosition
          }

  let allKeySpecs = map enumerateKeySpecs datatypeCons

  let keyDecl =
        let datatypeName = AppT (ConT ''Key) typeWithoutLastVar
            conNames = map (\spec -> NormalC (keySpecName spec) []) $ concat allKeySpecs
        in
        DataInstD [] Nothing datatypeName Nothing conNames []

  let traverseByKeyDecl =
        FunD 'traverseByKey (map keySpecToTraversalHandler $ concat allKeySpecs)

    {-
  let attachKeyDecl =
        FunD 'attachKey (mapMaybe keySpecsToAttachmentHandler allKeySpecs)
    -}

  --pure [InstanceD Nothing [] (ConT ''KeyBy `AppT` ConT targetName) [keyDecl, traverseByKeyDecl, attachKeyDecl]]
  pure [InstanceD Nothing [] (ConT ''KeyBy `AppT` typeWithoutLastVar) [keyDecl, traverseByKeyDecl]]
