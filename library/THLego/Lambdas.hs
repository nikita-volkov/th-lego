module THLego.Lambdas
where

import THLego.Prelude
import THLego.Helpers
import Language.Haskell.TH
import qualified TemplateHaskell.Compat.V0208 as Compat


{-|
Simulates lambda-case without the need for extension.
-}
matcher :: [Match] -> Exp
matcher matches =
  LamE [VarP aName] (CaseE (VarE aName) matches)

{-|
Lambda expression, which extracts a product member by index.
-}
productGetter ::
  {-| Constructor name. -}
  Name ->
  {-| Total amount of members. -}
  Int ->
  {-| Index of the member. -}
  Int ->
  {-|
  Lambda expression of the following form:
  
  > product -> member
  -}
  Exp
productGetter conName numMembers index =
  LamE [pat] exp
  where
    varName =
      indexName index
    pat =
      ConP conName pats
      where
        pats =
          replicate index WildP <>
          pure (VarP varName) <>
          replicate (numMembers - index - 1) WildP
    exp =
      VarE varName

{-|
Lambda expression, which sets a product member by index.
-}
productSetter ::
  {-| Constructor name. -}
  Name ->
  {-| Total amount of members. -}
  Int ->
  {-| Index of the member. -}
  Int ->
  {-|
  Lambda expression of the following form:

  > product -> member -> product
  -}
  Exp
productSetter conName numMembers index =
  LamE [stateP, valP] exp
  where
    valName =
      mkName "x"
    stateP =
      ConP conName pats
      where
        pats =
          fmap (VarP . indexName) (enumFromTo 0 (pred numMembers))
    valP =
      VarP valName
    exp =
      foldl' AppE (ConE conName) (fmap VarE names)
      where
        names =
          fmap indexName (enumFromTo 0 (pred index)) <>
          pure valName <>
          fmap indexName (enumFromTo (succ index) (pred numMembers))

adtConstructorNarrower :: Name -> Int -> Exp
adtConstructorNarrower conName numMembers =
  matcher [positive, negative]
  where
    positive =
      Match (ConP conName (fmap VarP varNames)) (NormalB exp) []
      where
        varNames =
          fmap indexName (enumFromTo 0 (pred numMembers))
        exp =
          AppE (ConE 'Just) (Compat.tupE (fmap VarE varNames))
    negative =
      Match WildP (NormalB (ConE 'Nothing)) []

enumConstructorToBool :: Name -> Exp
enumConstructorToBool constructorName =
  matcher [positive, negative]
  where
    positive =
      Match (ConP constructorName []) (NormalB bodyExp) []
      where
        bodyExp =
          ConE 'True
    negative =
      Match WildP (NormalB bodyExp) []
      where
        bodyExp =
          ConE 'False

singleConstructorAdtToTuple :: Name -> Int -> Exp
singleConstructorAdtToTuple conName numMembers =
  LamE [pat] exp
  where
    varNames =
      fmap indexName (enumFromTo 0 (pred numMembers))
    pat =
      ConP conName (fmap VarP varNames)
    exp =
      Compat.tupE (fmap VarE varNames)

tupleToProduct :: Name -> Int -> Exp
tupleToProduct conName numMembers =
  LamE [pat] exp
  where
    varNames =
      fmap indexName (enumFromTo 0 (pred numMembers))
    pat =
      TupP (fmap VarP varNames)
    exp =
      multiAppE (ConE conName) (fmap VarE varNames)

namedFieldSetter :: Name -> Exp
namedFieldSetter fieldName =
  LamE [VarP aName, VarP bName] (RecUpdE (VarE aName) [(fieldName, VarE bName)])
