module THLego.Instances
where

import THLego.Prelude
import THLego.Helpers
import Language.Haskell.TH
import qualified TemplateHaskell.Compat.V0208 as Compat
import qualified Data.Text as Text
import qualified THLego.Lambdas as Lambdas


-- * IsLabel
-------------------------

isLabel :: TyLit -> Type -> Exp -> Dec
isLabel label repType fromLabelExp =
  InstanceD Nothing [] headType [fromLabelDec]
  where
    headType =
      multiAppT (ConT ''IsLabel) [LitT label, repType]
    fromLabelDec =
      FunD 'fromLabel [Clause [] body []]
      where
        body =
          NormalB fromLabelExp

-- ** Constructor
-------------------------

newtypeConstructorIsLabel :: TyLit -> Type -> Name -> Type -> Dec
newtypeConstructorIsLabel label ownerType conName memberType =
  isLabel label repType fromLabelExp
  where
    repType =
      arrowChainT [memberType] ownerType
    fromLabelExp =
      ConE conName

sumConstructorIsLabel :: TyLit -> Type -> Name -> [Type] -> Dec
sumConstructorIsLabel label ownerType conName memberTypes =
  isLabel label repType fromLabelExp
  where
    repType =
      arrowChainT memberTypes ownerType
    fromLabelExp =
      ConE conName

enumConstructorIsLabel :: TyLit -> Type -> Name -> Dec
enumConstructorIsLabel label ownerType conName =
  isLabel label ownerType fromLabelExp
  where
    fromLabelExp =
      ConE conName

{-|
'IsLabel' instance which converts tuple to ADT.
-}
tupleAdtConstructorIsLabel :: TyLit -> Type -> Name -> [Type] -> Dec
tupleAdtConstructorIsLabel label ownerType conName memberTypes =
  isLabel label repType fromLabelExp
  where
    repType =
      arrowChainT [appliedTupleT memberTypes] ownerType
    fromLabelExp =
      Lambdas.tupleToProduct conName (length memberTypes)

-- ** Accessor
-------------------------

productAccessorIsLabel :: TyLit -> Type -> Type -> Name -> Int -> Int -> Dec
productAccessorIsLabel label ownerType projectionType conName numMembers offset =
  isLabel label repType fromLabelExp
  where
    repType =
      multiAppT ArrowT [ownerType, projectionType]
    fromLabelExp =
      Lambdas.productGetter conName numMembers offset

sumAccessorIsLabel :: TyLit -> Type -> Name -> [Type] -> Dec
sumAccessorIsLabel label ownerType conName memberTypes =
  isLabel label repType fromLabelExp
  where
    repType =
      multiAppT ArrowT [ownerType, projectionType]
      where
        projectionType =
          AppT (ConT ''Maybe) (appliedTupleT memberTypes)
    fromLabelExp =
      Lambdas.adtConstructorNarrower conName (length memberTypes)

enumAccessorIsLabel :: TyLit -> Type -> Name -> Dec
enumAccessorIsLabel label ownerType conName =
  isLabel label repType fromLabelExp
  where
    repType =
      multiAppT ArrowT [ownerType, projectionType]
      where
        projectionType =
          ConT ''Bool
    fromLabelExp =
      Lambdas.enumConstructorToBool conName


-- * 'HasField'
-------------------------

{-| The most general template for 'HasField'. -}
hasField :: TyLit -> Type -> Type -> [Clause] -> Dec
hasField fieldLabel ownerType projectionType getFieldFunClauses =
  InstanceD Nothing [] headType [getFieldDec]
  where
    headType =
      multiAppT (ConT ''HasField) [LitT fieldLabel, ownerType, projectionType]
    getFieldDec =
      FunD 'getField getFieldFunClauses

{-|
'HasField' instance which focuses on a variant of an enum
and projects it into 'Bool' signaling whether the value matches.

Generates code of the following pattern:

> instance HasField "fieldLabel" enumType Bool
-}
enumHasField ::
  {-| Field label. -}
  TyLit ->
  {-| Enum type. -}
  Type ->
  {-| Name of the constructor. -}
  Name ->
  Dec
enumHasField fieldLabel ownerType constructorName =
  hasField fieldLabel ownerType projectionType getFieldFunClauses
  where
    projectionType =
      ConT ''Bool
    getFieldFunClauses =
      [matching, unmatching]
      where
        matching =
          Clause [ConP constructorName []] (NormalB bodyExp) []
          where
            bodyExp =
              ConE 'True
        unmatching =
          Clause [WildP] (NormalB bodyExp) []
          where
            bodyExp =
              ConE 'False

{-|
Instance of 'HasField' for a constructor of a sum ADT,
projecting it into a 'Maybe' tuple of its members.

Generates code of the following pattern:

> instance HasField "fieldLabel" sumAdt (Maybe projectionType)

- When the amount of member types is 0, @projectionType@ is @()@.
- When the amount of member types is 1, it is that member type.
- Otherwise it is a tuple of those members.
-}
sumHasField ::
  {-| Field label. -}
  TyLit ->
  {-| The ADT type. -}
  Type ->
  {-| Name of the constructor. -}
  Name ->
  {-| Member types of that constructor. -}
  [Type] ->
  Dec
sumHasField fieldLabel ownerType constructorName memberTypes =
  hasField fieldLabel ownerType projectionType getFieldFunClauses
  where
    projectionType =
      AppT (ConT ''Maybe) (appliedTupleOrSingletonT memberTypes)
    getFieldFunClauses =
      [matching, unmatching]
      where
        varNames =
          enumFromTo 1 (length memberTypes) &
          fmap (mkName . showChar '_' . show)
        matching =
          Clause [ConP constructorName pats] (NormalB bodyExp) []
          where
            pats =
              fmap VarP varNames
            bodyExp =
              AppE (ConE 'Just) (appliedTupleE (fmap VarE varNames))
        unmatching =
          Clause [WildP] (NormalB bodyExp) []
          where
            bodyExp =
              ConE 'Nothing

{-|
Instance of 'HasField' for a member of a product type.
-}
productHasField ::
  {-| Field label. -}
  TyLit ->
  {-| Type of the product. -}
  Type ->
  {-| Type of the member we're focusing on. -}
  Type ->
  {-| Constructor name. -}
  Name ->
  {-| Total amount of members in the product. -}
  Int ->
  {-| Offset of the member we're focusing on. -}
  Int ->
  Dec
productHasField fieldLabel ownerType projectionType constructorName totalMemberTypes offset =
  hasField fieldLabel ownerType projectionType getFieldFunClauses
  where
    getFieldFunClauses =
      [Clause [ConP constructorName pats] (NormalB bodyExp) []]
      where
        pats =
          replicate offset WildP <>
          bool empty [VarP aName] (totalMemberTypes > 0) <>
          replicate (totalMemberTypes - offset - 1) WildP
        bodyExp =
          VarE aName
