module THLego.Instances
where

import THLego.Prelude
import THLego.Helpers
import Language.Haskell.TH
import qualified TemplateHaskell.Compat.V0208 as Compat
import qualified Data.Text as Text
import qualified THLego.Lambdas as Lambdas
import qualified THLego.Helpers as Helpers


-- * IsLabel
-------------------------

{-|
The most general template for 'IsLabel'.
-}
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

constructorIsLabel :: TyLit -> Type -> [Type] -> Exp -> Dec
constructorIsLabel label ownerType memberTypes fromLabelExp =
  InstanceD Nothing paramPreds headType [fromLabelDec]
  where
    paramPreds =
      memberTypes
        & Helpers.mapWithName (\ n t -> multiAppT EqualityT [VarT n, t])
    headType =
      multiAppT (ConT ''IsLabel) [LitT label, repType]
      where
        repType =
          arrowChainT memberVarTypes ownerType
          where
            memberVarTypes =
              Helpers.mapWithName (const . VarT) paramPreds
    fromLabelDec =
      FunD 'fromLabel [Clause [] (NormalB fromLabelExp) []]

newtypeConstructorIsLabel :: TyLit -> Type -> Name -> Type -> Dec
newtypeConstructorIsLabel label ownerType conName memberType =
  sumConstructorIsLabel label ownerType conName [memberType]

sumConstructorIsLabel :: TyLit -> Type -> Name -> [Type] -> Dec
sumConstructorIsLabel label ownerType conName memberTypes =
  constructorIsLabel label ownerType memberTypes (ConE conName)

enumConstructorIsLabel :: TyLit -> Type -> Name -> Dec
enumConstructorIsLabel label ownerType conName =
  sumConstructorIsLabel label ownerType conName []

{-|
'IsLabel' instance which converts tuple to ADT.
-}
tupleAdtConstructorIsLabel :: TyLit -> Type -> Name -> [Type] -> Dec
tupleAdtConstructorIsLabel label ownerType conName memberTypes =
  constructorIsLabel label ownerType [memberType] fromLabelExp
  where
    memberType =
      appliedTupleT memberTypes
    fromLabelExp =
      Lambdas.tupleToProduct conName (length memberTypes)

-- ** Accessor
-------------------------

{-|
Template of 'IsLabel' for instances mapping to accessor functions.
-}
accessorIsLabel :: TyLit -> Type -> Type -> Exp -> Dec
accessorIsLabel label ownerType projectionType fromLabelExp =
  InstanceD Nothing [memberPred] headType [fromLabelDec]
  where
    projVarType =
      VarT aName
    memberPred =
      multiAppT EqualityT [projVarType, projectionType]
    headType =
      multiAppT (ConT ''IsLabel) [LitT label, instanceType]
      where
        instanceType =
          multiAppT ArrowT [ownerType, projVarType]
    fromLabelDec =
      FunD 'fromLabel [Clause [] (NormalB fromLabelExp) []]

{-|
Instance of 'IsLabel' for a member of a product type.
-}
productAccessorIsLabel ::
  {-| Field label. -}
  TyLit ->
  {-| Type of the product. -}
  Type ->
  {-| Type of the member we\'re focusing on. -}
  Type ->
  {-| Constructor name. -}
  Name ->
  {-| Total amount of members in the product. -}
  Int ->
  {-| Offset of the member we're focusing on. -}
  Int ->
  {-| 'IsLabel' instance declaration. -}
  Dec
productAccessorIsLabel label ownerType projectionType conName numMembers offset =
  accessorIsLabel label ownerType projectionType fromLabelExp
  where
    fromLabelExp =
      Lambdas.productGetter conName numMembers offset

sumAccessorIsLabel :: TyLit -> Type -> Name -> [Type] -> Dec
sumAccessorIsLabel label ownerType conName memberTypes =
  accessorIsLabel label ownerType projectionType fromLabelExp
  where
    projectionType =
      AppT (ConT ''Maybe) (appliedTupleT memberTypes)
    fromLabelExp =
      Lambdas.adtConstructorNarrower conName (length memberTypes)

enumAccessorIsLabel :: TyLit -> Type -> Name -> Dec
enumAccessorIsLabel label ownerType conName =
  accessorIsLabel label ownerType projectionType fromLabelExp
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
  {-| 'HasField' instance declaration. -}
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
  {-| 'HasField' instance declaration. -}
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
  {-| Type of the member we\'re focusing on. -}
  Type ->
  {-| Constructor name. -}
  Name ->
  {-| Total amount of members in the product. -}
  Int ->
  {-| Offset of the member we're focusing on. -}
  Int ->
  {-| 'HasField' instance declaration. -}
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
