module THToolkit.Instances
where

import THToolkit.Prelude
import THToolkit.Helpers
import Language.Haskell.TH
import qualified TemplateHaskell.Compat.V0208 as Compat
import qualified Data.Text as Text
import qualified THToolkit.Lambdas as Lambdas


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

sumConstructorIsLabel :: TyLit -> Name -> Name -> [Type] -> Dec
sumConstructorIsLabel label typeName conName memberTypes =
  isLabel label repType fromLabelExp
  where
    repType =
      foldr (\ a b -> AppT (AppT ArrowT a) b) (ConT typeName) memberTypes
    fromLabelExp =
      ConE conName

enumConstructorIsLabel :: TyLit -> Name -> Name -> Dec
enumConstructorIsLabel label typeName conName =
  isLabel label repType fromLabelExp
  where
    repType =
      ConT typeName
    fromLabelExp =
      ConE conName

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
Field which projects enum values into bools.
-}
boolEnumHasField :: TyLit -> Type -> Name -> Dec
boolEnumHasField fieldLabel ownerType constructorName =
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

sumHasField :: TyLit -> Type -> Name -> [Type] -> Dec
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

productHasField :: TyLit -> Type -> Type -> Name -> Int -> Int -> Dec
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
