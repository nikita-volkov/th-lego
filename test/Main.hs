module Main where

import Prelude hiding (assert)
import Test.QuickCheck.Instances
import Test.Tasty
import Test.Tasty.Runners
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Language.Haskell.TH.Syntax
import qualified Test.QuickCheck as QuickCheck
import qualified THLego.Instances as Instances
import qualified THLego.Helpers as Helpers


main =
  defaultMain $ 
  testGroup "Instances" [
    testCase "productMapperIsLabel" $ let
      dec =
        Instances.productMapperIsLabel
          (StrTyLit "start")
          (ConT ''CharPos)
          (ConT ''Loc)
          'Loc
          5
          3
      in
        case dec of
          InstanceD _ cxt headType _ ->
            do
              assertEqual ""
                [AppT
                  (AppT EqualityT (VarT (mkName "mapper")))
                  (AppT (AppT ArrowT (ConT ''Loc))
                    (ConT ''Loc))]
                cxt
              assertEqual ""
                (AppT
                  (AppT (ConT ''IsLabel) (LitT (StrTyLit "start")))
                  (AppT (AppT ArrowT (VarT (mkName "mapper")))
                    (AppT
                      (AppT ArrowT (ConT ''CharPos))
                      (ConT ''CharPos))))
                headType
          _ ->
            assertFailure (show dec)
    ,
    testGroup "sumMapperIsLabel" [
      testCase "No fields" $ let
        dec =
          Instances.sumMapperIsLabel
            (StrTyLit "arrow")
            (ConT ''Type)
            'ArrowT
            []
        in
          case dec of
            InstanceD _ decCxt decHeadType _ ->
              let
                mapperType =
                  TupleT 0
                predType =
                  EqualityT
                    `AppT` VarT (mkName "mapper")
                    `AppT` mapperType
                fnType =
                  ConT ''Type
                    & AppT (AppT ArrowT (ConT ''Type))
                    & AppT (AppT ArrowT (VarT (mkName "mapper")))
                headType =
                  ConT ''IsLabel
                    `AppT` LitT (StrTyLit "arrow")
                    `AppT` fnType
                in do
                  assertEqual "cxt" [predType] decCxt
                  assertEqual "headType" headType decHeadType
            _ ->
              assertFailure (show dec)
      ,
      testCase "1 field" $ let
        dec =
          Instances.sumMapperIsLabel
            (StrTyLit "var")
            (ConT ''Type)
            'VarT
            [ConT ''Name]
        in
          case dec of
            InstanceD _ decCxt decHeadType _ ->
              let
                mapperType =
                  ConT ''Name
                    & AppT (AppT ArrowT (ConT ''Name))
                predType =
                  EqualityT `AppT` VarT (mkName "mapper") `AppT` mapperType
                fnType =
                  ConT ''Type
                    & AppT (AppT ArrowT (ConT ''Type))
                    & AppT (AppT ArrowT (VarT (mkName "mapper")))
                headType =
                  ConT ''IsLabel
                    `AppT` LitT (StrTyLit "var")
                    `AppT` fnType
                in do
                  assertEqual "cxt" [predType] decCxt
                  assertEqual "headType" headType decHeadType
            _ ->
              assertFailure (show dec)
      ,
      testCase "Multiple fields" $ let
        dec =
          Instances.sumMapperIsLabel
            (StrTyLit "val")
            (ConT ''Dec)
            'ValD
            [ConT ''Pat, ConT ''Body, AppT ListT (ConT ''Dec)]
        in
          case dec of
            InstanceD _ decCxt decHeadType _ ->
              let
                tupleType =
                  TupleT 3
                    `AppT` (ConT ''Pat)
                    `AppT` (ConT ''Body)
                    `AppT` (AppT ListT (ConT ''Dec))
                mapperType =
                  AppT (AppT ArrowT (ConT ''Pat))
                    (AppT (AppT ArrowT (ConT ''Body))
                      (AppT (AppT ArrowT (AppT ListT (ConT ''Dec)))
                        tupleType))
                predType =
                  EqualityT `AppT` VarT (mkName "mapper") `AppT` mapperType
                fnType =
                  ConT ''Dec
                    & AppT (AppT ArrowT (ConT ''Dec))
                    & AppT (AppT ArrowT (VarT (mkName "mapper")))
                headType =
                  ConT ''IsLabel
                    `AppT` LitT (StrTyLit "val")
                    `AppT` fnType
                in do
                  assertEqual "cxt" [predType] decCxt
                  assertEqual "headType" headType decHeadType
            _ ->
              assertFailure (show dec)
      ]
    ]
