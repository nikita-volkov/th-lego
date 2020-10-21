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
          InstanceD _ pred cxt _ ->
            do
              assertEqual ""
                [AppT
                  (AppT EqualityT (VarT (mkName "mapper")))
                  (AppT (AppT ArrowT (ConT ''Loc))
                    (ConT ''Loc))]
                pred
              assertEqual ""
                (AppT
                  (AppT (ConT ''IsLabel) (LitT (StrTyLit "start")))
                  (AppT (AppT ArrowT (VarT (mkName "mapper")))
                    (AppT
                      (AppT ArrowT (ConT ''CharPos))
                      (ConT ''CharPos))))
                cxt
          _ ->
            assertFailure (show dec)
    ]
