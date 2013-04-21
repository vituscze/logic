-- | Test suite.
module Main (main) where

import Test.HUnit ((@=?))
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)

import Test.Arbitrary ()
import Test.Concrete
import Test.Properties

main :: IO ()
main = defaultMain tests

tests :: [Test]
tests =
    [ testGroup "term"
        [ testProperty "functor law" fmapTermFunctorProp
        , testProperty "fold id"     foldTermId
        , testProperty "free vars"   freeVarsTVarsInTerm
        ]
    , testGroup "formula"
        [ testProperty "functor law"  fmapFormulaFunctorProp
        , testProperty "fold id"      foldFormulaId
        , testProperty "cnf"          cnfProp
        , testProperty "cnf idemp"    cnfIdempotent
        , testProperty "prenex"       prenexProp
        , testProperty "prenex idemp" prenexIdempotent
        , testProperty "skolem nf"    skolemizeProp
        ]
    , testGroup "concrete data"
        [ testCase "freevar term 1" (freeVarsT1  @=? freeVarsR1)
        , testCase "freevar term 2" (freeVarsT2  @=? freeVarsR2)
        , testCase "freevar term 3" (freeVarsT3  @=? freeVarsR3)
        , testCase "show term 1"    (showT1      @=? showR1)
        , testCase "show term 2"    (showT2      @=? showR2)
        , testCase "show term 3"    (showT3      @=? showR3)
        , testCase "freevar fl 1"   (freeVarsFT1 @=? freeVarsFR1)
        , testCase "freevar fl 2"   (freeVarsFT2 @=? freeVarsFR2)
        , testCase "freevar fl 3"   (freeVarsFT3 @=? freeVarsFR3)
        , testCase "freevar fl 4"   (showFT1     @=? showFR1)
        , testCase "show fl 1"      (showFT1     @=? showFR1)
        , testCase "show fl 2"      (showFT1     @=? showFR1)
        , testCase "prenex fl 1"    (prenexT1    @=? prenexR1)
        , testCase "prenex fl 2"    (prenexT2    @=? prenexR2)
        , testCase "Skolem fl 1"    (skolemT1    @=? skolemR1)
        , testCase "Skolem fl 2"    (skolemT2    @=? skolemR2)
        , testCase "CNF fl 1"       (cnfT1       @=? cnfR1)
        , testCase "CNF fl 2"       (cnfT2       @=? cnfR2)
        ]
    ]
