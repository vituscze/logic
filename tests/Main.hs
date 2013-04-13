-- | Test suite.
module Main (main) where

import qualified Data.Set as Set

import Control.Applicative
import Control.Monad
import Test.QuickCheck
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)

import Logic hiding (prenex, skolemize)

-- | Specialized variant of 'log' to prevent defaulting warnings.
logD :: Double -> Double
logD = log

-- | Specialized variant of 'round' to prevent defaulting warnings.
roundD :: Double -> Int
roundD = round

-- | Reduces the size argument to produce smaller random values.
smallArb :: Arbitrary a => Gen a
smallArb = sized $ \n ->
    resize (round . logD . fromIntegral $ n) arbitrary

newtype Var
  = V String
  deriving (Eq, Ord, Show)

-- | Unique variable names.
names' :: Stream Var
names' = fmap V names

-- | 'Logic.prenex' using 'Var' instead of 'String'.
prenex :: Formula r f Var -> Formula r f Var
prenex = prenexWith names'

-- | 'Logic.skolemize' using 'Var' instead of 'String'.
skolemize :: Ord v => Formula r f v -> Formula r (Either Var f) v
skolemize = skolemizeWith names'

instance Arbitrary Var where
    arbitrary = do
        n <- choose (0, 2)
        V <$> replicateM n arbitrary

instance (Arbitrary f, Arbitrary v) => Arbitrary (Term f v) where
    arbitrary = sized go
      where
        go 0 = Var <$> arbitrary
        go n = do
            Positive t <- smallArb
            let k :: Int
                k = roundD (fromIntegral n / fromIntegral (t + 1))
            Function <$> arbitrary <*> replicateM t (go k)

instance (Arbitrary r, Arbitrary f, Arbitrary v)
      => Arbitrary (Formula r f v) where
    arbitrary = sized go
      where
        go 0 = do
            Positive t <- smallArb
            Relation <$> arbitrary <*> replicateM t smallArb
        go n = oneof
            [ unary
            , binary
            ]
          where
            unary = oneof
                [ Forall <$> smallArb <*> go (n - 1)
                , Exists <$> smallArb <*> go (n - 1)
                , Not    <$> go (n - 1)
                ]
            binary = do
                Positive t <- smallArb :: Gen (Positive Int)
                let k :: Int
                    k = roundD (fromIntegral n / fromIntegral (t + 1))
                oneof
                    [ And     <$> go k <*> go k
                    , Or      <$> go k <*> go k
                    , Implies <$> go k <*> go k
                    ]

-- | 'Term' 'fmap' satisfies the first 'Functor' law. Second one then holds
--   by parametricity.
fmapTermFunctorProp :: Term Var Var -> Bool
fmapTermFunctorProp t = fmap id t == t

-- | 'foldT' applied to constructors is identity.
foldTermId :: Term Var Var -> Bool
foldTermId t = t == foldT Var Function t

-- | A variable is in 'freeVars' @t@ precisely when it is in @t@.
freeVarsTVarsInTerm :: Var -> Term Var Var -> Bool
freeVarsTVarsInTerm s t = s `Set.member` fv == contains s t
  where
    fv = freeVarsT t

    contains var = go
      where
        go (Var x)         = var == x
        go (Function _ ts) = any go ts

-- | 'Formula' 'fmap' satisfies the first 'Functor' law. See
--   'fmap_term_functor_prop'.
fmapFormulaFunctorProp :: Formula Var Var Var -> Bool
fmapFormulaFunctorProp f = fmap id f == f

-- | 'foldF' applied to constructors is identity.
foldFormulaId :: Formula Var Var Var -> Bool
foldFormulaId f = f == foldF Relation Forall Exists Not And Or Implies f

-- | 'cnf' produces a conjunctive normal form.
cnfProp :: Formula Var Var Var -> Bool
cnfProp fl = check . cnf . snd . splitPrenex . prenex $ fl
  where
    check (And f g)            = check f && check g
    check (Or  f g)            = check2 (Or f g)
    check (Not (Relation _ _)) = True
    check (Relation _ _)       = True
    check _                    = False

    check2 (Or f g)             = check2 f && check2 g
    check2 (Not (Relation _ _)) = True
    check2 (Relation _ _)       = True
    check2 _                    = False

-- | 'cnf' is idempotent.
cnfIdempotent :: Formula Var Var Var -> Bool
cnfIdempotent f = cnf f' == cnf (cnf f')
  where
    f' = snd . splitPrenex . prenex $ f

-- | 'prenex' produces prenex normal form.
prenexProp :: Formula Var Var Var -> Bool
prenexProp = check . prenex
  where
    check (Forall _ f) = check f
    check (Exists _ f) = check f
    check f            = binderFree f

-- | 'prenex' is idempotent with respect to formula structure (especially
--   /not/ with respect to variables, which can be renamed).
prenexIdempotent :: Formula Var Var Var -> Bool
prenexIdempotent f = prenex f `varEq` prenex (prenex f)
  where
    varEqT (Function f1 ts1) (Function f2 ts2) =
        f1 == f2 && and (zipWith varEqT ts1 ts2)
    varEqT (Var _) (Var _) = True
    varEqT _        _      = False

    varEq (Relation r1 ts1) (Relation r2 ts2) =
        r1 == r2 && and (zipWith varEqT ts1 ts2)
    varEq (Forall _ f1)    (Forall _ f2)    = f1 `varEq` f2
    varEq (Exists _ f1)    (Exists _ f2)    = f1 `varEq` f2
    varEq (Not      f1)    (Not      f2)    = f1 `varEq` f2
    varEq (And      f1 g1) (And      f2 g2) = f1 `varEq` f2 && g1 `varEq` g2
    varEq (Or       f1 g1) (Or       f2 g2) = f1 `varEq` f2 && g1 `varEq` g2
    varEq (Implies  f1 g1) (Implies  f2 g2) = f1 `varEq` f2 && g1 `varEq` g2
    varEq _               _                 = False

-- | 'skolemize' produces Skolem normal form.
skolemizeProp :: Formula Var Var Var -> Bool
skolemizeProp fl = ((&&) <$> noEx <*> binderFree) . skolemize $ fl'
  where
    fl' = prenex fl

    -- All existentially quantified variables.
    exVars = exQualVars fl'

    noEx = foldFw (`Set.notMember` exVars)
        (const and) (const and) (const id) id (&&)

    -- Extracts existentially quantified variables from prenex part.
    exQualVars (Forall _ f) = exQualVars f
    exQualVars (Exists x f) = Set.insert x (exQualVars f)
    exQualVars _            = Set.empty

-- | Checks whether the formula contains any binders ('Forall' or 'Exists').
binderFree :: Formula r f v -> Bool
binderFree = foldF
    (\_ _ -> True)
    (\_ _ -> False)
    (\_ _ -> False)
    id (&&) (&&) (&&)

-- Test harness.

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
    ]
