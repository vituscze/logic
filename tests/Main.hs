-- | Test suite.
module Main (main) where

import qualified Data.Set as Set
import qualified Logic

import Control.Applicative
import Control.Monad
import Test.HUnit hiding (Test)
import Test.QuickCheck
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)

import Data.Stream
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

-- Properties.

-- | 'Term' 'fmap' satisfies the first 'Functor' law. Second one then holds
--   by parametricity.
fmapTermFunctorProp :: Term Var Var -> Bool
fmapTermFunctorProp t = fmap id t == t

-- | 'foldT' applied to constructors is identity.
foldTermId :: Term Var Var -> Bool
foldTermId t = t == foldT Var Function t

-- | A variable is in 'freeVars' @t@ precisely when it is in @t@.
freeVarsTVarsInTerm :: Var -> Term Var Var -> Bool
freeVarsTVarsInTerm s t = s `Set.member` fvT == contains s t
  where
    fvT = freeVarsT t

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

-- Concrete data.

-- | Term free variables helper.
fv :: Term String String -> [String]
fv = Set.toList . freeVarsT

-- | Formula free variables helper.
fvf :: Formula String String String -> [String]
fvf = Set.toList . freeVars

-- | Constructs an empty relation.
r :: String -> Formula String String String
r x = Relation x []

-- | Skolemize a formula and get rid of 'Either'.
sk :: Formula String String String -> Formula String String String
sk = fmapF id (either id id) id . Logic.skolemize . Logic.prenex

-- Testing data for term free variables and pretty printing.
term1, term2, term3 :: Term String String
term1 = Function "f" [Var "a", Function "g" [Var "b", Var "c"], Var "c"]
term2 = Function "f" [Function "g" [], Function "h" []]
term3 = Var "a"

-- Testing data for formula free variables.
formula1, formula2, formula3, formula4 :: Formula String String String
formula1 = Relation "R" [Var "x"]
formula2 = Forall "x" $ Relation "R" [Var "x", Var "y"]
formula3 = Or (And formula2 (Relation "Q" [Var "x"])) formula2
formula4 = Exists "y" formula2

-- Testing data for formula pretty printing.
formula5, formula6 :: Formula String String String
formula5 = And (Implies (Implies (r "P") (r "Q")) (r "R"))
    (Relation "S" [Var "x", Var "y"])
formula6 = Not (Forall "x" (And (Or (r "A") (r "B")) (r "C")))

-- Testing data for prenex and Skolem normal form.
formula7, formula8 :: Formula String String String
formula7 = Not (Implies (Exists "x" (Relation "R" [Var "x", Var "y"]))
    (And (Relation "Q" [Var "x"]) (Exists "y"
    (Relation "S" [Var "y", Var "z"]))))
formula8 = Not (Implies (Implies (Exists "x" (Relation "R" [Var "x"]))
    (Relation "Q" [Var "y"])) (Forall "y" (Exists "z" (Relation "S"
    [Var "x", Var "y", Var "z"]))))

-- Testing data for CNF.
formula9, formula10 :: Formula String String String
formula9  = Forall "x" (Implies (Not (r "P")) (r "Q"))
formula10 = Implies (Or (r "A") (Not (Implies (Or (r "B") (r "C"))
    (And (Not (r "D")) (r "E"))))) (And (Not (r "F")) (Not (r "G")))

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
    , testGroup "concrete data"
        [ testCase "freevar term 1" (fv term1 @=? ["a", "b", "c"])
        , testCase "freevar term 2" (fv term2 @=? [])
        , testCase "freevar term 3" (fv term3 @=? ["a"])
        , testCase "show term 1"    (showTerm term1 @=? "f(a,g(b,c),c)")
        , testCase "show term 2"    (showTerm term2 @=? "f(g(),h())")
        , testCase "show term 3"    (showTerm term3 @=? "a")
        , testCase "freevar fl 1"   (fvf formula1 @=? ["x"])
        , testCase "freevar fl 2"   (fvf formula2 @=? ["y"])
        , testCase "freevar fl 3"   (fvf formula3 @=? ["x", "y"])
        , testCase "freevar fl 4"   (fvf formula4 @=? [])
        , testCase "show fl 1"      (showFormula formula5 @=?
            "((P[] -> Q[]) -> R[]) & S[x,y]")
        , testCase "show fl 2"      (showFormula formula6 @=?
            "~(Vx)((A[] v B[]) & C[])")
        , testCase "prenex fl 1"    (showFormula (Logic.prenex formula7) @=?
            "(Ed)(Ve)~(R[d,b] -> Q[a] & S[e,c])")
        , testCase "prenex fl 2"    (showFormula (Logic.prenex formula8) @=?
            "(Vc)(Ed)(Ve)~((R[c] -> Q[b]) -> S[a,d,e])")
        , testCase "Skolem fl 1"    (showFormula (sk formula7) @=?
            "~(R[a(),b] -> Q[a] & S[e,c])")
        , testCase "Skolem fl 2"    (showFormula (sk formula8) @=?
            "~((R[c] -> Q[b]) -> S[a,a(c),e])")
        , testCase "CNF fl 1"       (showFormula (cnf formula9)  @=?
            "(Vx)(P[] v Q[])")
        , testCase "CNF fl 2"       (showFormula (cnf formula10) @=?
            "(~A[] v ~F[]) & (~A[] v ~G[]) & (~B[] v ~D[] v ~F[]) & (~B[]\
            \ v ~D[] v ~G[]) & (~B[] v E[] v ~F[]) & (~B[] v E[] v ~G[]) \
            \& (~C[] v ~D[] v ~F[]) & (~C[] v ~D[] v ~G[]) & (~C[] v E[] \
            \v ~F[]) & (~C[] v E[] v ~G[])")
        ]
    ]
