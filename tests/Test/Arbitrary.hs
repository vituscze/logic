-- | 'Arbitrary' instances for 'Formula's, 'Term's and 'Var's.
module Test.Arbitrary () where

import Control.Applicative
import Control.Monad
import Test.QuickCheck

import Test.Var
import Logic

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
        go n = do
            Positive t <- smallArb :: Gen (Positive Int)
            let k :: Int
                k = roundD (fromIntegral n / fromIntegral (t + 1))
            oneof
                [ Forall  <$> smallArb <*> go (n - 1)
                , Exists  <$> smallArb <*> go (n - 1)
                , Not     <$> go (n - 1)
                , And     <$> go k <*> go k
                , Or      <$> go k <*> go k
                , Implies <$> go k <*> go k
                ]
