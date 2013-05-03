-- | 'Formula' operations with newtype 'Var's instead of 'String's.
module Test.Var
    ( Var(..)
    , names
    , prenex
    , skolemize
    )
where

import qualified Logic

import Data.Stream
import Logic (Formula)

-- | Variable names.
newtype Var
    = V String
    deriving (Eq, Ord, Show)

-- | Unique variable names.
names :: Stream Var
names = fmap V Logic.names

-- | 'Logic.prenex' using 'Var' instead of 'String'.
prenex :: Formula r f Var -> Formula r f Var
prenex = Logic.prenexWith names

-- | 'Logic.skolemize' using 'Var' instead of 'String'.
skolemize :: Ord v => Formula r f v -> Formula r (Either Var f) v
skolemize = Logic.skolemizeWith names
