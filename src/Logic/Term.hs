-- | Terms of a first order logic formula.
module Logic.Term
    ( Term(..)
    , fmapT
    , foldT
    , freeVarsT
    , showTerm
    , traverseT
    )
where

import qualified Data.Set as Set

import Control.Applicative
import Control.Monad.Identity
import Data.Foldable
import Data.List (intercalate)
import Data.Set (Set, unions)
import Data.Traversable
import Prelude hiding (concat)

-- | A data type for terms. @f@ is the type of function labels and @v@ of
--   variable labels.
data Term f v
    = Var v                 -- ^ Variable.
    | Function f [Term f v] -- ^ Function.
    deriving (Eq, Ord, Show)

instance Functor (Term f) where
    fmap = fmapT id

instance Foldable (Term f) where
    fold = fst . traverse (flip (,) ())

instance Traversable (Term f) where
    traverse = traverseT pure

-- | Pretty prints a 'Term'.
showTerm :: Term String String -> String
showTerm (Var v)         = v
showTerm (Function f ts) = concat
    [f, "(", intercalate "," (map showTerm ts), ")"]

-- | 'Term' bimap.
fmapT :: (f -> f') -> (v -> v') -> Term f v -> Term f' v'
fmapT func var = runIdentity . traverseT (Identity . func) (Identity . var)

-- | 'Term' bitraversal.
traverseT :: Applicative a
          => (f -> a f') -> (v -> a v')
          -> Term f v -> a (Term f' v')
traverseT func var = foldT
  (\v    -> Var      <$> var v)
  (\f ts -> Function <$> func f <*> sequenceA ts)

-- | 'Term' catamorphism.
foldT :: (v -> r)        -- ^ Variables.
      -> (f -> [r] -> r) -- ^ Functions.
      -> Term f v        -- ^ Term to reduce.
      -> r
foldT var func = go
  where
    go (Var x)         = var x
    go (Function f ts) = func f (map go ts)

-- | All variables of a 'Term'.
freeVarsT :: Ord v => Term f v -> Set v
freeVarsT = foldT Set.singleton (const unions)
