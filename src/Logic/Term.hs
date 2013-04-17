-- | Terms of a first order logic formula.
module Logic.Term
    ( Term(..)
    , fmapT
    , foldT
    , freeVarsT
    , showTerm
    , showSTerm
    , traverseT
    )
where

import qualified Data.Set as Set

import Control.Applicative
import Control.Monad.Identity
import Data.Foldable
import Data.List (intersperse)
import Data.Set (Set, unions)
import Data.Traversable
import Prelude hiding (foldr)

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

-- | Variant of 'showTerm' that returns a difference list.
showSTerm :: Term String String -> ShowS
showSTerm (Var v) = showString v
showSTerm (Function f ts) = concatD
    [ str f
    , str "("
    , concatD . intersperse (str ",") . map showSTerm $ ts
    , str")"
    ]
  where
    str     = showString

    -- Difference list concatenation.
    concatD = foldr (.) id

-- | Pretty prints a 'Term'.
--
-- > showTerm (Function "f" [Function "g" [Var "x"], Var "y"])
-- > == "f(g(x),y)"
showTerm :: Term String String -> String
showTerm t = showSTerm t ""

-- | 'Term' bimap.
--
-- > showTerm (fmapT (++ "!") (++ "?") (Function "f" [Var "x", Var "y"]))
-- > == "f!(x?,y?)"
fmapT :: (f -> f') -> (v -> v') -> Term f v -> Term f' v'
fmapT func var = runIdentity . traverseT (Identity . func) (Identity . var)

-- | 'Term' bitraversal.
--
-- >>> traverseT (\_ -> getLine) return $ Function () [Var "x", Function () []]
-- f
-- g
-- Function "f" [Var "x",Function "g" []]
traverseT :: Applicative a
          => (f -> a f') -> (v -> a v')
          -> Term f v -> a (Term f' v')
traverseT func var = foldT
  (\v    -> Var      <$> var v)
  (\f ts -> Function <$> func f <*> sequenceA ts)

-- | 'Term' catamorphism.
--
-- > foldT (\_ -> 0) (\_ ts -> 1 + sum ts) (Function "f" [Function "g" []])
-- > == 2
foldT :: (v -> r)        -- ^ Variables.
      -> (f -> [r] -> r) -- ^ Functions.
      -> Term f v        -- ^ Term to reduce.
      -> r
foldT var func = go
  where
    go (Var x)         = var x
    go (Function f ts) = func f (map go ts)

-- | All variables of a 'Term'.
--
-- > freeVarsT (Function "f" [Var "x", Var "y", Var "x"])
-- > == Set.fromList ["x", "y"]
freeVarsT :: Ord v => Term f v -> Set v
freeVarsT = foldT Set.singleton (const unions)
