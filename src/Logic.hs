-- | The main module.
module Logic
    ( -- * Data types
      module Logic.Formula
    , module Logic.Term
      -- * Conjunctive normal form
    , cnf
      -- * Prenex normal form
    , prenex
    , prenexWith
    , splitPrenex
      -- * Skolem normal form
    , skolemize
    , skolemizeWith
      -- * Variables
    , names
    , rename
    )
where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Foldable
import Data.Map (Map)
import Data.Maybe
import Data.Traversable
import Prelude hiding (foldr, foldr1)

import Data.Stream
import Logic.Formula
import Logic.Term

-- | A variant of 'zip' that zips a list with infinite stream, returning
--   the zipped part and rest of the stream.
zip' :: [a] -> Stream b -> ([(a, b)], Stream b)
zip' []     ys        = ([], ys)
zip' (x:xs) (y :< ys) = ((x,y):z, z')
  where
    (z, z') = zip' xs ys

-- | An infinite stream of unique names.
names :: Stream String
names = toStream $ [1..] >>= flip replicateM ['a' .. 'z']
  where
    -- The list of names is infinite, second case cannot happen.
    toStream (x:xs) = x :< toStream xs
    toStream _      = error "Impossible."

-- | Internal monad transformer used for variable renaming. Maps variables of
--   type @v@ to variables of type @v'@.
type RenameM v v' a = ReaderT (Map v v') (State (Stream v')) a

-- | Extracts a new name @s'@ from state and runs @m@ with environment mapping
--   @s@ to @s'@.
localInsert :: Ord v => v -> RenameM v v' a -> RenameM v v' (v', a)
localInsert s m = do
    s' <- state (\(x :< xs) -> (x,xs))
    a  <- local (Map.insert s s') m
    return (s', a)

-- | Given a stream of unique names, uniquely renames all variables inside
--   a formula.
rename :: Ord v => Stream v' -> Formula r f v -> Formula r f v'
rename vars formula = evalState (runReaderT action (Map.fromAscList m)) st
  where
    -- Get renaming for free variables.
    (m, st) = zip' (Set.toAscList . freeVars $ formula) vars

    -- Note: Usage of 'local' prevents implementation through 'Traversable'.
    action = foldF
        (\r ts  -> Relation r     <$> traverse go ts)
        (\x f   -> uncurry Forall <$> localInsert x f)
        (\x f   -> uncurry Exists <$> localInsert x f)
        (\  f   -> Not     <$> f)
        (\  f g -> And     <$> f <*> g)
        (\  f g -> Or      <$> f <*> g)
        (\  f g -> Implies <$> f <*> g)
        formula

    go = traverse (fmap fromJust . asks . Map.lookup)
    -- 'fromJust' is prefectly safe here, since all variables are inside the
    -- map, by construction.

-- | Type of a quantifier together with its bound variable.
data Type a
    = F a -- ^ Universal quantifier.
    | E a -- ^ Existential quantifier.
    deriving (Eq, Ord, Show)

-- | A (quantifier) prefix tree.
--
--   Tree node stores whether the quantifiers should be swapped, list of
--   quantifiers and two subtrees, which are used for binary logical operators.
data PrefixTree a
    = Nil                                              -- ^ Empty tree.
    | Node Bool [Type a] (PrefixTree a) (PrefixTree a) -- ^ Tree node.
    deriving (Eq, Ord, Show)

-- | Adds a new quantifier to a prefix tree.
add :: Type a -> PrefixTree a -> PrefixTree a
add q Nil             = Node False [q]               Nil Nil
add q (Node b qs l r) = Node b     (swapWhen b q:qs) l   r

-- | Swaps one quantifier when the condition holds. When it doesn't, it behaves
--   as an 'id'.
swapWhen :: Bool -> Type a -> Type a
swapWhen p = if p then s else id
  where
    s (F x) = E x
    s (E x) = F x

-- | Swaps all quantifiers in a prefix tree.
swapAll :: PrefixTree a -> PrefixTree a
swapAll Nil             = Nil
swapAll (Node b qs l r) = Node (not b) qs l r

-- | Merges two prefix trees into one.
merge :: PrefixTree a -> PrefixTree a -> PrefixTree a
merge = Node False []

-- | Given a prefix tree and a 'Formula', constructs a new formula
--   with the quantifiers given by prefix tree in head position.
rebuild :: PrefixTree v -> Formula r f v -> Formula r f v
rebuild = go False
  where
    go _  Nil            = id
    go p (Node b qs l r) = rebuildL p' qs . go p' l . go p' r
      where
        p' = p /= b

    rebuildL p = flip (foldr step)
      where
        step = convert . swapWhen p

        convert (F x) = Forall x
        convert (E x) = Exists x

-- | Given a stream of unique names, converts a formula into its prenex normal
--   form.
--
--   Formula is in a prenex normal form if it begins with a string of
--   quantifiers followed by quantifier-free core part.
--
--   Note that to prevent capturing substitutions, all variables will be
--   renamed.
prenexWith :: Ord v => Stream v' -> Formula r f v -> Formula r f v'
prenexWith n = uncurry rebuild . go . rename n
  where
    go = foldF
        (\r ts                -> (Nil,                   Relation r ts))
        (\x (p,  c)           -> (add (F x) p,           c))
        (\x (p,  c)           -> (add (E x) p,           c))
        (\  (p,  c)           -> (swapAll p,             Not c))
        (\  (p1, c1) (p2, c2) -> (merge p1           p2, And c1 c2))
        (\  (p1, c1) (p2, c2) -> (merge p1           p2, Or  c1 c2))
        (\  (p1, c1) (p2, c2) -> (merge (swapAll p1) p2, Implies c1 c2))

-- | Variant of 'prenexWith' that uses default renaming.
prenex :: Formula r f String -> Formula r f String
prenex = prenexWith names

-- | Splits a formula in a prenex form into prenex and the core. Prenex part is
--   represented as a function prepending the quantifiers to another formula.
splitPrenex :: Formula r f v -> (Formula r f v -> Formula r f v, Formula r f v)
splitPrenex (Forall x f) = (Forall x . g, core)
  where
    (g, core) = splitPrenex f
splitPrenex (Exists x f) = (Exists x . g, core)
  where
    (g, core) = splitPrenex f
splitPrenex f            = (id, f)

-- | Applies a function to all recursive 'Formula' occurences.
fw :: (Formula r f v -> Formula r f v) -> Formula r f v -> Formula r f v
fw r (Forall x f)   = Forall x (r f)
fw r (Exists x f)   = Exists x (r f)
fw r (Not      f)   = Not      (r f)
fw r (And      f g) = And      (r f) (r g)
fw r (Or       f g) = Or       (r f) (r g)
fw r (Implies  f g) = Implies  (r f) (r g)
fw _ f              = f

-- | Converts a formula into conjunctive normal form. Note that this function
--   does not attempt to move or otherwise modify quantifiers. It should be
--   used on a formula in prenex normal form obtained via 'prenex' or
--   'prenexWith'.
--
--   Formula is in a conjunctive normal form when it is a conjunction of
--   disjunction of literals. A literal is either a relation or
--   negation of a relation.
cnf :: Formula r f v -> Formula r f v
cnf fl = p . foldr1 And . cnf3 . cnf2 . cnf1 $ c
  where
    (p, c) = splitPrenex fl

    -- Remove implication.
    cnf1 (Implies f g) = Or (Not (cnf1 f)) (cnf1 g)
    cnf1 f             = fw cnf1 f

    -- Distribute negation and remove double negation.
    cnf2 (Not (Not f))   = cnf2 f
    cnf2 (Not (And f g)) = Or  (cnf2 (Not f)) (cnf2 (Not g))
    cnf2 (Not (Or  f g)) = And (cnf2 (Not f)) (cnf2 (Not g))
    cnf2 f               = fw cnf2 f

    -- Get conjunction into topmost level.
    cnf3 (And f g) =        cnf3 f ++  cnf3 g
    cnf3 (Or  f g) = Or <$> cnf3 f <*> cnf3 g
    cnf3 f         = [f]

-- | Given a stream of new function names, transforms a prenex formula into
--   its Skolem variant, removing any quantifiers. New function symbols are
--   distinguished by 'Left'.
--
--   Skolem variant of formula /φ/ is a closed universal formula /φ'/ in
--   prenex form such that /⊢ φ' → φ/.
--
--   Note that this function does not check if the formula is in prenex
--   normal form. It should be used on formulas obtained via 'prenex' or
--   'prenexWith'.
skolemizeWith :: Ord v => Stream f'
              -> Formula r f v -> Formula r (Either f' f) v
skolemizeWith name formula = foldF
    (\r -> Relation r . map updateTerm) Forall Exists Not And Or Implies c
  where
    -- Core of a formula in prenex normal form.
    c = snd $ splitPrenex formula

    -- Updates existentially quantified variables with their Skolem function.
    updateTerm =
        foldT (\v -> fromMaybe (Var v) (Map.lookup v m)) (Function . Right)

    -- Final mapping.
    m = execWriter (evalStateT action name)
      where
        action = createMap . reverse . qList $ formula

    -- Create a mapping from existentially bound variables to functions.
    createMap []       = return []
    createMap (F x:xs) = (Var x:) <$> createMap xs
    createMap (E x:xs) = do
        ts <- createMap xs
        f  <- state (\(y :< ys) -> (y, ys))
        tell (Map.singleton x . Function (Left f) . reverse $ ts)
        return ts

    -- Extracts prenext part into a list.
    qList (Forall x f) = F x:qList f
    qList (Exists x f) = E x:qList f
    qList _            = []

-- | Variant of 'skolemizeWith' that uses default function names.
skolemize :: Ord v => Formula r f v -> Formula r (Either String f) v
skolemize = skolemizeWith names
