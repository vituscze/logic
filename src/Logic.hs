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
import Prelude hiding (foldr)

import Data.Stream
import Logic.Formula
import Logic.Term

-- | Weak equality test which compares only formula structure.
weakEq :: Formula r f v -> Formula r f v -> Bool
weakEq (Relation _ _)   (Relation _ _)   = True
weakEq (Forall _ f1)    (Forall _ f2)    = weakEq f1 f2
weakEq (Exists _ f1)    (Exists _ f2)    = weakEq f1 f2
weakEq (Not      f1)    (Not      f2)    = weakEq f1 f2
weakEq (And      f1 g1) (And      f2 g2) = weakEq f1 f2 && weakEq g1 g2
weakEq (Or       f1 g1) (Or       f2 g2) = weakEq f1 f2 && weakEq g1 g2
weakEq (Implies  f1 g1) (Implies  f2 g2) = weakEq f1 f2 && weakEq g1 g2
weakEq _                _                = False

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

-- | Type of a binder together with its bound variable.
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

-- | Variant of 'iterate' that repeatedly applies the function @f@, until two
--   consecutive results are equal.
stabilizeBy :: (a -> a -> Bool) -> (a -> a) -> a -> [a]
stabilizeBy eq f =
    map snd . takeWhile (uncurry ((not .) . eq)) . (zip`ap`tail) . iterate f

-- | Returns the stabilized result.
stabilizeByR :: (a -> a -> Bool) -> (a -> a) -> a -> a
stabilizeByR eq f x = case stabilizeBy eq f x of
    [] -> x
    xs -> last xs

-- | Converts a formula into conjunctive normal form. Note that this function
--   does not attempt to move or otherwise modify quantifiers. It should be
--   used on a formula in prenex normal form obtained via 'prenex' or
--   'prenexWith'.
--
--   Formula is in a conjunctive normal form when it is a conjunction of
--   disjunction of literals. A literal is either a relation or
--   negation of a relation.
cnf :: Formula r f v -> Formula r f v
cnf = foldr ((.) . stabilizeByR weakEq) id [cnf3, cnf2, cnf1]
  where
    -- Remove implication, one step at a time.
    cnf1 (Implies f g) = Or (Not (cnf1 f)) (cnf1 g)
    cnf1 f             = fw cnf1 f

    -- Remove and distribute negation.
    cnf2 (Not (Not f))   = cnf2 f
    cnf2 (Not (And f g)) = Or  (Not (cnf2 f)) (Not (cnf2 g))
    cnf2 (Not (Or  f g)) = And (Not (cnf2 f)) (Not (cnf2 g))
    cnf2 f               = fw cnf2 f

    -- Get conjunction into topmost level.
    cnf3 (Or f (And g h)) = And (Or (cnf3 f) (cnf3 g)) (Or (cnf3 f) (cnf3 h))
    cnf3 (Or (And f g) h) = And (Or (cnf3 f) (cnf3 h)) (Or (cnf3 g) (cnf3 h))
    cnf3 f                = fw cnf3 f

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
        action = createMap . reverse . binderList $ formula

    -- Create a mapping from existentially bound variables to functions.
    createMap []       = return []
    createMap (F x:xs) = (Var x:) <$> createMap xs
    createMap (E x:xs) = do
        ts <- createMap xs
        f  <- state (\(y :< ys) -> (y, ys))
        tell (Map.singleton x . Function (Left f) . reverse $ ts)
        return ts

    -- Extracts prenext part into a list.
    binderList (Forall x f) = F x:binderList f
    binderList (Exists x f) = E x:binderList f
    binderList _            = []

-- | Variant of 'skolemizeWith' that uses default function names.
skolemize :: Ord v => Formula r f v -> Formula r (Either String f) v
skolemize = skolemizeWith names
