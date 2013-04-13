-- | The main module.
module Logic
   ( -- * Streams
      Stream(..)
    , names
    , unfoldS
    , unfoldStopS
      -- * Terms
    , Term(..)
    , fmapT
    , foldT
    , freeVarsT
    , showTerm
    , traverseT
      -- * Formulas
    , Formula(..)
    , fmapF
    , foldF
    , foldFw
    , showFormula
    , showFormulaUnicode
    , traverseF
      -- ** Conjunctive normal form
    , cnf
      -- ** Prenex normal form
    , prenex
    , prenexWith
    , splitPrenex
      -- ** Skolem normal form
    , skolemize
    , skolemizeWith
      -- ** Variables
    , freeVars
    , rename
    )
where

import qualified Data.Map      as Map
import qualified Data.Sequence as Seq
import qualified Data.Set      as Set

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Foldable
import Data.Function
import Data.List (intercalate)
import Data.Map (Map)
import Data.Maybe
import Data.Sequence ((><), (<|))
import Data.Set (Set, union, unions)
import Data.Traversable
import Prelude hiding (foldr, concat)

infixr 5 :<

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
showTerm (Function f ts) = f ++ "(" ++ intercalate "," (map showTerm ts) ++  ")"

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

-- | A data type for logical formulas. @r@ is the type of relation labels,
--   @f@ of function labels and @v@ of variable labels.
data Formula r f v
    = Relation r [Term f v]                      -- ^ Relation of 'Term's.
    | Forall   v (Formula r f v)                 -- ^ Universal quantifier.
    | Exists   v (Formula r f v)                 -- ^ Existential quantifier.
    | Not        (Formula r f v)                 -- ^ Negation.
    | And        (Formula r f v) (Formula r f v) -- ^ Conjunction.
    | Or         (Formula r f v) (Formula r f v) -- ^ Disjunction.
    | Implies    (Formula r f v) (Formula r f v) -- ^ Implication.
    deriving (Eq, Ord, Show)

instance Functor (Formula r f) where
    fmap = fmapF id id

instance Foldable (Formula r f) where
    fold = fst . traverse (flip (,) ())

instance Traversable (Formula r f) where
    traverse = traverseF pure pure

-- | Helper function for 'Formula' pretty printing.
--
--   The first argument specifies strings to use for 'Forall', 'Exists',
--   'Not', 'And', 'Or' and 'Implies', in this order. The list shall have
--   precisely 6 elements.
showFormulaWith :: [String] -> Formula String String String -> String
showFormulaWith enc = go 0
  where
    parensWhen p s
      | p         = "(" ++ s' ++ ")"
      | otherwise = s'
      where
        s' = concat s

    -- 'String' representation of logical operators.
    [fa,  ex,  neg,  con,  dis,  imp] = enc

    -- Precendence levels.
    [faP, exP, negP, conP, disP, impP] = [5, 5, 5, 4, 3, 2] :: [Int]

    go p (Forall x f)    = parensWhen (p > faP)  ["(", fa, x, ")", go faP f]
    go p (Exists x f)    = parensWhen (p > exP)  ["(", ex, x, ")", go exP f]
    go p (Not f)         = parensWhen (p > negP) [neg, go negP f]
    go p (And f g)       = parensWhen (p > conP) [go conP f, con, go conP g]
    go p (Or  f g)       = parensWhen (p > disP) [go disP f, dis, go disP g]
    go p (Implies f g)   = parensWhen (p > impP) [go impP f, imp, go impP g]
    go _ (Relation r ts) = concat
        [r, "[", intercalate "," (map showTerm ts), "]"]

-- | Pretty prints a 'Formula', using ASCII look-alike characters for
--   logical operators.
--
--   Note that 'Relation' arguments are enclosed in square brackets for
--   easier recognition.
showFormula :: Formula String String String -> String
showFormula = showFormulaWith
    ["V", "E", "~", " & ", " v ", " -> "]

-- | Pretty prints a 'Formula', using Unicode characters for logical
--   operators.
--
--   See 'showFormula'.
showFormulaUnicode :: Formula String String String -> String
showFormulaUnicode = showFormulaWith
    ["\8704", "\8707", "\172", " & ", " \8744 ", " \8594 "]

-- | 'Formula' trimap.
fmapF :: (r -> r') -> (f -> f') -> (v -> v')
      -> Formula r f v -> Formula r' f' v'
fmapF rel func var = runIdentity
    . traverseF (Identity . rel) (Identity . func) (Identity . var)

-- | 'Formula' tritraversal.
traverseF :: Applicative a
          => (r -> a r') -> (f -> a f') -> (v -> a v')
          -> Formula r f v -> a (Formula r' f' v')
traverseF rel func var = foldF
    (\r ts  -> Relation <$> rel r <*> traverse (traverseT func var) ts)
    (\x f   -> Forall   <$> var x <*> f)
    (\x f   -> Exists   <$> var x <*> f)
    (\  f   -> Not      <$> f)
    (\  f g -> And      <$> f <*> g)
    (\  f g -> Or       <$> f <*> g)
    (\  f g -> Implies  <$> f <*> g)

-- | 'Formula' catamorphism.
--
--   Note that unlike 'foldFw', this function does not recurse into 'Term's.
foldF :: (r' -> [Term f v] -> r) -- ^ Relations.
      -> (v -> r -> r)           -- ^ Universal quantificator.
      -> (v -> r -> r)           -- ^ Existential quantificator.
      -> (r -> r)                -- ^ Negation.
      -> (r -> r -> r)           -- ^ Conjunction.
      -> (r -> r -> r)           -- ^ Disjunction.
      -> (r -> r -> r)           -- ^ Implication.
      -> Formula r' f v          -- ^ Formula to reduce.
      -> r
foldF rel fa ex neg con dis imp = go
  where
    go (Relation r ts) = rel r ts
    go (Forall x f)    = fa x (go f)
    go (Exists x f)    = ex x (go f)
    go (Not f)         = neg  (go f)
    go (And f g)       = con  (go f) (go g)
    go (Or  f g)       = dis  (go f) (go g)
    go (Implies f g)   = imp  (go f) (go g)

-- | Weak 'Formula' catamorphism.
--
--   Several 'Formula' constructors use only a single reduction function,
--   namely binders ('Forall' and 'Exists') and binary operators ('And',
--   'Or' and 'Implies').
--
--   This function does recurse into 'Term's.
foldFw :: (v -> r)         -- ^ Variables.
       -> (f -> [r] -> r)  -- ^ Functions.
       -> (r' -> [r] -> r) -- ^ Relations.
       -> (v -> r -> r)    -- ^ Binders.
       -> (r -> r)         -- ^ Negation.
       -> (r -> r -> r)    -- ^ Binary operators.
       -> Formula r' f v   -- ^ Formula to reduce.
       -> r
foldFw var func rel binder unary binary =
    foldF rel' binder binder unary binary binary binary
  where
    rel' r = rel r . map (foldT var func)

-- | Weak equality test which compares only formula structure.
weakEq :: Formula r f v -> Formula r f v -> Bool
weakEq (Relation _ _)  (Relation _ _)  = True
weakEq (Forall _ f1)   (Forall _ f2)   = weakEq f1 f2
weakEq (Exists _ f1)   (Exists _ f2)   = weakEq f1 f2
weakEq (Not     f1)    (Not     f2)    = weakEq f1 f2
weakEq (And     f1 g1) (And     f2 g2) = weakEq f1 f2 && weakEq g1 g2
weakEq (Or      f1 g1) (Or      f2 g2) = weakEq f1 f2 && weakEq g1 g2
weakEq (Implies f1 g1) (Implies f2 g2) = weakEq f1 f2 && weakEq g1 g2
weakEq _               _               = False

-- | An infinite stream of @a@s.
data Stream a
    = a :< Stream a

instance Functor Stream where
    fmap f (x :< xs) = f x :< fmap f xs

instance Applicative Stream where
    pure a = fix (a :<)
    (f :< fs) <*> (x :< xs) = f x :< (fs <*> xs)

-- | Stream anamorphism.
unfoldS :: (b -> (a, b)) -> b -> Stream a
unfoldS step = go
  where
    go s = x :< go s'
      where
        (x, s') = step s

-- | Stream apomorphism.
unfoldStopS :: (b -> (a, Either b (Stream a))) -> b -> Stream a
unfoldStopS step = go
  where
    go s = x :< case e of
        Left s'   -> go s'
        Right st  -> st
      where
        (x, e) = step s

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

-- | All variables of a 'Term'.
freeVarsT :: Ord v => Term f v -> Set v
freeVarsT = foldT Set.singleton (const unions)

-- | All free variables of a 'Formula'.
freeVars :: Ord v => Formula r f v -> Set v
freeVars =
    foldFw Set.singleton (const unions) (const unions) Set.delete id union

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

-- | Type of trees.
data Tree a
    = Nil
    | Node a (Tree a) (Tree a)
    deriving (Eq, Ord, Show)

-- | A tree storing a quantifier prefix.
type PrefixTree a = Tree (Bool, [Type a])

add :: Type a -> PrefixTree a -> PrefixTree a
add q Nil                = Node (False, [q]) Nil Nil
add q (Node (b, qs) l r) = Node (b, q:qs)    l   r

swap :: PrefixTree a -> PrefixTree a
swap Nil                = Nil
swap (Node (b, qs) l r) = Node (not b, qs) l r

merge :: PrefixTree a -> PrefixTree a -> PrefixTree a
merge = Node (False, [])

rebuild :: PrefixTree v -> Formula r f v -> Formula r f v
rebuild = go False
  where
    go _  Nil               = id
    go p (Node (b, qs) l r) = rebuildL p' qs . go p' l . go p' r
      where
        p' = p /= b

    rebuildL p l = flip (foldr step) l
      where
        step (F x)
          | p         = Exists x
          | otherwise = Forall x
        step (E x)
          | p         = Forall x
          | otherwise = Exists x

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
        (\r ts                -> (Nil,                Relation r ts))
        (\x (p,  c)           -> (add (F x) p,        c))
        (\x (p,  c)           -> (add (E x) p,        c))
        (\  (p,  c)           -> (swap p,             Not c))
        (\  (p1, c1) (p2, c2) -> (merge p1        p2, And c1 c2))
        (\  (p1, c1) (p2, c2) -> (merge p1        p2, Or  c1 c2))
        (\  (p1, c1) (p2, c2) -> (merge (swap p1) p2, Implies c1 c2))

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
splitPrenex f = (id, f)

-- | Applies a function to all recursive 'Formula' occurences.
fw :: (Formula r f v -> Formula r f v) -> Formula r f v -> Formula r f v
fw r (Forall x f)  = Forall x (r f)
fw r (Exists x f)  = Exists x (r f)
fw r (Not f)       = Not      (r f)
fw r (And f g)     = And      (r f) (r g)
fw r (Or  f g)     = Or       (r f) (r g)
fw r (Implies f g) = Implies  (r f) (r g)
fw _ f             = f

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
