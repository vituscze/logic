-- | First order logic formulas.
module Logic.Formula
    ( -- * Recursion schemes
      Formula(..)
    , fmapF
    , foldF
    , foldFw
    , traverseF
      -- * Variables
    , freeVars
      -- * Pretty printing
    , showFormula
    , showFormulaUnicode
    , showSFormula
    , showSFormulaUnicode
    )
where

import qualified Data.Set as Set

import Control.Applicative
import Control.Monad.Identity
import Data.Foldable
import Data.List (intersperse)
import Data.Set (Set, union, unions)
import Data.Traversable
import Prelude hiding (foldr)

import Logic.Term

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
--   The first argument specifies strings (in a difference list form) to use
--   for 'Forall', 'Exists', 'Not', 'And', 'Or' and 'Implies', in this order.
--   The list shall have precisely 6 elements.
showFormulaWith :: [ShowS] -> Formula String String String -> ShowS
showFormulaWith enc = go 0
  where
    str = showString

    -- Difference list concatenation.
    concatD = foldr (.) id

    -- If the condition is satisfied, surround the 'ShowS' string
    -- in parentheses.
    pWhen p s = if p then str "(" . s' . str ")" else s'
      where
        s' = concatD s

    -- 'ShowS' representation of logical operators.
    [fa,  ex,  neg,  con,  dis,  imp]  = enc

    -- Precendence levels.
    [faP, exP, negP, conP, disP, impP] = [7, 7, 7, 5, 3, 1] :: [Int]

    go p (Forall x f)    = pWhen (p > faP)
        [str "(", fa, str x, str ")", go faP f]
    go p (Exists x f)    = pWhen (p > exP)
        [str "(", ex, str x, str ")", go exP f]
    go p (Not f)         = pWhen (p > negP)
        [neg, go negP f]
    go p (And f g)       = pWhen (p > conP)
        [go conP f, con, go conP g]
    go p (Or  f g)       = pWhen (p > disP)
        [go disP f, dis, go disP g]
    go p (Implies f g)   = pWhen (p > impP)
        [go (impP + 1) f, imp, go impP g]
    go _ (Relation r ts) = concatD
        [ str r
        , str "["
        , concatD . intersperse (str ",") . map showSTerm $ ts
        , str "]"
        ]

-- | Pretty prints a 'Formula', using ASCII look-alike characters for
--   logical operators.
--
--   Note that 'Relation' arguments are enclosed in square brackets for
--   easier recognition.
showFormula :: Formula String String String -> String
showFormula f = showSFormula f ""

-- | Pretty prints a 'Formula', using Unicode characters for logical
--   operators.
--
--   See 'showFormula'.
showFormulaUnicode :: Formula String String String -> String
showFormulaUnicode f = showSFormulaUnicode f ""

-- | Variant of 'showFormula' that returs a difference list.
showSFormula :: Formula String String String -> ShowS
showSFormula = showFormulaWith
    (map showString ["V", "E", "~", " & ", " v ", " -> "])

-- | Variant of 'showFormulaUnicode' that returns a difference list.
showSFormulaUnicode :: Formula String String String -> ShowS
showSFormulaUnicode = showFormulaWith
    (map showString ["\8704", "\8707", "\172", " & ", " \8744 ", " \8594 "])

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
    go (Not      f)    = neg  (go f)
    go (And      f g)  = con  (go f) (go g)
    go (Or       f g)  = dis  (go f) (go g)
    go (Implies  f g)  = imp  (go f) (go g)

-- | Weak 'Formula' catamorphism.
--
--   Several 'Formula' constructors use only a single reduction function,
--   namely binders ('Forall' and 'Exists') and binary operators ('And',
--   'Or' and 'Implies').
--
--   This function does recurse into 'Term's.
foldFw :: (v -> r)         -- ^ Variables.
       -> (f  -> [r] -> r) -- ^ Functions.
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

-- | All free variables of a 'Formula'.
freeVars :: Ord v => Formula r f v -> Set v
freeVars =
    foldFw Set.singleton (const unions) (const unions) Set.delete id union
