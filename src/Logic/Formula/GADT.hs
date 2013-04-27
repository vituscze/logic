{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE TypeOperators  #-}
-- | Alternative definition of a first order logic formula which remembers
--   its kind in type.
module Logic.Formula.GADT where

import qualified Data.Set as Set

import Data.Set (Set, union, unions)

import Logic.Formula.Spec
import Logic.Term

-- | A data type for logical formulas. @r@ is the type of relation labels,
--   @f@ of function labels and @v@ of variable labels. @t@ are type level
--   encoding of formula properties, namely being in a prenex and Skolem
--   normal forms.
data Formula :: Bool -> QType -> * -> * -> * -> * where
    Relation :: r -> [Term f v]        -> Formula True None r f v
    Forall   :: v -> Formula p t r f v -> Formula p (Merge t JustForall) r f v
    Exists   :: v -> Formula p t r f v -> Formula p Both r f v
    Not      ::      Formula p t r f v -> Formula (IsPrenex p t) t r f v
    And, Or, Implies :: Formula p1 t1 r f v -> Formula p2 t2 r f v
        -> Formula (IsPrenex (p1 :&&: p2) (Merge t1 t2)) (Merge t1 t2) r f v

-- | All free variables of a 'Formula'.
freeVars :: Ord v => Formula p t r f v -> Set v
freeVars (Relation _ ts) = unions (map freeVarsT ts)
freeVars (Forall x f)    = Set.delete x (freeVars f)
freeVars (Exists x f)    = Set.delete x (freeVars f)
freeVars (Not      f)    = freeVars f
freeVars (And      f g)  = freeVars f `Set.union` freeVars g
freeVars (Or       f g)  = freeVars f `Set.union` freeVars g
freeVars (Implies  f g)  = freeVars f `Set.union` freeVars g
