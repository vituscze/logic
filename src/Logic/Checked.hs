{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
-- | Compiler checked transformation into prenex normal form.
module Logic.Checked
    ( PrependResult(..)
    , prepend
    , remove
    , rename
    )
where

import qualified Data.Map as Map

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Data.Map (Map)
import Data.Traversable

import Data.Stream
import Logic.Checked.Formula
import Logic.Checked.Spec
import Logic.PrenexTree
import Logic.Term

-- | A type of formulas produced by 'prepend'.
--
--   Note that the actual type of quantifiers contained in the resulting formula
--   is existentially hidden. Therefore, 'Some' contains a proof that 'prepend'
--   didn't return a formula that contains less quantifiers than the original
--   one.
data PrependResult :: Bool -> QType -> * -> * -> * -> * where
    Some :: QTypeSing t -> Formula p t r f v -> Leq tOut t
         -> PrependResult p tOut r f v

-- | Prepend a list of quantifiers in front of a given formula.
prepend :: QTypeSing t -> [Type v] -> Formula p t r f v
        -> PrependResult p t r f v
prepend t [] f = Some t f (tRefl t)
prepend t (F x:qs) f = case prepend t qs f of
    Some t' f' pf -> Some (mergeSing t' JustForallS) (Forall x f')
        (mergeLeq t t' pf)
prepend t (E x:qs) f = case prepend t qs f of
    Some _ f' _ -> Some BothS (Exists x f') (bothMax t)

mapPair :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
mapPair f g (x, y) = (f x, g y)

zipPair :: (a -> c -> e) -> (b -> d -> f) -> (a, b) -> (c, d) -> (e, f)
zipPair f g (x1, y1) (x2, y2) = (f x1 x2, g y1 y2)

-- | Extracts all quantifiers from a formula into 'PrenexTree'.
remove :: Formula p t r f v -> (Formula True None r f v, PrenexTree v)
remove (Relation r ts) = (Relation r ts, Nil)
remove (Forall x f)   = mapPair id (add (F x)) (remove f)
remove (Exists x f)   = mapPair id (add (E x)) (remove f)
remove (Not      f)   = mapPair Not swapAll (remove f)
remove (And      f g) = zipPair And merge (remove f) (remove g)
remove (Or       f g) = zipPair Or  merge (remove f) (remove g)
remove (Implies  f g) = zipPair Implies (merge . swapAll) (remove f) (remove g)

-- Renaming helpers.
type RenameM v v' a = ReaderT (Map v v') (State (Stream v')) a

localInsert :: Ord v => v -> RenameM v v' a -> RenameM v v' (Either v v', a)
localInsert s m = do
    s' <- state (\(x :< xs) -> (x,xs))
    a  <- local (Map.insert s s') m
    return (Right s', a)

updateVar :: Ord v => v -> RenameM v v' (Either v v')
updateVar v = maybe (Left v) Right . Map.lookup v <$> ask

-- | Rename all bound variables to a unique name.
rename :: Ord v => Stream v' -> Formula p t r f v
       -> Formula p t r f (Either v v')
rename vs f' = evalState (runReaderT (go f') Map.empty) vs
  where
    go :: Ord v => Formula p t r f v
       -> RenameM v v' (Formula p t r f (Either v v'))
    go (Relation r ts) = Relation r <$> traverse goT ts
    go (Forall x f)   = uncurry Forall <$> localInsert x (go f)
    go (Exists x f)   = uncurry Exists <$> localInsert x (go f)
    go (Not      f)   = Not     <$> go f
    go (And      f g) = And     <$> go f <*> go g
    go (Or       f g) = Or      <$> go f <*> go g
    go (Implies  f g) = Implies <$> go f <*> go g

    goT (Var x)         = Var        <$> updateVar x
    goT (Function f ts) = Function f <$> traverse goT ts
