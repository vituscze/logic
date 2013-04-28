{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
module Logic.GADT where

import Logic.Formula.GADT
import Logic.Formula.Spec
import Logic.PrenexTree

data PrependResult :: Bool -> QType -> * -> * -> * -> * where
    Some :: QTypeSing t -> Formula p t r f v -> Leq tOut t
         -> PrependResult p tOut r f v

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

remove :: Formula p t r f v -> (Formula True None r f v, PrenexTree v)
remove (Relation r ts) = (Relation r ts, Nil)
remove (Forall x f)   = mapPair id (add (F x)) (remove f)
remove (Exists x f)   = mapPair id (add (E x)) (remove f)
remove (Not      f)   = mapPair Not swapAll (remove f)
remove (And      f g) = zipPair And merge (remove f) (remove g)
remove (Or       f g) = zipPair Or  merge (remove f) (remove g)
remove (Implies  f g) = zipPair Implies (merge . swapAll) (remove f) (remove g)
