{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Type level specification of a formula type.
module Logic.Formula.Spec where

infixr 3 :&&:

-- | Type level conjunction.
type family (:&&:) (a :: Bool) (b :: Bool) :: Bool
type instance (:&&:) True  True  = True
type instance (:&&:) False b     = False
type instance (:&&:) a     False = False

-- | Data type specifying what kind of quantifiers may a formula contain.
data QType
    = None
    | JustForall
    | Both
    deriving (Eq, Ord, Show)

-- | Type of a formula. At the moment, the 'Bool' field represents a prenex
--   flag.
data FType
    = T QType Bool
    deriving (Eq, Ord, Show)

-- | Merges two quantifier types into one.
type family Merge (x :: QType) (y :: QType) :: QType
type instance Merge None       y          = y
type instance Merge JustForall None       = JustForall
type instance Merge JustForall JustForall = JustForall
type instance Merge JustForall Both       = Both
type instance Merge Both       y          = Both

-- | Whether 'QType' specifies a quantifier-free formula.
type family QFree (q :: QType) :: Bool
type instance QFree None       = True
type instance QFree JustForall = False
type instance QFree Both       = False

-- | What kind of formula does 'Forall' produce.
type family AddForall (f :: FType) :: FType
type instance AddForall (T q p) = T (Merge q JustForall) p

-- | What kind of formula does 'Exists' produce.
type family AddExists (f :: FType) :: FType
type instance AddExists (T q p) = T Both p

-- | What kind of formula does 'Not' produce.
type family AddUnary (f :: FType) :: FType
type instance AddUnary (T q p) = T q (p :&&: QFree q)

-- | What kind of formula do 'And', 'Or' and 'Implies' produce.
type family AddBinary (f1 :: FType) (f2 :: FType) :: FType
type instance AddBinary (T q1 p1) (T q2 p2) =
    T (Merge q1 q2) (p1 :&&: p2 :&&: QFree (Merge q1 q2))

-- | Formula contains some kind of quantifier.
type ContainsQ q = QFree q ~ False
