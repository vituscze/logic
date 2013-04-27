{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
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

-- | Whether a formula still in a prenex normal form.
type family IsPrenex (p :: Bool) (q :: QType) :: Bool
type instance IsPrenex p None       = p
type instance IsPrenex p JustForall = False
type instance IsPrenex p Both       = False

-- | 'QType' ordering.
data Leq :: QType -> QType -> * where
    NoneFst  :: Leq None       q
    AllAll   :: Leq JustForall JustForall
    AllBoth  :: Leq JustForall Both
    BothBoth :: Leq Both       Both
