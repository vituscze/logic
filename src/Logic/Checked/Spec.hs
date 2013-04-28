{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Type level specification of a formula type.
module Logic.Checked.Spec where

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

-- | Singleton for 'QType'.
data QTypeSing :: QType -> * where
    NoneS       :: QTypeSing None
    JustForallS :: QTypeSing JustForall
    BothS       :: QTypeSing Both

-- | Convenience class for 'QType' singleton.
class QTypeC (t :: QType) where
    auto :: QTypeSing t

instance QTypeC None where
    auto = NoneS

instance QTypeC JustForall where
    auto = JustForallS

instance QTypeC Both where
    auto = BothS

-- | Merges two quantifier types into one.
type family Merge (x :: QType) (y :: QType) :: QType
type instance Merge None       y          = y
type instance Merge JustForall None       = JustForall
type instance Merge JustForall JustForall = JustForall
type instance Merge JustForall Both       = Both
type instance Merge Both       y          = Both

-- | A variant of 'Merge' that works on 'QType' singletons.
mergeSing :: QTypeSing t1 -> QTypeSing t2 -> QTypeSing (Merge t1 t2)
mergeSing NoneS       t           = t
mergeSing JustForallS NoneS       = JustForallS
mergeSing JustForallS JustForallS = JustForallS
mergeSing JustForallS BothS       = BothS
mergeSing BothS       _           = BothS

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

-- Few lemmas.

-- | 'Leq' is reflexive.
tRefl :: QTypeSing t -> Leq t t
tRefl NoneS       = NoneFst
tRefl JustForallS = AllAll
tRefl BothS       = BothBoth

-- | 'Merge' 'JustForall' respects 'Leq' in the second argument.
mergeLeq :: QTypeSing t1 -> QTypeSing t2 -> Leq t1 t2
         -> Leq t1 (Merge t2 JustForall)
mergeLeq NoneS       _           _  = NoneFst
mergeLeq JustForallS NoneS       _  = AllAll
mergeLeq JustForallS JustForallS pf = pf
mergeLeq JustForallS BothS       pf = pf
mergeLeq BothS       NoneS       _  = undefined -- 'pf' is empty.
mergeLeq BothS       JustForallS pf = pf
mergeLeq BothS       BothS       pf = pf

-- | 'Both' is maximal element of 'Leq' ordering.
bothMax :: QTypeSing t -> Leq t Both
bothMax NoneS       = NoneFst
bothMax JustForallS = AllBoth
bothMax BothS       = BothBoth
