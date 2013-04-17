{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs          #-}
module Logic.Formula.GADT where

import Logic.Formula.Spec
import Logic.Term

data Formula :: FType -> * -> * -> * -> * where
    Relation :: r -> [Term f v]      -> Formula (T None True) r f v
    Forall   :: v -> Formula t r f v -> Formula (AddForall t) r f v
    Exists   :: v -> Formula t r f v -> Formula (AddExists t) r f v
    Not      :: v -> Formula t r f v -> Formula (AddUnary  t) r f v
    And      :: Formula t1 r f v -> Formula t2 r f v
             -> Formula (AddBinary t1 t2) r f v
    Or       :: Formula t1 r f v -> Formula t2 r f v
             -> Formula (AddBinary t1 t2) r f v
    Implies  :: Formula t1 r f v -> Formula t2 r f v
             -> Formula (AddBinary t1 t2) r f v
