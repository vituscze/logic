-- | Infinite streams.
module Data.Stream
    ( Stream(..)
    , unfoldS
    , unfoldStopS
    )
where

import Control.Applicative
import Data.Function

infixr 5 :<

-- | An infinite stream of @a@s.
data Stream a
    = a :< Stream a

instance Functor Stream where
    fmap f (x :< xs) = f x :< fmap f xs

instance Applicative Stream where
    pure a = fix (a :<)
    (f :< fs) <*> (x :< xs) = f x :< (fs <*> xs)

-- | 'Stream' anamorphism.
--
-- > nats = unfoldS (\n -> (n, n + 1)) 0
-- >
-- > nats == 0 :< 1 :< 2 :< 3 :< ...
unfoldS :: (b -> (a, b)) -> b -> Stream a
unfoldS step = go
  where
    go s = x :< go s'
      where
        (x, s') = step s

-- | 'Stream' apomorphism.
--
-- > unfoldStopS (\n -> (n, Right nats)) 10 == 10 :< 0 :< 1 :< 2 :< ...
unfoldStopS :: (b -> (a, Either b (Stream a))) -> b -> Stream a
unfoldStopS step = go
  where
    go s = x :< case e of
        Left  s'  -> go s'
        Right st  -> st
      where
        (x, e) = step s
