-- | A binary tree for storing quantifiers.
module Logic.PrenexTree
    ( Type(..)
    , PrenexTree(..)
    , add
    , swapWhen
    , swapAll
    , merge
    )
where

-- | Type of a quantifier together with its bound variable.
data Type a
    = F a -- ^ Universal quantifier.
    | E a -- ^ Existential quantifier.
    deriving (Eq, Ord, Show)

-- | A (quantifier) prenex tree.
--
--   Tree node stores whether the quantifiers should be swapped, list of
--   quantifiers and two subtrees, which are used for binary logical operators.
data PrenexTree a
    = Nil                                              -- ^ Empty tree.
    | Node Bool [Type a] (PrenexTree a) (PrenexTree a) -- ^ Tree node.
    deriving (Eq, Ord, Show)

-- | Adds a new quantifier to a prefix tree.
add :: Type a -> PrenexTree a -> PrenexTree a
add q Nil             = Node False [q]               Nil Nil
add q (Node b qs l r) = Node b     (swapWhen b q:qs) l   r

-- | Swaps one quantifier when the condition holds. When it doesn't, it behaves
--   as an 'id'.
swapWhen :: Bool -> Type a -> Type a
swapWhen p = if p then s else id
  where
    s (F x) = E x
    s (E x) = F x

-- | Swaps all quantifiers in a prefix tree.
swapAll :: PrenexTree a -> PrenexTree a
swapAll Nil             = Nil
swapAll (Node b qs l r) = Node (not b) qs l r

-- | Merges two prefix trees into one.
merge :: PrenexTree a -> PrenexTree a -> PrenexTree a
merge = Node False []
