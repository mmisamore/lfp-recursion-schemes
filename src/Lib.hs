module Lib
    ( ) where

import Prelude hiding (foldr,fmap,Functor)

-- | Classic foldr
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z []        = z
foldr step z (a:as) = step a (foldr step z as)

-- | A couple of examples
foldrExample1 :: Int
foldrExample1 = foldr (+) 0 [1..5]

-- | Note that we append new characters on the left, starting from end of the input list
foldrExample2 :: String
foldrExample2 = foldr (\c s -> [c] ++ s) "" ['a'..'z']

-- Reminder: Maybe a = Nothing | Just a
--
-- Some type manipulations:
-- (a -> b -> b) -> b -> r
-- = ((a,b) -> b, b) -> r
-- = (Maybe (a,b) -> b) -> r
-- The (Maybe (a,b) -> b) is an example of an *f-algebra* over "b", where f = Maybe (a,-)

-- | foldr using an "Algebra"
foldrAlg :: (Maybe (a,b) -> b) -> [a] -> b
foldrAlg alg []     = alg Nothing
foldrAlg alg (a:as) = alg (Just (a, foldrAlg alg as))

-- | Here's an example of an algebra over Int
plusAlg :: Maybe (Int,Int) -> Int
plusAlg Nothing      = 0
plusAlg (Just (a,b)) = a + b

-- | and an example of how to use it
foldrExample3 = foldrAlg plusAlg [0..5]

-- | Another example of an algebra, this time over String
concatAlg :: Maybe (Char,String) -> String
concatAlg Nothing = ""
concatAlg (Just (c,s)) = [c] ++ s

-- | and an example of how to use it
foldrExample4 = foldrAlg concatAlg ['a'..'z']

-- | Looking at the definition of foldrAlg above, we can factor out decomposition of the list:
unList :: [a] -> Maybe (a,[a])
unList []     = Nothing
unList (a:as) = Just (a,as)

-- A helper function for parallel composition
(f *** g) (x,y) = (f x, g y)

-- | Introduce Functors
class Functor f where
  fmap :: (a -> b) -> f a -> f b
  -- Must satisfy Laws to be valid:
  -- 1. fmap id fa = fa
  -- 2. fmap g . fmap f = fmap (g . f)

-- | Standard functor instance for Maybe
instance Functor Maybe where
  fmap f Nothing  = Nothing
  fmap f (Just a) = Just (f a)

-- | A fancier version of foldr
foldrAlg1 :: (Maybe (a,b) -> b) -> [a] -> b
foldrAlg1 alg = alg . fmap (id *** foldrAlg1 alg) . unList
-- unList [a] :: Maybe (a, [a])
-- apply: fmap (id *** foldrAlg1 alg) gives Maybe (a, b)
-- apply: alg to Maybe (a,b) gives "b"

-- Consider a type defined by r = Maybe (a,r). What could this be?
-- By recursing on r, we get:
-- r = Maybe (a,r) = Maybe (a, Maybe (a,r)) = Maybe (a, Maybe (a, Maybe (a,r)))
-- At any point, we might get Nothing or another pair of (a,r), and we continue on "r"
-- | Define the fixed point of any functor f
newtype Fix f = Fix { unFix :: f (Fix f) }

-- | Observation: Maybe (a, r) is a functor with respect to r, and its fixed point is [a]
data ListF a r = Empty | Cons a r -- = Maybe (a,r)
  deriving (Show)
instance Functor (ListF a) where
  fmap f Empty      = Empty
  fmap f (Cons a r) = Cons a (f r)

-- | [a] is just the fixed point of ListF a.
--   ListF is called a "pattern functor"
type List a = Fix (ListF a)

-- A helper function to turn ordinary lists into fixed point representation
list :: [a] -> List a
list []     = Fix Empty
list (a:as) = Fix (Cons a (list as))

-- | Given any algebra for ListF with carrier b, we can reduce Fix (ListF a) = List a to b
foldrAlg2 :: (ListF a b -> b) -> List a -> b
foldrAlg2 alg = alg . fmap (foldrAlg2 alg) . unFix

-- | Obviously this applies to more than just Lists. "r" always stands for the "rest" of
--   the structure, and we want to be a functor with respect to "r" (not "a")
data TreeF a r = EmptyTree | Branch a r r
instance Functor (TreeF a) where
  fmap f EmptyTree = EmptyTree
  fmap f (Branch a l r) = Branch a (f l) (f r)

-- | A Tree as the fixed point of a pattern functor
type Tree a  = Fix (TreeF a)
emptyTree    = Fix EmptyTree
branch a l r = Fix (Branch a l r)

-- | Algebra for computing height of a tree
heightAlg1 :: TreeF a Int -> Int
heightAlg1 EmptyTree        = -1
heightAlg1 (Branch _ r1 r2) = (max r1 r2) + 1

-- | Algebra for computing sum of elements of a tree
treeSumAlg1 :: TreeF Int Int -> Int
treeSumAlg1 EmptyTree        = 0
treeSumAlg1 (Branch a r1 r2) = a + r1 + r2

-- | Now here's something we can do in general:
cata :: Functor f => (f b -> b) -> Fix f -> b
cata alg = alg . fmap (cata alg) . unFix
-- Taking f b = ListF a b recovers foldr for List a
-- Think of this like a bottom-up reducer for the data structure

-- | Algebra for summing List elements
plusAlg1 :: ListF Int Int -> Int
plusAlg1 Empty      = 0
plusAlg1 (Cons a b) = a + b

-- | Algebra for products of List elements
multAlg1 :: ListF Int Int -> Int
multAlg1 Empty      = 1
multAlg1 (Cons a b) = a * b

-- | Some examples
foldrExample5 = cata plusAlg1 (list [1..5])
foldrExample6 = cata multAlg1 (list [1..5])
foldrExample7 = cata heightAlg1 emptyTree
foldrExample8 = cata heightAlg1 (branch 'a' emptyTree emptyTree)
foldrExample9 = cata heightAlg1
  (branch 'a'
    (branch 'b' emptyTree emptyTree)
    (branch 'c'
      (branch 'd' emptyTree emptyTree)
      emptyTree)
  )

-- | Why are algebras useful? We can compose them:
algProd :: Functor f => (f a -> a) -> (f b -> b) -> (f (a,b) -> (a,b))
algProd alg1 alg2 = (alg1 *** alg2) . funzip where
  funzip fab      = (fmap fst fab, fmap snd fab)

-- | Example of products for f-algebras
foldrExample10 = cata (plusAlg1 `algProd` multAlg1) (list [1..5])
foldrExample11 = cata (heightAlg1 `algProd` treeSumAlg1)
  (branch 1 (branch 2 emptyTree emptyTree) (branch 3 (branch 4 emptyTree emptyTree) emptyTree))

-- | So far, we just know how to analyze data down to answers. How do we synthesize
--   new data from a starting point?
unfoldr :: (b -> Maybe (a,b)) -> b -> [a]
unfoldr coalg b =
  case coalg b of
    Nothing -> []
    Just (a',b') -> a' : unfoldr coalg b'

-- | Here, b -> Maybe (a,b) is an *f-coalgebra* with carrier "b" where f = Maybe (a,-)

-- | Examples
replicate k x = unfoldr (\n -> if n <= 0 then Nothing else Just (x,n-1)) k
splitOn p = unfoldr (
  \s -> if s == ""
           then Nothing
           else Just (takeWhile (not . p) s, drop 1 (dropWhile (not . p) s)))

-- | Let's cut to the chase:
ana :: Functor f => (b -> f b) -> b -> Fix f
ana coalg = Fix . fmap (ana coalg) . coalg

-- | Tree pattern functor for splitting lists in half
data SplitF a r = EmptySplit | Leaf a | Bin r r
  deriving (Show)
instance Functor (SplitF a) where
  fmap f EmptySplit = EmptySplit
  fmap f (Leaf a)   = Leaf a
  fmap f (Bin l r)  = Bin (f l) (f r)

-- | A coalgebra to split lists in half
splitCoAlg :: [a] -> SplitF a [a]
splitCoAlg []  = EmptySplit
splitCoAlg [a] = Leaf a
splitCoAlg as  = let (xs,ys) = splitAt (length as `div` 2) as
                  in Bin xs ys

-- | An algebra so we can see how we've split
splitString :: Show a => SplitF a String -> String
splitString EmptySplit = "[]"
splitString (Leaf a)   = "[" ++ show a ++ "]"
splitString (Bin l r)  = "(" ++ l ++ "," ++ r ++ ")"

-- | Splitting example
splitExample = cata splitString (ana splitCoAlg [20,19..1])

-- | Fixed point of the splitting functor
type Split a = Fix (SplitF a)

-- | Core of merge sort: merge two sorted lists
mergeLists :: Ord a => [a] -> [a] -> [a]
mergeLists [] [] = []
mergeLists [] ys = ys
mergeLists xs [] = xs
mergeLists ts@(x:xs) zs@(y:ys) =
  if x <= y then x : mergeLists xs zs
            else y : mergeLists ts ys

-- | The corresponding f-algebra for merging sorted lists
merge :: Ord a => SplitF a [a] -> [a]
merge EmptySplit  = []
merge (Leaf a)    = [a]
merge (Bin as bs) = mergeLists as bs

-- | Compose any f-algebra with f-coalgebra to get a map on the carriers
hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo alg coalg = alg . fmap (hylo alg coalg) . coalg
-- Alternatively:
-- hylo alg coalg = cata alg . ana coalg
--  = alg . fmap (cata alg) . unFix . Fix . fmap (ana coalg) . coalg
--  = alg . fmap (cata alg) . fmap (ana coalg) . coalg
--  = alg . fmap (cata alg . ana coalg) . coalg
--  = alg . fmap (hylo alg coalg) . coalg
-- We have fused away the intermediate Fix f data structure!

-- | Merge sort
mergeSort :: Ord a => [a] -> [a]
mergeSort = hylo merge splitCoAlg


-- Catamorphism Fusion Law:
-- By definition, cata alg = alg . fmap (cata alg) . unFix
-- Suppose f :: f a -> a, g :: f b -> b, h :: a -> b
-- Suppose also that h . f = g . fmap h (i.e. h induces an algebra homomorphism)
-- Then h . cata f = cata g
--
-- Equational proof assuming uniqueness of fixed points:
-- Observe that cata g = g . fmap (cata g) . unFix, so g is a fixed point of the equation
-- X = g . fmap X . unFix
-- Then h . cata f = h . f . fmap (cata f) . unFix
-- = g . fmap h . fmap (cata f) . unFix
-- = g . fmap (h . cata f) . unFix
-- so h . cata f is a fixed point of the same equation. By uniqueness of fixed points,
-- h . cata f = cata g.
--
-- There is also a direct category-theoretic proof, but the equational proof is advantageous
-- for clarifying the role of fixed points. If the cost of h (in time or memory)
-- is proportional to the size of its input then this law sometimes leads to a performance
-- gain.

-- Catamorphism Compose Law:
-- Suppose h :: g a -> f a, f :: f a -> a
-- Then cata f . cata (Fix . h) = cata (f . h)
--
-- Equational proof assuming uniqueness of fixed points:
-- By parametricity, h is a natural transformation so in particular
-- fmap (cata f) . h = h . fmap (cata f)
-- Observe that cata (f . h) is a solution to the equation X = f . h . fmap X . unFix.
-- Now consider
-- f . h . fmap (cata f . cata (Fix . h)) . unFix
-- = f . h . fmap (f . fmap (cata f) . unFix . Fix . h . fmap (cata (Fix.h)) . unFix) . unFix
-- = f . h . fmap (f . fmap (cata f) . h . fmap (cata (Fix.h)) . unFix) . unFix
-- = f . h . fmap (f . h . fmap (cata f) . fmap (cata (Fix.h)) . unFix) . unFix
-- = f . h . fmap (f . h . fmap (cata f . cata (Fix.h)) . unFix) . unFix
-- So cata f . cata (Fix . h) is also a fixed point of the same equation. By uniqueness of
-- fixed points, cata f . cata (Fix . h) = cata (f . h)
--
-- The categorical statement of this is roughly that catamorphisms respect natural transformations.
-- The computational import is that we can fuse together two catamorphisms into a single traversal,
-- eliminating the intermediate Fix f structure.
-- Here's a famous special case: in the above, let a = Fix f, g = f. Then:
-- h :: f (Fix f) -> f (Fix f)
-- f :: f (Fix f) -> Fix f
-- Let g = Fix . h so g :: f (Fix f) -> Fix f
-- Therefore cata f . cata g = cata (f . h) = cata (f . unFix . g).

