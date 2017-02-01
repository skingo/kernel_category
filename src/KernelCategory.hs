{-# LANGUAGE GADTs #-}

module KernelCategory where

import qualified Data.Set as DS
import Data.List (intercalate)

newtype Pairwise a = Pairwise { unPairwise :: DS.Set a }
   deriving (Eq,Ord)

instance (Monoid m, Ord m) => Monoid (Pairwise m) where
   mempty = Pairwise $ DS.singleton mempty
   ms1 `mappend` ms2 = Pairwise $ DS.fromList [ m1 `mappend` m2 | m1 <- DS.toList (unPairwise ms1), m2 <- DS.toList (unPairwise ms2) ]

class (Ord m, Monoid m) => FinMonoid m where
   allElems :: DS.Set m

--  data FinMonRelMorphism m n where
   --  Morph :: (Monoid m, Monoid n) => { morph :: m -> DS.Set n } -> FinMonRelMorphism m n

isRelMorph :: (FinMonoid m, FinMonoid n) => (m -> DS.Set n) -> Bool
isRelMorph phi =  mempty `DS.member` phi mempty
                  &&
                  let pairs = [ (m1,m2) | m1 <- DS.toList allElems, m2 <- DS.toList allElems ]
                      checkMul (m1,m2) = unPairwise (Pairwise (phi m1) `mappend` Pairwise (phi m2)) `DS.isSubsetOf` phi (m1 `mappend` m2)
                  in all checkMul pairs


isMorph :: (FinMonoid m, FinMonoid n) => (m -> n) -> Bool
isMorph = isRelMorph . morphToRelMorph

morphToRelMorph :: (FinMonoid m, FinMonoid n) => (m -> n) -> (m -> DS.Set n)
morphToRelMorph = (.) DS.singleton

isFinMonoid :: (FinMonoid m) => m -> Bool
isFinMonoid n = if n `elem` elems
                then hasUnit && isAssoc && isClosed
                else error "the specified element is not part of the finite monoid"
   where
      elems   = DS.toList allElems
      pairs   = [ (m, m') | m <- elems, m' <- elems ]
      triples = [ (m, m', m'') | m <- elems, m' <- elems, m'' <- elems ]
      hasUnit = all (\m -> mempty `mappend` m == m && m `mappend` mempty == m) elems
      isAssoc = all (\(m,m',m'') -> (m `mappend` m') `mappend` m'' == m `mappend` (m' `mappend` m'')) triples
      isClosed = all (\(m,m') -> m `mappend` m' `DS.member` allElems) pairs


class Category cat where
   objects :: cat o a -> DS.Set o
   arrows  :: cat o a -> o -> o -> DS.Set a
   id      :: cat o a -> o -> DS.Set a
   comp    :: cat o a -> o -> o -> o -> a -> a -> a

--  image :: (FinMonoid m, FinMonoid n) => FinMonRelMorphism m n -> DS.Set n
--  image (Morph phi) = DS.fold (\m ns -> phi m `DS.union` ns) DS.empty allElems

image :: (FinMonoid m, FinMonoid n) => (m -> DS.Set n) -> DS.Set n
image phi = DS.fold (\m ns -> phi m `DS.union` ns) DS.empty allElems

preimage :: (FinMonoid m, FinMonoid n) => (m -> DS.Set n) -> n -> DS.Set m
preimage phi n = DS.filter (\m -> n `DS.member` phi m) allElems

data DerivedCat m n where
   DC :: { obj :: DS.Set n , arr :: n -> n -> DS.Set (DS.Set (m,n)), compose :: n -> n -> n -> DS.Set (m,n) -> DS.Set (m,n) -> DS.Set (m,n) } -> DerivedCat m n

instance (Show m, Show n) => Show (DerivedCat m n) where
   show dc = let  objs     = DS.toList $ obj dc
                  arrs     = fmap (\(n,n') -> ((n, n'), arr dc n n')) [ (n, n') | n <- objs, n' <- objs ]
                  arrList  = fmap (\((n, n'), as) -> "\t" ++ show n ++ ", " ++ show n' ++ ":\t" ++ intercalate "\n\t\t\t" (fmap (show . DS.toList) (DS.toList as))) arrs
             in "Objects:\n\t" ++ show objs ++ "\nArrows:\n" ++ unlines arrList

derive :: (FinMonoid m, FinMonoid n) => (m -> DS.Set n) -> DerivedCat m n
derive phi = DC { obj = obj', arr = a, compose = c }
   where
      a n n' = let   green_rs = DS.toList $ DS.filter (\n'' -> n `mappend` n'' == n') allElems
                     pairs    = concatMap (\n'' -> [ (m,n'') | m <- DS.toList (preimage phi n'') ] ) green_rs
                     preImg   = DS.toList $ preimage phi n
                     inducedFct  = fmap (\p -> (p, fmap (\m -> m `mappend` fst p) preImg)) pairs
                     classify [] (p, img) = [(DS.singleton p, img)]
                     classify ((ps, img'):cs) (p, img)
                        | img == img'  = (p `DS.insert` ps, img):cs
                        | otherwise    = (ps, img'):classify cs (p, img)
                     classes  = foldl classify [] inducedFct
               in DS.fromList $ fmap fst classes
      obj'  = image phi
      c sr m el l r  =  let   prod     = unPairwise $ Pairwise r `mappend` Pairwise l
                              arrs     = DS.toList $ a sr el
                              cands    = filter (prod `DS.isSubsetOf`) arrs
                              lValid   = l `elem` a m el
                              rValid   = r `elem` a sr m
                        in case (lValid, rValid) of
                           (False, False) -> error "both arrows are invalid"
                           (True,  False) -> error "left arrow is invalid"
                           (False, True ) -> error "right arrow is invalid"
                           (True,  True ) ->  case cands of
                              []  -> error "no product found"
                              [x] -> x
                              _   -> error "too many products possible"



data KernelCat m n where
   KC :: { objK :: DS.Set (n,n) , arrK :: (n,n) -> (n,n) -> DS.Set (DS.Set (m,n)), composeK :: (n,n) -> (n,n) -> (n,n) -> DS.Set (m,n) -> DS.Set (m,n) -> DS.Set (m,n) } -> KernelCat m n

instance (Show m, Show n) => Show (KernelCat m n) where
   show kc = let  objs     = DS.toList $ objK kc
                  arrs     = fmap (\(n,n') -> ((n, n'), arrK kc n n')) [ (n, n') | n <- objs, n' <- objs ]
                  arrList  = fmap (\((n, n'), as) -> "\t" ++ show n ++ ", " ++ show n' ++ ":\t" ++ intercalate "\n\t\t\t" (fmap (show . DS.toList) (DS.toList as))) arrs
             in "Objects:\n\t" ++ show objs ++ "\nArrows:\n" ++ unlines arrList

kernelize :: (FinMonoid m, FinMonoid n) => (m -> DS.Set n) -> KernelCat m n
kernelize phi = KC { objK = obj', arrK = a, composeK = c }
   where
      a (nl, nr) (nl', nr') =
         let   connectors  = DS.toList $ DS.filter (\n -> nl `mappend` n == nl' && nr == n `mappend` nr') allElems
               pairs       = concatMap (\n' -> [ (m,n') | m <- DS.toList (preimage phi n') ] ) connectors
               preImgL     = DS.toList $ preimage phi nl
               preImgR     = DS.toList $ preimage phi nr'
               prePairs    = [ (ml, mr) | ml <- preImgL, mr <- preImgR ]
               inducedFct  = fmap (\p -> (p, fmap (\(ml,mr) -> ml `mappend` fst p `mappend` mr) prePairs)) pairs
               classify [] (p, img) = [(DS.singleton p, img)]
               classify ((ps, img'):cs) (p, img)
                  | img == img'  = (p `DS.insert` ps, img):cs
                  | otherwise    = (ps, img'):classify cs (p, img)
               classes  = foldl classify [] inducedFct
         in DS.fromList $ fmap fst classes
      --  a n n' = let   green_rs = DS.toList $ DS.filter (\n'' -> n `mappend` n'' == n') allElems
                     --  pairs    = concatMap (\n'' -> [ (m,n'') | m <- DS.toList (preimage phi n'') ] ) green_rs
                     --  preImg   = DS.toList $ preimage phi n
                     --  inducedFct  = fmap (\p -> (p, fmap (\m -> m `mappend` fst p) preImg)) pairs
                     --  classify [] (p, img) = [(DS.singleton p, img)]
                     --  classify ((ps, img'):cs) (p, img)
                        --  | img == img'  = (p `DS.insert` ps, img):cs
                        --  | otherwise    = (ps, img'):classify cs (p, img)
                     --  classes  = foldl classify [] inducedFct
               --  in DS.fromList $ fmap fst classes
      img  = DS.toList $ image phi
      obj' = DS.fromList [ (n,n') | n <- img, n' <- img ]
      c sr m el l r  =  let   prod     = unPairwise $ Pairwise r `mappend` Pairwise l
                              arrs     = DS.toList $ a sr el
                              cands    = filter (prod `DS.isSubsetOf`) arrs
                              lValid   = l `elem` a m el
                              rValid   = r `elem` a sr m
                        in case (lValid, rValid) of
                           (False, False) -> error "both arrows are invalid"
                           (True,  False) -> error "left arrow is invalid"
                           (False, True ) -> error "right arrow is invalid"
                           (True,  True ) ->  case cands of
                              []  -> error "no product found"
                              [x] -> x
                              _   -> error "too many products possible"



--------------------------
------  playground -------
--------------------------


data U1 = U0 | U1
   deriving (Eq,Ord)

instance Show U1 where
   show U0 = "0_U"
   show U1 = "1_U"

instance Monoid U1 where
   mempty = U1
   U1 `mappend` x  = x
   x  `mappend` U1 = x
   U0 `mappend` U0 = U0

instance FinMonoid U1 where
   allElems = DS.fromList [U0, U1]

data Z2 = Z0 | Z1
   deriving (Eq,Ord)

instance Show Z2 where
   show Z0 = "0_Z"
   show Z1 = "1_Z"

instance Monoid Z2 where
   mempty = Z0
   Z0 `mappend` x  = x
   x  `mappend` Z0 = x
   Z1 `mappend` Z1 = Z0

instance FinMonoid Z2 where
   allElems = DS.fromList [Z0, Z1]

newtype Trunc = Trunc Int
   deriving (Eq,Ord)

instance Show Trunc where
   show (Trunc n) = show n ++ "_T"

truncationLevel :: Int
truncationLevel = 3

instance Monoid Trunc where
   mempty = Trunc 0
   (Trunc n) `mappend` (Trunc m) = Trunc $ min (n+m) truncationLevel

instance FinMonoid Trunc where
   allElems = DS.fromList $ fmap Trunc [0 .. truncationLevel]

simpleMorph :: U1 -> DS.Set Z2
simpleMorph U0 = DS.fromList [ Z0, Z1 ]
simpleMorph U1 = DS.singleton Z0

truncMorph :: Z2 -> DS.Set Trunc
truncMorph Z0 = DS.fromList $ fmap Trunc [0,2,3]
truncMorph Z1 = DS.fromList $ fmap Trunc [1,3]

--  truncMorph :: Z2 -> DS.Set Trunc
--  truncMorph Z0 = DS.fromList $ fmap Trunc [0,2,4,5]
--  truncMorph Z1 = DS.fromList $ fmap Trunc [1,3,5]

