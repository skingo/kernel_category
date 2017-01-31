{-# LANGUAGE GADTs #-}

module KernelCategory where

import qualified Data.Set as DS

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

class Category cat where
   objects :: cat o a -> DS.Set o
   arrows  :: cat o a -> o -> o -> DS.Set a
   id      :: cat o a -> o -> DS.Set a
   comp    :: cat o a -> a -> a -> a

--  image :: (FinMonoid m, FinMonoid n) => FinMonRelMorphism m n -> DS.Set n
--  image (Morph phi) = DS.fold (\m ns -> phi m `DS.union` ns) DS.empty allElems

image :: (FinMonoid m, FinMonoid n) => (m -> DS.Set n) -> DS.Set n
image phi = DS.fold (\m ns -> phi m `DS.union` ns) DS.empty allElems

preimage :: (FinMonoid m, FinMonoid n) => (m -> DS.Set n) -> n -> DS.Set m
preimage phi n = DS.filter (\m -> n `DS.member` phi m) allElems

data DerivedCat m n where
   DC :: { obj :: DS.Set n , arr :: n -> n -> DS.Set (DS.Set (m,n)), compose :: DS.Set (m,n) -> DS.Set (m,n) -> DS.Set (m,n) } -> DerivedCat m n

derive :: (FinMonoid m, FinMonoid n) => (m -> DS.Set n) -> DerivedCat m n
derive phi = DC { obj = image phi, arr = a, compose = c }
   where 
      a n n' = let   green_rs = DS.toList $ DS.filter (\n'' -> n `mappend` n'' == n) allElems
                     pairs    = concatMap (\n -> [ (m,n) | m <- DS.toList (preimage phi n) ] ) green_rs
               in undefined
      c = undefined
