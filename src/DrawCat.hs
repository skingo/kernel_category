
module DrawCat where

import KernelCategory

import Data.GraphViz hiding (toDot)
import Data.Graph.Inductive

import Data.GraphViz.Attributes.Complete
import Data.Text.Lazy (pack)

import qualified Data.Set as DS
import Data.List (intercalate)
import Control.Arrow (second)

derivedToGraph :: (Show m, Show n) => DerivedCat m n -> Gr String String
derivedToGraph dc = insEdges edges $ insNodes nodes empty
   where
      obj'     = DS.toList $ obj dc
      nodes'   = zip [0..] obj'
      --  nodes    = fmap (\(i,o) -> (i, show o)) nodes'
      nodes    = fmap (second show) nodes'
      pairs    = [ (o,o') | o <- nodes', o' <- nodes' ]
      arrSets  = fmap getArrs pairs
      getArrs ((l,ln),(r,rn)) = ((l,r), arr dc ln rn)
      arrSets' = filter (not . DS.null . snd) arrSets
      --  arrList  = fmap (\(p,as) -> (p,unlines . fmap (show . DS.toList) . DS.toList $ as)) arrSets
      showSetSets = fmap (show . DS.toList) . DS.toList
      toEdges (p,as) = (fst p, snd p, unlines . showSetSets $ as)
      edges    = fmap toEdges arrSets'

kernelToGraph :: (Show m, Show n) => KernelCat m n -> Gr String String
kernelToGraph kc = insEdges edges $ insNodes nodes empty
   where
      obj'     = DS.toList $ objK kc
      nodes'   = zip [0..] obj'
      --  nodes    = fmap (\(i,o) -> (i, show o)) nodes'
      nodes    = fmap (second show) nodes'
      pairs    = [ (o,o') | o <- nodes', o' <- nodes' ]
      arrSets  = fmap getArrs pairs
      getArrs ((l,ln),(r,rn)) = ((l,r), arrK kc ln rn)
      arrSets' = filter (not . DS.null . snd) arrSets
      --  arrList  = fmap (\(p,as) -> (p,unlines . fmap (show . DS.toList) . DS.toList $ as)) arrSets
      showSetSets = fmap (show . DS.toList) . DS.toList
      toEdges (p,as) = (fst p, snd p, unlines . showSetSets $ as)
      edges    = fmap toEdges arrSets'


toDot :: Gr String String -> DotGraph Int
toDot = graphToDot (params :: GraphvizParams Int String String String String)
   where
      params   = defaultParams { fmtEdge = fe, fmtNode = fn, globalAttributes = globAttrs }
      fe (n,m,el) = [ Label $ StrLabel $ pack el ]
      fn (n,l)    = [ Label $ StrLabel $ pack l  ]
      globAttrs   = [GraphAttrs [NodeSep 1]]
      changeNodeSep (GraphAttrs gas) = GraphAttrs $ fmap changeNodeSep' gas
      changeNodeSep x = x
      changeNodeSep' (NodeSep _) = NodeSep 0.2
      changeNodeSep' (Rotate _) = Rotate 1
      changeNodeSep' x = x

drawKernel :: (FinMonoid m, FinMonoid n, Show n, Show m) => (m -> DS.Set n) -> IO FilePath
drawKernel phi
   | not $ isRelMorph phi
            = error "relation ist not a morpism"
   | not $ isFinMonoid $ DS.findMin $ preimage phi mempty
            = error "preimage is not a finite monoid"
   | not $ isFinMonoid $ DS.findMin $ phi mempty
            = error "image is not a finite monoid"
   | otherwise
            = runGraphviz (toDot $ kernelToGraph $ kernelize phi) Png "out.png"


drawDerived :: (FinMonoid m, FinMonoid n, Show n, Show m) => (m -> DS.Set n) -> IO FilePath
drawDerived phi
   | not $ isRelMorph phi
            = error "relation ist not a morpism"
   | not $ isFinMonoid $ DS.findMin $ preimage phi mempty
            = error "preimage is not a finite monoid"
   | not $ isFinMonoid $ DS.findMin $ phi mempty
            = error "image is not a finite monoid"
   | otherwise
            = runGraphviz (toDot $ derivedToGraph $ derive phi) Png "out.png"

