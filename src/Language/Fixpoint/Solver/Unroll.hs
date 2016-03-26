{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Fixpoint.Solver.Unroll (unroll) where

import           Control.Comonad
import           Data.Bifunctor
import           Data.Bifoldable
import           Data.Bitraversable

import qualified Control.Arrow as A
import           GHC.Exts (groupWith)

import           Data.Hashable
import qualified Data.HashMap.Strict              as M
import           Control.Monad.State

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.SubstKV
import qualified Language.Fixpoint.Types.Visitor as V

--------------------------------------------------------
unroll :: forall a. Int -> SInfo a -> Integer -> SInfo a
--------------------------------------------------------
unroll depth fi start = fi {cm = M.fromList cons', bs = be, ws = M.fromList $ we ++ M.toList (ws fi)}
  where (tree,be) = unroll' depth fi start
        cons' = (\(b,a) -> (b, a { _cid = Just b })) <$> foldr (:) [] tree
        (we,_) = runState wfcs (bs fi, M.size (cm fi))

        wfcs :: State (BindEnv, Int) [(KVar,WfC a)]
        wfcs = mapM renameWfC [ (wfc,i) | wfc <- M.toList (ws fi), i<- [0..(depth+1)]]

renameWfC ((kv,wfc),i) = (kv',) <$> substKV [(kv, kv')] wfc
  where kv' = renameKv kv i

renameKv :: Integral i => KVar -> i -> KVar
-- |"k" -> n -> "k_n"
renameKv a i = KV $ renameSymbol (kv a) $ fromIntegral i

unroll' :: Int -> SInfo a0 -> Integer -> (Node (KVar, Int) (Integer, SimpC a0), BindEnv)
unroll' depth fi start = (tree',be)
  where m = cm fi

        mlookup v = M.lookupDefault (error $"cons # "++show v++" not found") v $ M.insert 0 emptycons m
        klookup k = M.lookupDefault [0] k $ M.fromList $ (fst . head A.&&& (snd <$>)) <$> groupWith fst pairs
          where pairs = [(k,i)|(i,ks) <- A.second rhsKVars <$> M.toList m, k<-ks]

        emptycons = cons1 { _cenv = emptyIBindEnv, _crhs = PTrue }
          where cons1 = headError "no constraints" $ M.elems m

        tree = Node (start,0) (prune depth . index M.empty . ana klookup kenv <$> kenv start)
        treeofsubs = dup [(KV nonSymbol, KV nonSymbol)] $ kvarSubs <<= tree
        treesubs = prime (\v s -> substKV s $ mlookup v) <$> treeofsubs
        (tree',(be,_)) = flip runState (bs fi, M.size m) $ sequenceA treesubs

        kenv = lhsKVars (bs fi) . mlookup

rhsKVars :: SimpC a -> [KVar]
rhsKVars = V.kvars . crhs

lhsKVars :: BindEnv -> SimpC a -> [KVar]
lhsKVars = V.envKVars

-- probably pretty inefficent
kvarSubs :: Node (KVar, Int) a -> (a,[(KVar,KVar)])
-- |Lists all the subsitutions that are to made
kvarSubs t@(Node a _) = (a, reverse subs)
  where subs = bifoldr (:) (flip const) [] tree
        tree = (\(k,i) -> (k,renameKv k i)) `first` t

prime :: ( a -> s -> State (e, Int) b ) -> ((a, Int), s) -> State (e, Int) (Integer, b)
-- |Builds our new constraint graph, now knowing the substitutions.
prime sub ((v,_),su) = modify (A.second (+1)) >> ((,) <$> (fromIntegral . snd <$> get) <*> sub v su)

dup :: [c] -> Node b (a,[c]) -> Node b (a,[c])
dup c (Node (a,[]) bs) = Node (a,c) bs
dup c (Node (a,cs) bs) = Node (a,c ++ cs) [Node b $ dup [head cs] <$> as | Node b as <- bs]

data Node b a = Node a [Node a b] deriving Show

ana :: (Show b , Show a) => (b -> [a]) -> (a -> [b]) -> b -> Node a b
ana vs ks k = Node k [Node v $ ana vs ks <$> ks v | v <- vs k]

index :: (Eq a, Hashable a) => M.HashMap a Int -> Node b a -> Node (b,Int) (a,Int)
-- |Number each node by the number of ancestors it has that hae the same label
index m (Node a bs) = Node (a,i) [Node (b,i) (index m' <$> ns) | Node b ns <- bs]
  where i = M.lookupDefault 0 a m
        m' = M.insertWith (+) a 1 m

prune :: Int -> Node a (b,Int) -> Node a (b,Int)
-- |Removes all nodes numbered higher than `depth`
prune depth (Node (a,i) l) = Node (a,i) $
  if i>depth
     then []
     else [Node v (prune depth <$> ns) | Node v ns <- l]

instance Bifunctor Node where
  bimap f g (Node a bs) = Node (g a) (bimap g f <$> bs)

instance Bifoldable Node where
  bifoldMap f g (Node a bs) = g a `mappend` foldMap (bifoldMap g f) bs

instance Bitraversable Node where
  bitraverse f g (Node a bs) = Node <$> g a <*> traverse (bitraverse g f) bs

instance Comonad (Node b) where
  extract (Node a _) = a
  duplicate t@(Node _ bs) = Node t [Node b (duplicate <$> as) | Node b as <- bs]

-- Why aren't these defined in Data.Bifunctor?
instance Bifunctor p => Functor (p b) where
  fmap = second

instance Bifoldable p => Foldable (p b) where
  foldMap = bifoldMap (const mempty)

instance (Bitraversable p, Bifunctor p) => Traversable (p b) where
  traverse = bitraverse pure

headError _ (x:_) = x
headError s _  = error s

{-
traceDrawId n = trace (unlines $ draw n) n

-- based on `draw` from Data.Tree
draw :: (Show a,Show b) => Node a b -> [String]
draw (Node x ts0) = show x : drawSubTrees ts0
  where
    drawSubTrees [] = []
    drawSubTrees [t] =
        "|" : shift "`--" "   " (draw t)
    drawSubTrees (t:ts) =
        "|" : shift "+--" "|  " (draw t) ++ drawSubTrees ts
    shift first other = zipWith (++) (first : repeat other)
-}
