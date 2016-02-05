{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections#-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Fixpoint.Solver.Unroll (unroll) where

import           Data.Hashable
import           Data.Bifunctor
import           Control.Monad.State
import           Control.Comonad
import qualified Control.Arrow as A
-- import           Language.Fixpoint.Types.Names (renameSymbol, nonSymbol)
import qualified Language.Fixpoint.Types.Visitor as V
import           GHC.Exts (groupWith)

-- import           Language.Fixpoint.Config
import           Language.Fixpoint.Types
import qualified Data.HashMap.Strict              as M
import Debug.Trace

data Node b a = Node a [Node a b] deriving Show

data NodeR a b = Rev (Node b a) deriving Show

instance Bifunctor Node where
  bimap f g (Node a bs) = Node (g a) [Node (f b) (bimap f g <$> as) | Node b as <- bs]

instance Functor (Node b) where
  fmap = bimap id

instance Functor (NodeR b) where
  fmap f (Rev t) = Rev $ bimap f id t

instance Comonad (Node b) where
  extract (Node a _) = a
  duplicate t@(Node _ bs) = Node t [Node b (duplicate <$> as) | Node b as <- bs]

instance Foldable (Node b) where
  foldMap f (Node a bs) = foldr mappend (f a) [foldr mappend mempty (foldMap f <$> as) | Node _ as <- bs]

instance Foldable (NodeR b) where
  foldMap f (Rev (Node _ bs)) = foldr mappend mempty [foldr mappend (f b) $ foldMap f . Rev <$> as | Node b as <- bs]

instance Traversable (Node b) where
  traverse f (Node a bs) = Node <$> f a <*> sequenceA [ Node b <$> sequenceA (traverse f <$> as) | Node b as <- bs]

ana :: (Show b , Show a) => (b -> [a]) -> (a -> [b]) -> b -> Node a b
ana vs ks k = traceShow (k, vs k) $ Node k [Node v $ ana vs ks <$> ks v | v <- vs k]

index :: (Eq a, Hashable a) => M.HashMap a Int -> Node b a -> Node (b,Int) (a,Int)
-- |Number each node by the number of ancestors it has that hae the same label
index m (Node a bs) = Node (a,i) [Node (b,i) (index m' <$> ns) | Node b ns <- bs]
  where i = traceShowId $ M.lookupDefault 0 a m
        m' = M.insertWith (+) a 1 m

prune :: Int -> Node a (b,Int) -> Node a (b,Int)
-- |Removes all nodes numbered higher than `depth`
prune depth (Node (a,i) l) = Node (a,i) $
  if i>depth
     then []
     else [Node v (prune depth <$> ns) | Node v ns <- l]

instance Monoid Int where
  mempty = 0
  mappend = (+)

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

unroll :: Int -> SInfo a -> Integer -> SInfo a
unroll depth fi start = traceShow (map fst cons') $ fi {cm = M.fromList cons', bs = be, ws = M.fromList $ we ++ M.toList (ws fi)}
  where m = cm fi
        emptycons = cons1 { _cenv = emptyIBindEnv, _crhs = PTrue }
          where cons1 = headError "no constraints" $ M.elems m
        kidsm = M.fromList $ (fst. headError "groupWith broken" A.&&& (snd <$>)) <$> groupWith fst pairs
          where pairs = [(k,i)|(i,ks) <- A.second rhsKVars <$> M.toList m, k<-ks]

        -- mlookup :: Integer -> SimpC _
        mlookup v = M.lookupDefault (error $"cons # "++show v++" not found") v $ M.insert 0 emptycons m
        klookup :: KVar -> [Integer]
        klookup k = M.lookupDefault [0] k kidsm
        kenv :: Integer -> [KVar]
        kenv = lhsKVars (bs fi) . mlookup

        tree :: Node (KVar, Int) (Integer, Int)
        tree = traceDrawId $ Node (start,0) (prune depth . index M.empty . ana klookup kenv <$> kenv start)

        treeofsubs :: Node (KVar, Int) ((Integer, Int), [(KVar,KVar)])
        treeofsubs = {- traceDrawId $ -} dup [(KV nonSymbol, KV nonSymbol)] $ {- traceDrawId $ -} kvarSubs <<= tree

        -- treesubs :: Node (KVar, Int) (State (BindEnv, Int) (Integer, SimpC _))
        treesubs = prime (\v s -> substKV s $ mlookup v) <$> treeofsubs

        -- tree' :: Node (KVar, Int) (Integer, SimpC _)
        (tree', (be,_)) = flip runState (bs fi, M.size m) $ sequenceA treesubs

        cons' = (\(b,a) -> (b, a { _cid = Just b })) <$> foldr (:) [] tree'

        renameWfC ((kv,wfc),i) = (kv',) <$> substKV [(kv, kv')] wfc
          where kv' = renameKv kv i

        (we,_) = flip runState (bs fi, M.size m) $ mapM renameWfC $ concatMap (\i -> map (,i) $ M.toList (ws fi)) [0..(depth+1)]

rhsKVars :: SimpC a -> [KVar]
rhsKVars = V.kvars . crhs

lhsKVars :: BindEnv -> SimpC a -> [KVar]
lhsKVars be = V.envKVars be

renameKv :: Integral i => KVar -> i -> KVar
-- |"k" -> n -> "k_n"
renameKv a i = KV $ renameSymbol (kv a) $ fromIntegral i

-- inefficent
kvarSubs :: Node (KVar, Int) a -> (a,[(KVar,KVar)])
-- |Lists all the subsitutions that are to made
kvarSubs t@(Node a _) = (,) a $ reverse $ foldr (:) [] $ (\(k,i) -> (k,renameKv k i)) <$> Rev t

prime :: ( a -> s -> State (e, Int) b ) -> ((a, Int), s) -> State (e, Int) (Integer, b)
-- |Builds our new constraint graph, now knowing the substitutions.
prime sub ((v,_),su) = modify (A.second (+1)) >> ((,) <$> (fromIntegral <$> snd <$> get) <*> sub v su)

dup :: [c] -> Node b (a,[c]) -> Node b (a,[c])
dup c (Node (a,[]) bs) = Node (a,c) bs
dup c (Node (a,cs) bs) = Node (a,c ++ cs) [Node b $ dup [head cs] <$> as | Node b as <- bs]

class SubstKV a where
  substKV :: [(KVar,KVar)] -> a -> State (BindEnv,Int) a

instance SubstKV (WfC a) where
  substKV su wfc = do e <- substKV su (wrft wfc)
                      return $ wfc { wrft = e }

instance SubstKV (SimpC a) where
  substKV su cons = do l <- substKV (tailSafe su) (_cenv cons)
                       r <- substKV (headSafe su) (_crhs cons)
                       return $ cons {_cenv = l, _crhs = r}

instance SubstKV Int where
  substKV su i = do (be,_) <- get
                    let (sym,sr) = lookupBindEnv i be
                    sr' <- substKV su sr
                    let (id,be') = insertBindEnv sym sr' be
                    (_,n) <- get
                    put (be',n)
                    return id

instance SubstKV IBindEnv where
  substKV su be = flip insertsIBindEnv emptyIBindEnv <$> mapM (substKV su) (elemsIBindEnv be)

instance SubstKV Expr where
  substKV su sr = do s <- get
                     let visitor = V.defaultVisitor {V.txExpr = \c p -> fst $ tx c p, V.ctxExpr = \c p -> snd $ tx c p}
                     let (v,s') = V.accumulate visitor s sr
                     put s'
                     return v
    where
      tx s (PKVar k z)   = flip runState s $ do kv' <- substKV su k
                                                return $ {-if kv k == kv kv' then PTrue else-} PKVar kv' z
      tx s p             = (p, s)

instance SubstKV (Symbol,Sort,KVar) where
  substKV su (a,b,k) = (a,b,) <$> substKV su k

instance SubstKV SortedReft where
  substKV su sr = do s <- get
                     let visitor = V.defaultVisitor {V.txExpr = \c p -> fst $ tx c p, V.ctxExpr = \c p -> snd $ tx c p}
                     let (v,s') = V.accumulate visitor s sr
                     put s'
                     return v
    where
      tx s (PKVar k z)   = flip runState s $ do kv' <- substKV su k
                                                -- @TODO leave terminal kvars? or?
                                                return $ {-if kv k == kv kv' then PTrue else-} PKVar kv' z
      tx s p             = (p, s)

instance SubstKV KVar where
  substKV su k = case lookup k su of
                    Just k' -> if kv k' /= kv k then substKV su k' else return k
                    Nothing -> return k


headError _ (x:_) = x
headError s _  = error s
headSafe (x:_) = [x]
headSafe [] = []
tailSafe (_:xs) = xs
tailSafe [] = []

traceDrawId n = trace (unlines $ draw n) n
{-
traceFId f n = traceShow (f n) n
-}
