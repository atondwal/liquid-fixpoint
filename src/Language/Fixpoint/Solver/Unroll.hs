{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections#-}

module Language.Fixpoint.Solver.Unroll (unroll) where

import           Data.Maybe
import           Data.Hashable
import           Data.Bifunctor
import           Control.Monad
import           Control.Monad.State
import           Control.Comonad
import qualified Control.Arrow as A
import           Language.Fixpoint.Names (renameSymbol)
import qualified Language.Fixpoint.Visitor as V
import           GHC.Exts (groupWith)

import           Language.Fixpoint.Config
import           Language.Fixpoint.Types
import qualified Data.HashMap.Strict              as M
import Debug.Trace

data Node b a = Node { me :: a, kids :: [Node a b] } deriving Show

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
  foldMap f (Node a bs) = foldr mappend (f a) [foldr mappend mempty (foldMap f <$> as) | Node b as <- bs]

instance Foldable (NodeR b) where
  foldMap f (Rev (Node a bs)) = foldr mappend mempty [foldr mappend (f b) $ foldMap f . Rev <$> as | Node b as <- bs]

instance Monoid Int where
  mempty = 0
  mappend = (+)

headError _ (x:xs) = x
headError s _  = error s
headSafe (x:xs) = [x]
headSafe [] = []
tailSafe (x:xs) = xs
tailSafe [] = []

unroll :: FInfo a -> Integer -> FInfo a
unroll fi start = traceShow (map fst cons') $ fi {cm = M.fromList $ extras ++ map reid cons', bs = be, ws = we ++ ws fi}
  where m = cm fi
        emptycons = cons1 { senv = emptyIBindEnv, srhs = makeBlankReft (srhs cons1), slhs = makeBlankReft (slhs cons1) }
          where cons1 = M.lookupDefault (error "no cons #1") 1 m
        mlookup v = M.lookupDefault (error $"cons # "++show v++" not found") v $ M.insert 0 emptycons m
        kidsm = M.fromList $ (fst.(headError "groupWith broken") A.&&& (snd <$>)) <$> groupWith fst pairs
          where pairs = [(k,i)|(i,ks) <- A.second rhs <$> M.toList m, k<-ks]
        klookup k = M.lookupDefault [0] k kidsm

        rhs, lhs :: SubC a -> [KVar]
        rhs = V.rhsKVars
        lhs = V.lhsKVars (bs fi)

        tree = traceShowId $ Node (start,0) (prune . index M.empty . ana <$> lhs (mlookup start))
        tree' :: State (BindEnv, Int) (Node (Integer, SubC _) [(KVar,KVar)])
        tree' = prime $ kvarSubs <<= tree
        (cons', (be,_)) = flip runState (bs fi, M.size m) $ (foldr (:) [] . Rev <$>) $ do tp <- tree'
                                                                                          return $ traceShow (bimap fst void tp) tp
        extras = M.toList $ M.filter ((==[]).rhs) m
        reid :: (Integer, SubC a) -> (Integer, SubC a)
        reid (b,a) = (b, a { sid = Just b })

        ana k = traceShow (k, klookup k) $ Node k [Node v $ ana <$> lhs (mlookup v) | v <- klookup k]

        -- Lists all the subsitutions that are to made
        -- inefficent
        kvarSubs :: Node (KVar, Int) a -> (a,[(KVar,KVar)])
        kvarSubs t = (,) (me t) $ foldr (:) [] $ (\(k,i) -> (k,renameKv k i)) <$> Rev t

        -- Builds our new constraint graph, now knowing the substitutions.
        prime :: Node a ((Integer, Int),[(KVar, KVar)]) -> State (BindEnv, Int) (Node (Integer, SubC _) [(KVar, KVar)])
        prime (Node ((v,i),subs) vs) = Node subs <$> forM vs (\(Node _ ns) -> do subd <- substKV subs $ mlookup v
                                                                                 grandkids <- mapM prime ns
                                                                                 (s,n) <- get
                                                                                 put (s,n+1)
                                                                                 return $ Node (fromIntegral n, subd) grandkids)

        (we,_) = flip runState (bs fi, M.size m) $ mapM renameWfC $ concatMap (\i -> map (,i) $ ws fi) [1..(depth+1)]
        renameWfC (wfc,i) = if i == 0 then return wfc else substKV [(kv, renameKv kv i)] wfc
          where kv = headError "no KVar in WFC" $ V.kvars $ sr_reft $ wrft wfc


renameKv :: Integral i => KVar -> i -> KVar
-- "k" -> n -> "k_n"
renameKv a i = KV $ renameSymbol (kv a) $ fromIntegral i

-- Removes all nodes numbered higher than `depth`
prune :: Node a (b,Int) -> Node a (b,Int)
prune (Node (a,i) l) = Node (a,i) $
  if i>depth
     then []
     else [Node v (prune <$> ns) | Node v ns <- l]

class SubstKV a where
  substKV :: [(KVar,KVar)] -> a -> State (BindEnv,Int) a

instance SubstKV (WfC a) where
  substKV su wfc = do e <- substKV su (wrft wfc)
                      return $ wfc { wrft = e }

instance SubstKV (SubC a) where
  substKV su cons = do l <- substKV (headSafe su) (slhs cons)
                       r <- substKV (tailSafe su) (srhs cons)
                       e <- substKV (tailSafe su) (senv cons)
                       return $ cons {slhs = l, srhs = r, senv = e}

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

instance SubstKV SortedReft where
  substKV su sr = do s <- get
                     let visitor = V.defaultVisitor {V.txPred = (\c p -> fst $ tx c p), V.ctxPred = (\c p -> snd $ tx c p)}
                     let (v,s') = V.execVisitM visitor s s V.visit sr
                     put s'
                     return v
    where
      tx s (PKVar k z)   = flip runState s $ do kv' <- substKV su k
                                                return $ if k == kv' then PTrue else PKVar kv' z
      tx s p             = (p, s)

instance SubstKV KVar where
  substKV su kv = case lookup kv su of
                    Just kv' -> if kv' /= kv then substKV su kv' else return kv
                    Nothing -> return kv

index :: (Eq a, Hashable a) => M.HashMap a Int -> Node b a -> Node (b,Int) (a,Int)
-- |Number each node by the number of ancestors it has that hae the same label
index m (Node a bs) = Node (a,i) [Node (b,i) (index m' <$> ns) | Node b ns <- bs]
  where i = M.lookupDefault 0 a m
        m' = M.insertWith (+) a 1 m

makeBlankReft :: SortedReft -> SortedReft
makeBlankReft (RR sort (Reft (sym, Refa pred))) = RR sort (Reft (sym, Refa PTrue))

depth :: Int
-- |Equals 4 @TODO justify me
depth = 4
