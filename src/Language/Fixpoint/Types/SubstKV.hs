{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Fixpoint.Types.SubstKV ( SubstKV (..) ) where

import           Control.Monad.State
import           Language.Fixpoint.Types
import qualified Language.Fixpoint.Types.Visitor as V

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

instance Monoid Int where
  mempty = 0
  mappend = (+)

headSafe (x:_) = [x]
headSafe [] = []
tailSafe (_:xs) = xs
tailSafe [] = []
