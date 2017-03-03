{-# LANGUAGE PatternGuards #-}
module Language.Fixpoint.Solver.Congruence (
    saturate
) where

import Language.Fixpoint.Types
import Language.Fixpoint.Smt.Types
import Language.Fixpoint.Smt.Interface (checkValidWithContext, smtAssert)

import           Control.Monad
import qualified Data.HashMap.Strict       as M

saturate :: Context -> M.HashMap Symbol Definition -> Pred -> IO ()
saturate ctx m p = smtAssert ctx p >> go (subExprs m p)
  where {-@ Lazy go @-} -- Terminates b/c reft logic is strongly normalizing
        go ((f,es):wkl)
           | Just defn <- M.lookup f m
           = do newes <- expand ctx defn es
                mapM_ (smtAssert ctx . EEq (eApps (EVar f) es)) newes
                go $ wkl++(subExprs m =<< newes)
        go [] = return ()
        go _  = error "Function definition not found. This should never happen! Email Anish?"

expand :: Context -> Definition -> [Expr] -> IO [Expr]
expand ctx (Dfn _ xs pes) es = map (sub . snd) <$>
                           filterM (checkValidWithContext ctx [] PTrue . sub . fst)
                           pes
  where sub = subst (Su $ M.fromList (zip xs es))
