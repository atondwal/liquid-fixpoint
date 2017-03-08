{-# LANGUAGE PatternGuards #-}
module Language.Fixpoint.Solver.Congruence (
    saturate
) where

import Language.Fixpoint.Types
import Language.Fixpoint.Smt.Types
import Language.Fixpoint.Types.Visitor
import Language.Fixpoint.Smt.Interface (checkValidWithContext, smtAssert)

import           Data.Maybe
import           Control.Monad
import qualified Data.HashMap.Strict       as M

saturate :: Context -> M.HashMap Symbol Definition -> Pred -> IO ()
-- TODO bring in the other binders
saturate ctx m p = go (subExprs m p)
  where {-@ Lazy go @-} -- Terminates b/c reft logic is strongly normalizing
        go ((f,es):wkl)
           | Just defn <- M.lookup f m
           = do newes <- expand p ctx defn es
                mapM_ (smtAssert ctx . EEq (eApps (EVar f) es)) newes
                go $ wkl++(subExprs m =<< newes)
        go [] = return ()
        go _  = error "Function definition not found. This should never happen! Email Anish?"

expand :: Expr -> Context -> Definition -> [Expr] -> IO [Expr]
expand p ctx (Dfn _ xs pes) es = map (sub . snd) <$>
                           filterM (checkValidWithContext ctx [] p . sub . fst)
                           pes
  where sub = subst (Su $ M.fromList (zip xs es))

subExprs :: M.HashMap Symbol Definition -> Expr -> [(Symbol,[Expr])]
subExprs m e = filter (isJust . flip M.lookup m . fst) $
               unsymb =<<
               splitEApp <$> eapps e

unsymb (EVar f, es) = [(f,es)]
unsymb (ECst _ _,_) = [] -- Z3 builtins
unsymb _ = error "Applying something that's not a function?"
