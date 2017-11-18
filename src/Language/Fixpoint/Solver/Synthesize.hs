module Language.Fixpoint.Solver.Synthesize (
    synthesize
) where

import           Language.Fixpoint.Types
-- GROSS!!! unfuck later, if I feel like it
import qualified Data.Text                as T
import qualified Data.List                       as L
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Types.Visitor as Vis
import           Language.Fixpoint.Types.Config  as FC
import           Language.Fixpoint.Defunctionalize
import           Language.Fixpoint.SortCheck

import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S

synthesize :: SInfo a -> IO (SInfo a)
synthesize fi = do
      qs <- theks
      return fi { quals = qs }
  where (KS kvars) = kuts fi
        cons k = M.filter (hasKvar k) (cm fi)
        theks = (\k -> synthesizeKvar k (cons k)) `mapM` (S.toList kvars)

-- Yeah, these qualifiers should acutally be known types wrapped inside a
-- solverInfo, but I really don't understand that solverInfo/Eliminate codebase
-- that well... maybe then
synthesizeKvar :: KVar -> M.HashMap SubcId (SimpC a) -> IO Qualifier
synthesizeKvar = _

hasKvar k a = elem k (Vis.kvars a)

-- The thing to do is to find all the kut KVars and then

-- This context needs to be spun up for every actual context Γ.
-- In practice this means that we need one for each constraint
-- that uses a kut Kvar
data SynthesisConext
  = SC { scContext :: IO SMT.Context
       , scPreds   :: !([(Symbol, Sort)] -> Expr -> SMT.Context -> IO [(Symbol, T.Text)])
       , scLams    :: [(Symbol, Sort)]
       }

dumbContext :: IO SMT.Context -> SynthesisConext
dumbContext ctx = SC ctx (\_ _ _ -> error "HAHA") []

isValid :: SynthesisConext -> Expr -> IO [(Symbol, T.Text)]
isValid γ b = scPreds γ (scLams γ) b =<< scContext γ

makeCtx :: Config -> SMT.Context -> [(Symbol, SortedReft)] -> SynthesisConext
makeCtx cfg ctx es = (dumbContext context) { scPreds  = \bs e c -> askSMT c bs e }
  where
    context :: IO SMT.Context
    context = do
      SMT.smtPop ctx
      SMT.smtPush ctx
      SMT.smtAssert ctx $
        pAnd $ filter (null . Vis.kvars) ((toSMT [] . expr . snd) <$> es)
      return ctx

    toSMT bs = defuncAny cfg (SMT.ctxSymEnv ctx) . elaborate "makeSynCtx" (elabEnv bs)
    elabEnv  = L.foldl' (\env (x, s) -> insertSymEnv x s env) (SMT.ctxSymEnv ctx)

    askSMT :: SMT.Context -> [(Symbol, Sort)] -> Expr -> IO [(Symbol, T.Text)]
    askSMT ctx bs e
      -- Fix this to work nicely with Eliminate?
      | null (Vis.kvars e) = do
          SMT.smtPush ctx
          b <- SMT.getValues ctx [] (toSMT bs e) (fst <$> bs)
          SMT.smtPop ctx
          return b
      | otherwise      = error "Synthesis tried to write a KVar to SMT"
