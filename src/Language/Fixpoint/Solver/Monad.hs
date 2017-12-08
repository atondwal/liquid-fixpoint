{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExplicitForAll    #-}
{-# LANGUAGE RankNTypes        #-}

-- | This is a wrapper around IO that permits SMT queries

module Language.Fixpoint.Solver.Monad
       ( -- * Type
         SolveM

         -- * Execution
       , runSolverM

         -- * Get Binds
       , getBinds

         -- * SMT Query
       , filterRequired
       , filterValid
       , filterValidCEGIS
       , filterValidGradual
       , checkSat
       , smtEnablembqi

         -- * Debug
       , Stats
       , tickIter
       , stats
       , numIter
       )
       where

import           Control.DeepSeq
import           GHC.Generics
import           Language.Fixpoint.Utils.Progress
import qualified Language.Fixpoint.Types.Config  as C
import           Language.Fixpoint.Types.Config  (Config)
import qualified Language.Fixpoint.Types   as F
-- import           Language.Fixpoint.SortCheck
import qualified Language.Fixpoint.Types.Solutions as F
import           Language.Fixpoint.Types   (pprint)
-- import qualified Language.Fixpoint.Types.Errors  as E
import           Language.Fixpoint.Smt.Serialize ()
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Smt.Interface
import           Language.Fixpoint.Types.Visitor
-- import qualified Language.Fixpoint.Smt.Theories as Thy
import           Language.Fixpoint.Solver.Sanitize
import           Language.Fixpoint.Graph.Types (SolverInfo (..))
-- import           Language.Fixpoint.Solver.Solution
-- import           Data.Maybe           (catMaybes)
import           Data.List            (partition)
-- import           Data.Either
-- import           Data.Char            (isUpper)
import           Text.PrettyPrint.HughesPJ (text)
import           Control.Monad.State.Strict
import qualified Data.HashMap.Strict as M
import           Data.Maybe (catMaybes)
import           Control.Exception.Base (bracket)

--------------------------------------------------------------------------------
-- | Solver Monadic API --------------------------------------------------------
--------------------------------------------------------------------------------

type SolveM = StateT SolverState IO

type CntrEx = [(F.Symbol,F.Expr)]

data SolverState = SS { ssCtx     :: !Context      -- ^ SMT Solver Context
                      , ssBinds   :: !F.SolEnv     -- ^ All variables and types
                      , ssStats   :: !Stats        -- ^ Solver Statistics
                      , ssPts     :: ![CntrEx]      -- ^ CEs for synthesis
                      }

data Stats = Stats { numCstr :: !Int -- ^ # Horn Constraints
                   , numIter :: !Int -- ^ # Refine Iterations
                   , numBrkt :: !Int -- ^ # smtBracket    calls (push/pop)
                   , numChck :: !Int -- ^ # smtCheckUnsat calls
                   , numVald :: !Int -- ^ # times SMT said RHS Valid
                   } deriving (Show, Generic)

instance NFData Stats

stats0    :: F.GInfo c b -> Stats
stats0 fi = Stats nCs 0 0 0 0
  where
    nCs   = M.size $ F.cm fi


instance F.PTable Stats where
  ptable s = F.DocTable [ (text "# Constraints"         , pprint (numCstr s))
                        , (text "# Refine Iterations"   , pprint (numIter s))
                        , (text "# SMT Brackets"        , pprint (numBrkt s))
                        , (text "# SMT Queries (Valid)" , pprint (numVald s))
                        , (text "# SMT Queries (Total)" , pprint (numChck s))
                        ]

--------------------------------------------------------------------------------
runSolverM :: Config -> SolverInfo b c -> SolveM a -> IO a
--------------------------------------------------------------------------------
runSolverM cfg sI act =
  bracket acquire release $ \ctx -> do
    res <- runStateT act' (s0 ctx)
    smtWrite ctx "(exit)"
    return (fst res)
  where
    s0 ctx   = SS ctx be (stats0 fi) []
    act'     = {- declare initEnv >> -} assumesAxioms (F.asserts fi) >> act
    release  = cleanupContext
    acquire  = makeContextWithSEnv cfg file initEnv
    initEnv  = symbolEnv   cfg fi
    -- lts      = F.toListSEnv (F.dLits fi)
    -- ds       = F.ddecls fi
    be       = F.SolEnv (F.bs fi)
    file     = C.srcFile cfg
    -- only linear arithmentic when: linear flag is on or solver /= Z3
    -- lar     = linear cfg || Z3 /= solver cfg
    fi       = (siQuery sI) {F.hoInfo = F.HOI (C.allowHO cfg) (C.allowHOqs cfg)}


--------------------------------------------------------------------------------
getBinds :: SolveM F.SolEnv
--------------------------------------------------------------------------------
getBinds = ssBinds <$> get

--------------------------------------------------------------------------------
getIter :: SolveM Int
--------------------------------------------------------------------------------
getIter = numIter . ssStats <$> get

--------------------------------------------------------------------------------
incIter, incBrkt :: SolveM ()
--------------------------------------------------------------------------------
incIter   = modifyStats $ \s -> s {numIter = 1 + numIter s}
incBrkt   = modifyStats $ \s -> s {numBrkt = 1 + numBrkt s}

--------------------------------------------------------------------------------
incChck, incVald :: Int -> SolveM ()
--------------------------------------------------------------------------------
incChck n = modifyStats $ \s -> s {numChck = n + numChck s}
incVald n = modifyStats $ \s -> s {numVald = n + numVald s}

withContext :: (Context -> IO a) -> SolveM a
withContext k = (lift . k) =<< getContext

getContext :: SolveM Context
getContext = ssCtx <$> get

modifyStats :: (Stats -> Stats) -> SolveM ()
modifyStats f = modify $ \s -> s { ssStats = f (ssStats s) }

--------------------------------------------------------------------------------
-- | SMT Interface -------------------------------------------------------------
--------------------------------------------------------------------------------
-- | `filterRequired [(x1, p1),...,(xn, pn)] q` returns a minimal list [xi] s.t.
--   /\ [pi] => q
--------------------------------------------------------------------------------
filterRequired :: F.Cand a -> F.Expr -> SolveM [a]
--------------------------------------------------------------------------------
filterRequired = error "TBD:filterRequired"

{-
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

; Z3 will only track assertions that are named.

(assert (< 0 x))
(assert (! (< 0 y)       :named b2))
(assert (! (< x 10)      :named b3))
(assert (! (< y 10)      :named b4))
(assert (! (< (+ x y) 0) :named bR))
(check-sat)
(get-unsat-core)

> unsat (b2 bR)
-}
--

--------------------------------------------------------------------------------
-- | `filterValid p [(x1, q1),...,(xn, qn)]` returns the list `[ xi | p => qi]`
--------------------------------------------------------------------------------
filterValid :: F.SrcSpan -> F.Expr -> F.Cand a -> SolveM [a]
--------------------------------------------------------------------------------
filterValid sp p qs = do
  qs' <- withContext $ \me ->
           smtBracket me "filterValidLHS" $
             filterValid_ sp p qs me
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  return qs'

filterValid_ :: F.SrcSpan -> F.Expr -> F.Cand a -> Context -> IO [a]
filterValid_ sp p qs me = catMaybes <$> do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracketAt sp me "filterValidRHS" $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ if valid then Just x else Nothing



--------------------------------------------------------------------------------
-- | `filterValidGradual ps [(x1, q1),...,(xn, qn)]` returns the list `[ xi | p => qi]`
-- | for some p in the list ps
--------------------------------------------------------------------------------
filterValidGradual :: [F.Expr] -> F.Cand a -> SolveM [a]
--------------------------------------------------------------------------------
filterValidGradual p qs = do
  qs' <- withContext $ \me ->
           smtBracket me "filterValidGradualLHS" $
             filterValidGradual_ p qs me
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  return qs'

filterValidGradual_ :: [F.Expr] -> F.Cand a -> Context -> IO [a]
filterValidGradual_ ps qs me
  = (map snd . fst) <$> foldM partitionCandidates ([], qs) ps
  where
    partitionCandidates :: (F.Cand a, F.Cand a) -> F.Expr -> IO (F.Cand a, F.Cand a)
    partitionCandidates (ok, candidates) p = do
      (valids', invalids')  <- partition snd <$> filterValidOne_ p candidates me
      let (valids, invalids) = (fst <$> valids', fst <$> invalids')
      return (ok ++ valids, invalids)

filterValidOne_ :: F.Expr -> F.Cand a -> Context -> IO [((F.Expr, a), Bool)]
filterValidOne_ p qs me = do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracket me "filterValidRHS" $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ ((q, x), valid)

smtEnablembqi :: SolveM ()
smtEnablembqi
  = withContext $ \me ->
      smtWrite me "(set-option :smt.mbqi true)"

--------------------------------------------------------------------------------
filterValidCEGIS :: F.SrcSpan -> F.Expr -> F.Cand (F.KVar, F.EQual)
                    -> SolveM [(F.KVar, F.EQual)]
--------------------------------------------------------------------------------
filterValidCEGIS _sp p qs = do
  xs  <- fmap snd3 . F.bindEnvToList . F.soeBinds <$> getBinds
  qs' <- getContext >>= \me ->
           smtBracket me "filterValidLHS" $ catMaybes<$> do
    def <- lift $ getValuesExpr me xs
    liftIO $ smtAssert me p
    forM qs $ \(q, x) ->
      smtBracket me "filterValidRHS" $ do
        pts <- ssPts <$> get
        if and $ isImpliedAt def (ctxSymEnv me) p q <$> pts
          then do
            liftIO $ smtAssert me (F.PNot q)
            valid <- liftIO $ smtCheckUnsat me
            if valid then return $ Just x else smtGetModel me >> return Nothing
          else return Nothing
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  return qs'


-- smt2 (ctxSymEnv me)
monomorphizeApp :: F.SymEnv -> F.Expr -> F.Expr
monomorphizeApp env (F.ECst (F.EVar f) t@F.FFunc{}) | f == F.applyName
  = F.EVar $ F.symbolAtName F.applyName env e t
  where e = error "eval called on unknown expression" :: Int
monomorphizeApp _ e = e

isImpliedAt def env p q pt = termAtPoint def env p pt <= termAtPoint def env q pt

termAtPoint :: CntrEx -> F.SymEnv -> F.Expr -> CntrEx -> Maybe Bool
termAtPoint def env term pt = toBool $ eval $
                              ev def $ ev pt $
                              mapExpr (monomorphizeApp env) term

snd3 :: (a,b,c) -> b
snd3 (_,x,_) = x

ev :: CntrEx -> F.Expr -> F.Expr
ev pts e = foldr (flip F.subst1) e pts

smtGetModel :: Context -> SolveM ()
smtGetModel me = do
  pt <- liftIO $ (\(Model x) -> x) <$> command me GetModel
  modify (\s -> s { ssPts = pt : ssPts s })

--------------------------------------------------------------------------------
checkSat :: F.Expr -> SolveM  Bool
--------------------------------------------------------------------------------
checkSat p
  = withContext $ \me ->
      smtBracket me "checkSat" $
        smtCheckSat me p

--------------------------------------------------------------------------------
assumesAxioms :: [F.Triggered F.Expr] -> SolveM ()
--------------------------------------------------------------------------------
assumesAxioms es = withContext $ \me -> forM_  es $ smtAssertAxiom me


---------------------------------------------------------------------------
stats :: SolveM Stats
---------------------------------------------------------------------------
stats = ssStats <$> get

---------------------------------------------------------------------------
tickIter :: Bool -> SolveM Int
---------------------------------------------------------------------------
tickIter newScc = progIter newScc >> incIter >> getIter

progIter :: Bool -> SolveM ()
progIter newScc = lift $ when newScc progressTick
