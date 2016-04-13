-- | This module implements the top-level API for interfacing with Fixpoint
--   In particular it exports the functions that solve constraints supplied
--   either as .fq files or as FInfo.
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Fixpoint.Solver (
    -- * Invoke Solver on an FInfo
    solve, Solver

    -- * Invoke Solver on a .fq file
  , solveFQ

    -- * Function to determine outcome
  , resultExit

    -- * Parse Qualifiers from File
  , parseFInfo
) where


import           Control.Concurrent
import           Data.Binary
-- import           Data.Maybe                         (fromMaybe)
-- import           Data.List                          hiding (partition)
-- import qualified Data.HashSet                       as S
import           System.Exit                        (ExitCode (..))

-- import           System.Console.CmdArgs.Verbosity   hiding (Loud)
import           Text.PrettyPrint.HughesPJ          (render)
-- import           Text.Printf                        (printf)
import           Control.Monad                      (when, forM_)
import           Control.Exception                  (catch)
-- import           Control.Arrow

import           Language.Fixpoint.Solver.Graph     -- (slice)
import           Language.Fixpoint.Solver.Validate  (sanitize)
import qualified Language.Fixpoint.Solver.Eliminate as E
-- import           Language.Fixpoint.Solver.Deps      -- (deps, GDeps (..))
import           Language.Fixpoint.Solver.UniqifyBinds (renameAll)
import           Language.Fixpoint.Solver.UniqifyKVars (wfcUniqify)
import qualified Language.Fixpoint.Solver.Solve     as Sol
-- import           Language.Fixpoint.Solver.Solution  (Solution)

import           Language.Fixpoint.Types.Config           (queryFile, multicore, Config (..))
-- import           Language.Fixpoint.Solver.Unroll    (unroll)
-- import           Language.Fixpoint.Solver.Eliminate (eliminateAll, eliminateInterp)
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files            hiding (Result)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Utils.Progress
import           Language.Fixpoint.Utils.Statistics (statistics)
import           Language.Fixpoint.Partition        -- (mcInfo, partition, partition')
import           Language.Fixpoint.Parse            (rr', mkQual)
import           Language.Fixpoint.Types
-- import qualified Language.Fixpoint.Types.Visitor as V
import           Language.Fixpoint.Minimize (minQuery)
import           Language.Fixpoint.Interpolate (genQualifiers)
import           Language.Fixpoint.Smt.Types
import           Control.DeepSeq

-- type Solver a = Config -> FInfo a -> IO (Result a)

---------------------------------------------------------------------------
-- | Solve an .fq file ----------------------------------------------------
---------------------------------------------------------------------------
solveFQ :: Config -> IO ExitCode
---------------------------------------------------------------------------
solveFQ cfg = do
    fi      <- readFInfo file
    r       <- solve cfg fi
    let stat = resStatus $!! r
    -- putStrLn "solution:"
    -- print $ resSolution r
    -- let str  = render $ resultDoc $!! (const () <$> stat)
    -- putStrLn "\n"
    colorStrLn (colorResult stat) (statStr $!! stat)
    return $ eCode r
  where
    file    = inFile       cfg
    eCode   = resultExit . resStatus
    statStr = render . resultDoc . fmap fst

---------------------------------------------------------------------------
-- | Solve FInfo system of horn-clause constraints ------------------------
---------------------------------------------------------------------------
solve :: (NFData a, Fixpoint a) => Solver a
---------------------------------------------------------------------------
solve cfg q
  | parts cfg    = partition  cfg        $!! q
  | stats cfg    = statistics cfg        $!! q
  | minimize cfg = minQuery   cfg solve' $!! q
  | interpolate cfg = interpSolve 0 cfg $!! q
  | otherwise    = solve'     cfg        $!! q

interpSolve :: (NFData a, Fixpoint a) => Int -> Solver a
interpSolve n cfg q = do
  putStrLn $ "Generating qualifiers with unrolling depth=" ++ show n
  putStrLn "BEFORE Lits:"
  print (lits q)
  putStrLn "BEFORE BindEnv:"
  print (bs q)
  interpQuals <- genQualifiers q n
  putStrLn "Computed qualifiers:"
  forM_ interpQuals (putStrLn . show . smt2 . q_body)
  let q' = q { quals = interpQuals }
  res <- solve' cfg q'
  case res of
    (Result Safe _) -> return res 
    _               -> do
      if n < unrollDepth cfg
        then interpSolve (n+1) cfg q
        else return res

solve' :: (NFData a, Fixpoint a) => Solver a
solve' cfg q = do
  when (save cfg) $ saveQuery   cfg q
  configSW  cfg     solveNative cfg q

configSW :: (NFData a, Fixpoint a) => Config -> Solver a -> Solver a
configSW cfg
  | multicore cfg = solveParWith
  | otherwise     = solveSeqWith

---------------------------------------------------------------------------
readFInfo :: FilePath -> IO (FInfo ())
---------------------------------------------------------------------------
readFInfo f        = fixFileName <$> act
  where
    fixFileName q  = q {fileName = f}
    act
      | isBinary f = readBinFq f
      | otherwise  = readFq f

readFq :: FilePath -> IO (FInfo ())
readFq file = do
  str   <- readFile file
  let q = {-# SCC "parsefq" #-} rr' file str :: FInfo ()
  return q

readBinFq :: FilePath -> IO (FInfo ())
readBinFq file = {-# SCC "parseBFq" #-} decodeFile file

---------------------------------------------------------------------------
-- | Solve in parallel after partitioning an FInfo to indepdendant parts
---------------------------------------------------------------------------
solveSeqWith :: (Fixpoint a) => Solver a -> Solver a
solveSeqWith s c fi0 = withProgressFI fi $ s c fi
  where
    fi               = slice fi0


---------------------------------------------------------------------------
-- | Solve in parallel after partitioning an FInfo to indepdendant parts
---------------------------------------------------------------------------
solveParWith :: (Fixpoint a) => Solver a -> Solver a
---------------------------------------------------------------------------
solveParWith s c fi0 = do
  -- putStrLn "Using Parallel Solver \n"
  let fi       = slice fi0
  withProgressFI fi $ do
    mci <- mcInfo c
    let (_, fis) = partition' (Just mci) fi
    writeLoud $ "Number of partitions : " ++ show (length fis)
    writeLoud $ "number of cores      : " ++ show (cores c)
    writeLoud $ "minimum part size    : " ++ show (minPartSize c)
    writeLoud $ "maximum part size    : " ++ show (maxPartSize c)
    case fis of
      []        -> errorstar "partiton' returned empty list!"
      [onePart] -> s c onePart
      _         -> inParallelUsing (s c) fis

-------------------------------------------------------------------------------
-- | Solve a list of FInfos using the provided solver function in parallel
-------------------------------------------------------------------------------
inParallelUsing :: (a -> IO (Result b)) -> [a] -> IO (Result b)
-------------------------------------------------------------------------------
inParallelUsing f xs = do
   setNumCapabilities (length xs)
   rs <- asyncMapM f xs
   return $ mconcat rs

---------------------------------------------------------------------------
-- | Native Haskell Solver ------------------------------------------------
---------------------------------------------------------------------------
solveNative, solveNative' :: (NFData a, Fixpoint a) => Solver a
---------------------------------------------------------------------------
solveNative !cfg !fi0 = (solveNative' cfg fi0)
                          `catch`
                             (return . result)

result :: Error -> Result a
result e = Result (Crash [] msg) mempty
  where
    msg  = showpp e

solveNative' !cfg !fi0 = do
  -- writeLoud $ "fq file in: \n" ++ render (toFixpoint cfg fi)
  -- rnf fi0 `seq` donePhase Loud "Read Constraints"
  -- let qs   = quals fi0
  -- whenLoud $ print qs
  let fi1  = fi0 { quals = remakeQual <$> quals fi0 }
  -- whenLoud $ putStrLn $ showFix (quals fi1)
  let si0   = {-# SCC "convertFormat" #-} convertFormat fi1
  -- writeLoud $ "fq file after format convert: \n" ++ render (toFixpoint cfg si0)
  -- rnf si0 `seq` donePhase Loud "Format Conversion"
  let si1 = either die id $ {-# SCC "validate" #-} sanitize $!! si0
  -- writeLoud $ "fq file after validate: \n" ++ render (toFixpoint cfg si1)
  -- rnf si1 `seq` donePhase Loud "Validated Constraints"
  graphStatistics cfg si1
  let si2  = {-# SCC "wfcUniqify" #-} wfcUniqify $!! si1
  let si3  = {-# SCC "renameAll" #-} renameAll $!! si2
  -- rnf si2 `seq` donePhase Loud "Uniqify"
  (s0, si4) <- {-# SCC "elim" #-} elim cfg $!! si3
  -- writeLoud $ "About to solve: \n" ++ render (toFixpoint cfg si4)
  -- _ <- interp cfg $!! si4
  res <- {-# SCC "Sol.solve" #-} Sol.solve cfg s0 $!! si4
  -- rnf soln `seq` donePhase Loud "Solve2"
  --let stat = resStatus res
  saveSolution cfg res
  -- when (save cfg) $ saveSolution cfg
  -- writeLoud $ "\nSolution:\n"  ++ showpp (resSolution res)
  -- colorStrLn (colorResult stat) (show stat)
  return res


elim :: (Fixpoint a) => Config -> SInfo a -> IO (Solution, SInfo a)
elim cfg fi
  | eliminate cfg = do
      let (s0, fi') = E.eliminate fi
      writeLoud $ "fq file after eliminate: \n" ++ render (toFixpoint cfg fi')
      -- elimSolGraph cfg s0
      donePhase Loud "Eliminate"
      writeLoud $ "Solution after eliminate: \n" ++ showpp s0 -- toFixpoint cfg fi')
      -- donePhase Loud "DonePrint"
      return (s0, fi')
  | otherwise     =
      return (mempty, fi)

remakeQual :: Qualifier -> Qualifier
remakeQual q = {- traceShow msg $ -} mkQual (q_name q) (q_params q) (q_body q) (q_pos q)
--   where
--     msg      = "REMAKEQUAL: " ++ show q

---------------------------------------------------------------------------
-- | Extract ExitCode from Solver Result ----------------------------------
---------------------------------------------------------------------------
resultExit :: FixResult a -> ExitCode
---------------------------------------------------------------------------
resultExit Safe        = ExitSuccess
resultExit (Unsafe _)  = ExitFailure 1
resultExit _           = ExitFailure 2

{-
interpSym = symbol "InterpolatedQu"

interp :: (Fixpoint a) => Config -> SInfo a -> IO (SInfo a)
interp cfg fi
  | interpolate cfg > -1 = do let fc = failCons cfg
                              let fi' = unroll (interpolate cfg) fi fc
                              whenLoud $ putStrLn $ "fq file after unrolling: \n" ++ render (toFixpoint cfg fi')
                              let (sol,fi'') = eliminateInterp fi'
                              DT.traceShow sol (return ())
                              let fi''' = V.mapKVars (Just . apply sol) fi''
                              whenLoud $ putStrLn $ "fq file after unrolled elimination: \n" ++ render (toFixpoint cfg fi'')
                              donePhase Loud "Unroll"
                              let _ = mlookup (cm fi) (failCons cfg)
                              DT.traceShow (M.keys $ cm fi) (return ())
                              DT.traceShow (M.keys $ cm fi') (return ())
                              DT.traceShow (M.keys $ cm fi'') (return ())
                              DT.traceShow (M.keys $ cm fi''') (return ())
                              DT.traceShow ((V.kvars . crhs &&& V.envKVars (bs fi)) <$>  M.elems (cm fi)) (return ())
                              DT.traceShow ((V.kvars . crhs &&& V.envKVars (bs fi')) <$>  M.elems (cm fi')) (return ())
                              DT.traceShow ((V.kvars . crhs &&& V.envKVars (bs fi'')) <$>  M.elems (cm fi'')) (return ())
                              DT.traceShow ((V.kvars . crhs &&& V.envKVars (bs fi''')) <$>  M.elems (cm fi''')) (return ())
                                  -- @FIXME is the right constraint always the first WCC?
                              q <- buildQual cfg fi''' $ head $ M.elems (cm fi''')
                              DT.traceShow q (return ())
                              return fi''' { quals = q:quals fi''' }
  | otherwise     = return fi

buildQual :: Config -> SInfo a -> SimpC a -> IO Qualifier
buildQual cfg fi c = qualify <$> Sol.interpolation cfg fi (DT.traceShowId (PAnd [p, q]))
  where env  = envCs (bs fi) $ _cenv c
        (qenv,ps) = substBinds env
        p = PAnd ps
        q = PNot $ prop $ crhs c
        qualify p = Q interpSym qenv p (dummyPos "interp")

-- [ x:{v:int|v=10} , y:{v:int|v=20} ] -> [x:int, y:int], [(x=10), (y=20)]
substBinds :: [(Symbol, SortedReft)] -> ([(Symbol,Sort)],[Expr])
substBinds = unzip . map substBind

substBind :: (Symbol, SortedReft) -> ((Symbol,Sort), Expr)
substBind (sym, sr) = ((sym, sr_sort sr), subst1 (reftPred reft) sub)
  where
    reft = sr_reft sr
    sub = (reftBind reft, eVar sym)
-}

---------------------------------------------------------------------------
-- | Parse External Qualifiers --------------------------------------------
---------------------------------------------------------------------------
parseFInfo :: [FilePath] -> IO (FInfo a) -- [Qualifier]
---------------------------------------------------------------------------
parseFInfo fs = mconcat <$> mapM parseFI fs

parseFI :: FilePath -> IO (FInfo a) --[Qualifier]
parseFI f = do
  str   <- readFile f
  let fi = rr' f str :: FInfo ()
  return $ mempty { quals = quals  fi
                  , lits  = lits   fi }

saveSolution :: Config -> Result a -> IO ()
saveSolution cfg res = when (save cfg) $ do
  let f = queryFile Out cfg
  putStrLn $ "Saving Solution: " ++ f ++ "\n"
  ensurePath f
  writeFile f $ "\nSolution:\n"  ++ showpp (resSolution res)

---------------------------------------------------------------------------
-- | Initialize Progress Bar
---------------------------------------------------------------------------
withProgressFI :: FInfo a -> IO b -> IO b
---------------------------------------------------------------------------
withProgressFI = withProgress . fromIntegral . gSccs . cGraph
