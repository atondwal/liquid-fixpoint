import System.Console.CmdArgs
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.List (intercalate)
import Control.Monad
import Control.Monad.State

import Language.Fixpoint.Types
import Language.Fixpoint.Types.Config
import Language.Fixpoint.Solver.Solve
import Language.Fixpoint.Smt.Types

data AOTree b a = And b a [AOTree b a]
                | Or b [AOTree b a]

instance (Show a, Show b) => Show (AOTree b a) where
  show (And b a children) = "And " ++ (show b) ++ " " ++ (show a) ++ " [" ++ intercalate "," (map show children) ++ "]"
  show (Or b children) = "Or " ++ (show b) ++ " [" ++ intercalate "," (map show children) ++ "]"

-- this could be a functor except the mapping function "f"
-- needs extra context (the extra b param)
mapAOTree :: (b -> a -> c) -> AOTree b a -> AOTree b c
mapAOTree f (And i n children) = And i (f i n) $ map (mapAOTree f) children
mapAOTree f (Or i children) = Or i $ map (mapAOTree f) children

-- the corresponding HC head of a node (non-root nodes correspond to HC bodies)
newtype HeadInfo = HeadInfo (Maybe (KVar, Symbol)) deriving (Show)

-- an interpolation query
-- an And/Or tree corresponds to a disjunctive interpolant
-- an And tree corresponds to a tree interpolant
type InterpQuery = AOTree HeadInfo Expr

-- a tree interpolant
-- this should have the same structure as its corresponding
-- tree interp query
type TreeInterp = AOTree HeadInfo Expr
showTreeInterp :: TreeInterp -> String
showTreeInterp (And b a children) =
  "And " ++ (show b) ++ " " ++ (show $ smt2 a) ++ " [" ++ intercalate "," (map showTreeInterp children) ++ "]"
showTreeInterp (Or b children) =
  "Or " ++ (show b) ++ " [" ++ intercalate "," (map showTreeInterp children) ++ "]"

-- a set of candidate solutions
type CandSolutions = M.HashMap KVar [Expr]

-- new substitutions generated from unrolling
-- the Symbol at the value of a mapping corresponds
-- to the original variable that the tmp
type UnrollSubs = M.HashMap Symbol (Expr,Symbol)

-- remove OR nodes from AOTree by converting disjunctive interp query
-- to a set of tree interp queries
expandTree :: InterpQuery -> [InterpQuery]
expandTree (And info root children) = map (And info root) (sequence $ map expandTree children)
expandTree (Or info children) = children >>= expandOr info
  where expandOr info (And _ root children) = expandTree (And info root children)
        expandOr _ t = expandTree t

-- generate a tree interp query
-- there shouldn't be an OR node processed in the tree
genQueryFormula :: InterpQuery -> Expr
genQueryFormula (Or _ children) = POr (map genQueryFormula children)
genQueryFormula (And _ root children) = PAnd $ root:(map genQueryFormula' children)
  where genQueryFormula' c@(And _ _ _) = Interp $ genQueryFormula c
        genQueryFormula' c@(Or _ _) = genQueryFormula c

popInterp :: State [Expr] Expr
popInterp = do
  (x:xs) <- get
  put xs
  return x

genTreeInterp :: InterpQuery -> State [Expr] TreeInterp
genTreeInterp query
  | And info _ [] <- query = do
    interp <- popInterp
    return (And info interp [])

  | And info _ children <- query = do
    ichildren <- forM children genTreeInterp
    interp <- popInterp
    return (And info interp ichildren)

  -- this is for tree interpolants, so we don't
  -- do anything for OR nodes
  | Or info children <- query = do
    ichildren <- forM children genTreeInterp
    return (Or info ichildren)

  | otherwise = return query

computeCandSolutions :: UnrollSubs -> InterpQuery -> IO CandSolutions
computeCandSolutions u dquery = do
  -- convert disjunctive interp query to a set of tree interp queries
  let tqueries = expandTree dquery
  tinterps <- forM tqueries $ \_ ->
    -- FIXME: fill in dummy treeInterpolation
    -- should have signature
    -- treeInterpolation :: InterpQuery -> IO TreeInterp
    -- treeInterpolation tquery 
    return $ Or (HeadInfo Nothing) []

  let usubs = Su $ M.fromList $ map (\(x,(_,orig)) -> (x,EVar orig)) $ M.toList u
  let cands = map (extractCandSolutions usubs) tinterps 
  return $ foldr (M.unionWith (++)) M.empty cands

-- map a tree interpolant to candidate solutions
-- we do this by substituting the following at an interpolant:
-- * the symbol at the head |--> v (or nu)
-- * sub symbols (e.g. tmp) generated from unrolling |--> original symbol
extractCandSolutions :: Subst -> TreeInterp -> CandSolutions
extractCandSolutions usubs t =
  let subtree = mapAOTree (\i e -> subUnroll i $ subNu i e) t in 
  collectSol subtree M.empty
  where subUnroll _ = (subst :: Subst -> Expr -> Expr) usubs
        subNu (HeadInfo (Just (_, sym))) e =
          flip (subst1 :: Expr -> (Symbol,Expr) -> Expr) (sym,EVar vvName) e
        subNu (HeadInfo Nothing) e = e
        collectSol (And (HeadInfo Nothing) _ children) m = 
          foldr collectSol m children
        collectSol (And (HeadInfo (Just (k,_))) v children) m =
          let m' = M.insertWith (++) k [v] m in 
          foldr collectSol m' children
        -- this is supposed to be called on tree interps only,
        -- so we set a dummy value for OR nodes
        collectSol (Or _ _) m = m
          
imain = do
  let vars = [(symbol "k",intSort),(vvName,intSort),(symbol "s",intSort),(symbol "s2",intSort),(symbol "tmp",intSort),(symbol "tmp2",intSort)]
  let sinfo = FI {
                cm = M.empty
              , ws = M.empty
              , bs = emptyBindEnv
              , lits = fromListSEnv vars
              , kuts = KS S.empty
              , quals = []
              , bindInfo = M.empty
              , fileName = ""
              , Language.Fixpoint.Types.allowHO = False
              }
  let k = EVar (symbol "k")
  let v = EVar vvName
  let s = EVar (symbol "s")
  let s2 = EVar (symbol "s2")
  let tmp = EVar (symbol "tmp")
  let tmp2 = EVar (symbol "tmp2")
  let u = M.fromList [(symbol "tmp",(PTrue,symbol "k")), (symbol "tmp2",(PTrue,symbol "k"))]
  let usubs = Su $ M.fromList $ map (\(x,(_,orig)) -> (x,EVar orig)) $ M.toList u
  let root = PNot (PAtom Ge v k)
  let int i = ECon (I i)
  let b3a = And (HeadInfo Nothing) (PAnd [PAtom Le tmp2 (int 0), PAtom Eq s2 (int 0)]) []
  let b3 = Or (HeadInfo (Just (KV (symbol "ksum"),symbol "s2"))) [b3a]
  let b2a = And (HeadInfo Nothing) (PAnd [PAtom Le tmp (int 0), PAtom Eq s (int 0)]) []
  let b2b = And (HeadInfo Nothing) (PAnd [PAtom Gt tmp (int 0), PAtom Eq s (EBin Plus s2 tmp), PAtom Eq tmp2 (EBin Minus k (int 2))]) [b3]
  let b2 = Or (HeadInfo (Just (KV (symbol "ksum"),symbol "s"))) [b2a, b2b]
  let b1a = And (HeadInfo Nothing) (PAnd [PAtom Le k (int 0), PAtom Eq v (int 0)]) []
  let b1b = And (HeadInfo Nothing) (PAnd [PAtom Gt k (int 0), PAtom Eq v (EBin Plus s k), PAtom Eq tmp (EBin Minus k (int 1))]) [b2]
  let b1 = Or (HeadInfo (Just (KV (symbol "ksum"),vvName))) [b1a, b1b]
  let sum = And (HeadInfo Nothing) root [b1]
  let trees = expandTree sum
  let query = trees !! 2
  putStrLn "Query:"
  putStrLn $ show $ smt2 $ genQueryFormula query
  interps <- interpolation (def :: Config) sinfo $ genQueryFormula query
  let treeInterp = evalState (genTreeInterp query) $ interps ++ [PFalse]
  putStrLn $ showTreeInterp treeInterp
  forM_ (M.toList $ extractCandSolutions usubs treeInterp) $ \(kvar,cands) -> do
    putStrLn $ "Candidates for " ++ (show kvar) ++ ":"
    forM_ cands (putStrLn . show . smt2)


    
