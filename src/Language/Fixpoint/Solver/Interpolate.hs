import qualified Data.HashMap.Strict as M
import Control.Monad

import Language.Fixpoint.Types

data AOTree b a = And b a [AOTree b a]
                | Or b [AOTree b a]

-- this could be a functor except the mapping function "f"
-- needs extra context (the extra b param)
mapAOTree :: (b -> a -> c) -> AOTree b a -> AOTree b c
mapAOTree f (And i n children) = And i (f i n) $ map (mapAOTree f) children
mapAOTree f (Or i children) = Or i $ map (mapAOTree f) children

-- the corresponding HC head of a node (non-root nodes correspond to HC bodies)
newtype HeadInfo = HeadInfo (Maybe (KVar, Symbol))

-- an interpolation query
-- an And/Or tree corresponds to a disjunctive interpolant
-- an And tree corresponds to a tree interpolant
type InterpQuery = AOTree HeadInfo Expr

-- a tree interpolant
-- this should have the same structure as its corresponding
-- tree interp query
type TreeInterp = AOTree HeadInfo Expr

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
genTreeQuery :: InterpQuery -> Expr
genTreeQuery (Or _ children) = POr (map genTreeQuery children)
genTreeQuery (And _ root children) = PAnd $ root:(map genTreeQuery' children)
  where genTreeQuery' c@(And _ _ _) = Interp $ genTreeQuery c
        genTreeQuery' c@(Or _ _) = genTreeQuery c

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
  let subtree = mapAOTree (subUnroll . subNu) t in 
  collectSol subtree M.empty
  where subUnroll _ = (subst :: Subst -> Expr -> Expr) usubs
        subNu (HeadInfo (Just (_, sym))) =
          flip (subst1 :: Expr -> (Symbol,Expr) -> Expr) (sym,EVar vvName)
        subNu (HeadInfo Nothing) = id
        collectSol (And (HeadInfo Nothing) _ children) m = 
          foldr collectSol m children
        collectSol (And (HeadInfo (Just (k,_))) v children) m =
          let m' = M.insertWith (++) k [v] m in 
          foldr collectSol m' children
        -- this is supposed to be called on tree interps only,
        -- so we set a dummy value for OR nodes
        collectSol (Or _ _) m = m
          

