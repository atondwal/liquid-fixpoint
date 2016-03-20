import qualified Data.HashMap.Strict as M

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
type CandSolutions = M.Map KVar [Expr]

-- new substitutions generated from unrolling
-- the Symbol at the value of a mapping corresponds
-- to the original variable that the tmp
type UnrollSubs = M.Map Symbol (Expr,Symbol)

-- remove OR nodes from AOTree by converting disjunctive interp query
-- to a set of tree interp queries
expandTree :: InterpQuery -> [InterpQuery]
expandTree (And root children) = map (And root) (sequence $ map genQueries children)
expandTree (Or b children) = children >>= genQueries

computeCandSolutions :: UnrollSubs -> InterpQuery -> IO CandSolutions
computeCandSolutions u dquery = do
  -- convert disjunctive interp query to a set of tree interp queries
  let tqueries = expandTree dquery
  tinterps <- forM tqueries $ \tquery ->
    -- FIXME: fill in dummy treeInterpolation
    -- should have signature
    -- treeInterpolation :: InterpQuery -> IO TreeInterp
    treeInterpolation tquery 

  let usubs = Su $ M.fromList $ map (\(x,(_,orig)) -> (x,EVar orig)) $ M.toList u
  let cands = map (extractCandSolutions usubs) tinterps 
  return $ M.unionsWith (++) cands

-- map a tree interpolant to candidate solutions
-- we do this by substituting the following at an interpolant:
-- * the symbol at the head |--> v (or nu)
-- * sub symbols (e.g. tmp) generated from unrolling |--> original symbol
extractCandSolutions :: Subst -> TreeInterp -> CandSolutions
extractCandSolution usubs t = mapAOTree (subUnroll . subNu) t
  where subUnroll _ = subst usubs
	subNu (HeadInfo (Just (_, sym))) = flip subst1 (sym,EVar vvName)

