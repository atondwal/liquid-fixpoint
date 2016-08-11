-- | This module uses Craig interpolation to compute qualifiers
  -- Q name (reverse params'') e loc
-- | that can be used to solve constraint sets

{-# LANGUAGE PatternGuards #-}

module Language.Fixpoint.Interpolate ( genQualifiers, imain ) where

import System.Console.CmdArgs hiding (Loud)
import qualified Data.HashMap.Strict as M
-- import qualified Data.HashSet as S
import Data.List (intercalate, nub, permutations)
import Data.Maybe (fromMaybe, maybeToList)

import Control.Arrow ((&&&))
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader

-- import Language.Fixpoint.Smt.Types
import Language.Fixpoint.Types hiding (renameSymbol)
import Language.Fixpoint.Types.Config
import Language.Fixpoint.Solver.Solve
import Language.Fixpoint.Solver.Solution
import qualified Language.Fixpoint.Types.Visitor as V
-- import Data.Interned
-- import Debug.Trace

data AOTree b a = And b a [AOTree b a]
                | Or b [AOTree b a]

instance (Show a, Show b) => Show (AOTree b a) where
  show (And b a children) =
    let showChildren = intercalate "," (map show children) in
    "And " ++ (show b) ++ " " ++ (show a) ++ " [" ++ showChildren ++ "]"
  show (Or b children) =
    let showChildren = intercalate "," (map show children) in
    "Or " ++ (show b) ++ " [" ++ showChildren ++ "]"

instance (Eq a, Eq b) => Eq (AOTree b a) where
  (And x1 y1 c1) == (And x2 y2 c2)  = x1 == x2 && y1 == y2 && c1 == c2
  (Or x1 c1) == (Or x2 c2)          = x1 == x2 && c1 == c2
  (And _ _ _) == (Or _ _)           = False
  (Or _ _) == (And _ _ _)           = False

-- this could be a functor except the mapping function "f"
-- needs extra context (the extra b param)
mapAOTree :: (b -> a -> c) -> AOTree b a -> AOTree b c
mapAOTree f (And i n children) = And i (f i n) $ map (mapAOTree f) children
mapAOTree f (Or i children) = Or i $ map (mapAOTree f) children

-- the corresponding HC head of a node (non-root nodes correspond to HC bodies)
type HeadInfo = (KVar, Symbol)

-- an interpolation query
-- an And/Or tree corresponds to a disjunctive interpolant
-- an And tree corresponds to a tree interpolant
type InterpQuery = AOTree (Maybe HeadInfo) Expr

-- a tree interpolant
-- this should have the same structure as its corresponding tree interp query
type TreeInterp = AOTree (Maybe HeadInfo) Expr

-- a set of candidate solutions
type CandSolutions = M.HashMap KVar [Expr]

-- body, children, head
-- this is computed from SubC
type ClauseChild = (KVar, Subst, Symbol)
type ClauseInfo a = (Expr, [ClauseChild], a)
type Rule = ClauseInfo (KVar, Subst)
type ExprSort = (Expr,Sort)
type Query = ClauseInfo ExprSort

instance Functor ((,,) a b) where
  fmap f (a,b,c) = (a,b,f c)

-- new substitutions generated from unrolling
-- the Symbol at the value of a mapping corresponds
-- to the original variable that the tmp var substituted
type UnrollSubs = M.HashMap Symbol Symbol
-- type SymbolMap  = M.HashMap Symbol Symbol

-- mapping from kvars to rec/nonrec-clauses with head as the kvar
type KClauses = M.HashMap KVar ([Rule], [Rule])
-- sorts of symbols; this is used for 
type SymSorts = M.HashMap Symbol Sort
type ArgMap   = M.HashMap Symbol (Symbol, Maybe Symbol)
data UnrollInfo = UI {
                    kcs :: KClauses
                  , ss :: SymSorts
                  , argmap :: M.HashMap Symbol (Symbol, Maybe Symbol)
                  }

setKClauses :: KClauses -> UnrollInfo -> UnrollInfo
setKClauses kcs (UI _ ss am) = UI kcs ss am

-- for generating renamed symbols
type RenameMap = M.HashMap Symbol Int

-- created symbols, rename map, unroll subs
data UnrollState = URS {
                      createdSymbols :: SymSorts
                    , renameMap :: RenameMap
                    , unrollSubs :: UnrollSubs
                    }
type UnrollDepth = M.HashMap KVar Int
type UnrollM a = ReaderT UnrollInfo (State UnrollState) a

-- Get and set for UnrollM

-- get sort for a symbol (could be in uinfo or created symbols)
getSymSort :: Symbol -> UnrollM (Maybe Sort)
getSymSort s = do
  ss <- ss <$> ask
  case M.lookup s ss of
    Just sort -> return (Just sort)
    Nothing -> M.lookup s . createdSymbols <$> get

updateRenameMap :: RenameMap -> UnrollM ()
updateRenameMap rm = modify $ \x -> x {renameMap = rm}

updateCreatedSymbols :: SymSorts -> UnrollM ()
updateCreatedSymbols cs = modify $ \x -> x {createdSymbols = cs}

updateUnrollSubs :: UnrollSubs -> UnrollM ()
updateUnrollSubs us = modify $ \x -> x {unrollSubs = us}

  -- FIXME: CHECK IF s has number suffix
getSubCount :: Symbol -> UnrollM Int
getSubCount s = fromMaybe 1 . M.lookup (unSuffixSymbol s) . renameMap <$> get

updateSubCount :: Symbol -> Int -> UnrollM ()
updateSubCount s n = updateRenameMap =<< M.insert s n . renameMap <$> get

-- HELPER FUNCTIONS

bindSym :: BindEnv -> BindId -> Symbol
bindSym env id = fst $ lookupBindEnv id env

substToList :: Subst -> [(Symbol, Expr)]
substToList (Su map) = M.toList map

-- like intSymbol, but without the separator
-- numSymbol :: (Show a) => Symbol -> a -> Symbol
-- numSymbol x i = x `mappendSym` (symbol $ show i)

--------------------------------
-- | PRELIMINARIES FOR UNROLLING
--------------------------------

atomicExprs :: Expr -> [Expr]
atomicExprs (PAnd ps) = ps >>= atomicExprs
-- atomicExprs (POr ps) = concatMap atomicExprs ps
atomicExprs e         = [e]

isKVar :: Expr -> Bool
isKVar (PKVar _ _)    = True
isKVar _              = False

getKVar :: Expr -> (KVar, Subst)
getKVar (PKVar k s)   = (k, s)
getKVar e             = error $ "expr " ++ show e ++ " is not a kvar"

bsym symrhs s = if s == symrhs then vvName else s

clauseInfo :: (Symbol,Sort) -> SInfo a -> SimpC a -> ClauseInfo ExprSort
clauseInfo (symrhs,sortrhs) sinfo c = (PAnd body, kvars, (rhs,sortrhs))
  where body     = filter (not . isKVar) . fst =<< bindings
        kvars    = getKVarSym =<< bindings
        rhs      = cleanSubs globals sinfo $ subst1 (crhs c) (symrhs, EVar vvName)

        bindings :: [([Expr], Symbol)]
        bindings = map (filter cleanExprs . substVv . (atomicExprs =<<) . lookupBind
                           &&& bsym symrhs . bindSym (bs sinfo))
                       (elemsIBindEnv $ senv c)

        lookupBind :: BindId -> [Expr]
        lookupBind = bindExprs (sid c, bs sinfo, senv c)
        substVv    = map (`subst1` (symrhs, EVar vvName))

        globals           = map fst $ toListSEnv (lits sinfo)
        getKVarSym (es,s) = map (packHead s) $ filter isKVar es
        packHead s pk     = (k, subsInScope globals sinfo (filterConSym e s) k, s)
          where (k,e) = getKVar pk

-- only inlcude exprs that have content
-- (i.e., remove True and exprs of the form x == x
cleanExprs :: Expr -> Bool
cleanExprs expr
  | PTrue <- expr                 = False
  | PAnd [] <- expr               = False
  | PAtom Eq x y <- expr, x == y  = False
  | otherwise                     = True

-- substitution sanitizer:
-- (1) filter out substitutions for [VV###:=s]; this is used by liquid
-- fixpoint to insert the actual variable of a constraint instead
-- of a generic "v". we erase these subs because they interfere
-- with unrolling
-- (2) filter out substitutions not of the form [x:=expr], where
-- x is in in the WfC of a kvar (or in the "global" scope of
-- finfo lits
cleanSubs globals si = V.trans (subVisitor vvName) () ()
  where
  subVisitor s          = V.defaultVisitor { V.txExpr = (cleanSubs' s) }
  cleanSubs' s _ (PKVar k subs) = PKVar k $
                    subsInScope globals si (filterConSym subs s) k
  cleanSubs' _ _ e = e

-- sanitizer (1)
filterConSym subs s   = filterSubst (\_ e -> not $ isExprSym e s) subs

isExprSym (EVar s') s = s' == s
isExprSym _ _         = False

-- sanitizer (2)
subsInScope :: Foldable t => t Symbol -> SInfo a -> Subst -> KVar -> Subst
subsInScope globals si subs k =
  filterSubst (\s _ -> s `elem` kenv si k || s `elem` globals) subs

kenv :: SInfo a -> KVar -> [Symbol]
kenv si k = map (fst . flip lookupBindEnv (bs si)) $
              elemsIBindEnv . wenv =<<
              maybeToList (M.lookup k $ ws si)
--  END substitution sanitizer

isClauseRec :: [Rule] -> Rule -> Bool
isClauseRec rs = \r@(_,_,(k,_)) -> k `elem` getChildK r []
  where kmap :: M.HashMap KVar [Rule] -- memoization gives significant performance
        kmap = foldl (\acc r@(_,_,(k,_)) -> M.insertWith (++) k [r] acc) M.empty rs

        getChildK (_,cs,_) seen =
          let cks     = map (\(k,_,_) -> k) cs in
          let crules  = filter (`notElem` seen) cks >>= \r -> M.lookupDefault [] r kmap in
          foldr getChildK (cks ++ seen) crules

genKClauses :: [Rule] -> KClauses
genKClauses rules = foldr (addRule (isClauseRec rules)) M.empty rules

addRule isRec r@(_,_,(h,_)) kmap
      | isRec r = addRule' insertRec r h kmap
      | otherwise           = addRule' insertNRec r h kmap

insertRec r (rec,nrec)  = (r:rec,nrec)
insertNRec r (rec,nrec) = (rec,r:nrec)
addRule' f r h kmap     =
  let val = f r $ fromMaybe mempty (M.lookup h kmap) in
  M.insert h val kmap

-- create a map of binding and kvar sorts
symSorts :: SInfo a -> SymSorts
symSorts sinfo = M.fromList $ bindsyms ++ wfsyms
  where bindsyms = getBindSort <$> bindEnvToList (bs sinfo)
        wfsyms = getKSort <$> M.elems (ws sinfo)

getBindSort (_,s,RR sort _)         = (s,sort)
getKSort (WfC _ (_, sort, KV s) _)  = (s,sort)
-- convert SInfo to data structures used for unrolling

-- A Query is the root of the unrolling tree: subtyes of the form  Gamma /\ k_1 /\ k_2 <: { v /= 0 }
-- A Rule is the rest of the nodes of the unrolling tree, of the form Gamma /\ k_3 <: k_2
--
-- the KClauses map kvars to (recursive, nonrec) rules that correspond to them. For example it would map k_2
-- to the latter rule.

genUnrollInfo :: M.HashMap Integer (Symbol,Sort) -> SInfo a -> (SymSorts, KClauses, [Query])
genUnrollInfo csyms sinfo = (sorts, genKClauses rules, queries)
  where (rules, queries) = foldr addCon ([],[]) $ M.toList $ cm sinfo
        sorts = M.fromList (toListSEnv $ lits sinfo) `M.union` symSorts sinfo

        addCon (i,c) (rules,queries)
          | PKVar _ _ <- crhs c =
              ((getKVar . fst <$> clauseInfo (symsort i) sinfo c):rules, queries)
          | otherwise           =
              (rules, clauseInfo (symsort i) sinfo c:queries)
        symsort i = fromMaybe (dummyName,intSort) $ M.lookup i csyms

--------------
-- | UNROLLING
--------------

exprSyms :: Expr -> [Symbol]
exprSyms e  = nub $ V.fold symVisitor () [] e
  where symVisitor :: V.Visitor [Symbol] ()
        symVisitor                  = dv { V.accExpr = getSymbol }
        dv                          = V.defaultVisitor :: V.Visitor [Symbol] ()
        getSymbol _ (EVar s)        = [s]
        getSymbol _ (PKVar _ subs)  =
          let (ks, sexprs) = unzip $ substToList subs in
          ks ++ concatMap exprSyms sexprs
        getSymbol _ _               = []


-- rename instances of symbol in substitutions
renameSubst :: Symbol -> Symbol -> Subst -> Subst
renameSubst s s' subs =
  let slist  = substToList subs in
  let slist' = map renameSub slist in
  Su $ M.fromList slist'
  where renameSub (sk,se) =
          let sk' = if sk == s then s' else sk in
          let se' = renameExpr s s' se in
          (sk', se')

-- rename all instances of symbol in body
renameExpr :: Symbol -> Symbol -> Expr -> Expr
renameExpr s s' e = V.trans renameVisitor () () e
  where rename _ e@(EVar s'')
          | s == s''  = EVar s'
          | otherwise = e
        rename _ (PKVar k subs) =
          let subs'   = renameSubst s s' subs in
          PKVar k subs'
        rename _ e    = e
        renameVisitor = dv { V.txExpr = rename }
        dv            = V.defaultVisitor :: V.Visitor () ()

renameClauseChild :: Symbol -> Symbol -> ClauseChild -> ClauseChild
renameClauseChild s s' (ck,csub,csym) = (ck, newsub, newsym)
  where newsub = renameSubst s s' csub
        newsym = if csym == s then s' else csym

-- replace all instances of s in kcs with s'
renameClauses :: Symbol -> Symbol -> UnrollInfo -> UnrollInfo
renameClauses s s' (UI kcs ss am) = UI (M.fromList $ map renameK $ M.toList kcs) ss am
  where renameK (k,(rec,nrec)) = (k, (map renameRule rec, map renameRule nrec))
        renameRule (b, cs, h) =
          let b'  = renameExpr s s' b in
          let cs' = map (renameClauseChild s s') cs in
          (b', cs', h)

-- inherit the orig symbol that the variable was substituted for
newSub :: Symbol -> Symbol -> UnrollM ()
newSub s s' = do
  usubs <- unrollSubs <$> get
  let orig = maybe s id (M.lookup s usubs)
  let usubs' = M.insert s' orig usubs
  updateUnrollSubs usubs'

renameSymbol :: Symbol -> UnrollM Symbol
renameSymbol s = do
  let spref = unSuffixSymbol s
  n <- getSubCount spref
  updateSubCount spref (n+1)
  -- FIXME: change this to intSymbol
  let s' = intSymbol spref n
  cs <- createdSymbols <$> get
  msort <- getSymSort s
  -- if sort cannot be found, assume it's an int
  let sort = maybe intSort id msort
  updateCreatedSymbols (M.insert s' sort cs)
  return s'

freshSubSymbol :: UnrollM Symbol
freshSubSymbol = renameSymbol $ symbol "SUB"

generateHeadSubst :: ArgMap -> [(Symbol,Symbol)]
generateHeadSubst argmap = concatMap toHeadSubs $ M.elems argmap
  where toHeadSubs (_,Nothing) = []
        toHeadSubs (s,Just v)  = [(v,s)]

-- update argmap information and return
-- a new set of head substitutions
updateHeadSubs :: Subst -> UnrollM ([(Symbol,Symbol)], ArgMap)
updateHeadSubs hsubs = do
  am <- argmap <$> ask
  let slist = substToList hsubs
  am' <- foldM updateHeadSub am slist
  let subs = generateHeadSubst am'
  return (subs, am')
  where updateHeadSub am (s,EVar v) = do
          case M.lookup s am of
            Nothing -> return am
            Just (v',_) -> return $ M.insert s (v',Just v) am
        updateHeadSub _ _ = error "head substitution must be a variable!"

applyHeadSubsBody :: [(Symbol,Symbol)] -> Expr -> Expr
applyHeadSubsBody hsubs b = foldr (uncurry renameExpr) b hsubs

applyHeadSubsChildren :: [(Symbol,Symbol)] -> [ClauseChild] -> [ClauseChild]
applyHeadSubsChildren hsubs ccs = map applyHeadSubsChild ccs
  where applyHeadSubsChild (ck, csubs, csyms) =
          let csubs' = foldr (uncurry renameSubst) csubs hsubs in
          (ck, csubs', csyms)

updateArgMap :: Subst -> UnrollInfo -> UnrollInfo
updateArgMap subs uinfo =
  let am = argmap uinfo in
  let am' = foldr insertArg am $ substToList subs in
  uinfo { argmap = am' }
  where insertArg (s,EVar v) acc =
          let subsyms = M.keys $ M.filter (\(s',_) -> s' == s) acc in
          case subsyms of
            [] -> M.insert s (v,Nothing) acc
            xs -> foldr (\x acc2 -> M.insert x (v,Nothing) acc2) acc xs
        insertArg _ _ = error "substitution should be a variable!"

-- apply pending substitutions
applySubst :: Subst -> UnrollM (KClauses, [Expr])
applySubst subs = do
  uinfo <- ask
  (uinfo', es) <- foldM applySub1 (uinfo,[]) $ substToList subs
  return (kcs uinfo', es)

applySub1 (ui,tmpexprs) (ssym,sexpr) = do
  case sexpr of
   -- if the substitution is symbol to symbol,
   -- we don't introduce a new "tmp expr"
    EVar ssym' -> do
      tmp <- freshSubSymbol
      newSub ssym ssym'
      newSub ssym' tmp
      return (renameClauses ssym ssym' (renameClauses ssym' tmp ui), tmpexprs)

    _ -> do
      tmp <- freshSubSymbol
      newSub ssym tmp
      return (renameClauses ssym tmp ui, (PAtom Eq (EVar tmp) sexpr):tmpexprs)

-- generate disjunctive interpolation query
unroll :: UnrollDepth -> HeadInfo -> UnrollM InterpQuery
unroll dmap (k,sym) = do
  kc <- kcs <$> ask
  case M.lookup k kc of
    Nothing -> return $ Or Nothing []
    Just (crec, cnrec) -> do
      let depth = maybe 0 id (M.lookup k dmap)
      let rec = depth > 0
      let cs = if not rec then cnrec else crec ++ cnrec
      let dmap' = M.insert k (depth-1) dmap

      -- generate children
      children <- forM cs $ \(b, c, (_,hsubs)) -> do
        (hsubs2, argmap') <- updateHeadSubs hsubs
        let b1 = applyHeadSubsBody hsubs2 b
        let c1 = applyHeadSubsChildren hsubs2 c

        -- rename body to prevent capture
        sym' <- renameSymbol sym
        let b2 = renameExpr sym sym' b1
        let c2 = map (renameClauseChild sym sym') c1

        -- apply argument i.e. [nu/x]
        let b3 = renameExpr vvName sym b2
        
        local (renameClauses sym sym' . setArgMap argmap') $ do
          -- generate child subtree
          ginfo <- forM c2 $ \(ck,csub,csym) -> do
            -- if csym == VV, then it's the LHS of a constraint
            -- and so csym = the symbol on the head (i.e., sym)
            let csym' = if vvName == csym then sym else csym
            (kc'', tmps) <- applySubst csub
            local (updateArgMap csub . setKClauses kc'')$ do
              gc <- unroll dmap' (ck,csym')
              return (gc, tmps)
          
          let (gchildren, gtmps) = unzip ginfo

          -- add substitution predicates to body
          let b4 = PAnd $ b3:(concat gtmps)
          return $ And Nothing b4 gchildren

      return $ Or (Just (k,sym)) children

  where setArgMap argmap' uinfo = uinfo { argmap = argmap' }

-- we use this instead of vvName because liquid-fixpoint
-- uses vvName internally, and if we use it here we get
-- weird bugs
argName = symbol "ARG"

-- generate a disjunctive interpolation query for a query clause
unrollQuery :: Int -> Query -> UnrollM InterpQuery
unrollQuery n (b, c, (h,_)) = do
  kc <- kcs <$> ask
  let initDepths = map (\k -> (k,n)) $ M.keys kc
  let dmap = foldr (uncurry M.insert) M.empty $ initDepths

  -- rename instances of VV in query, since it's treated specially
  -- in unrolling
  v <- renameSymbol argName
  newSub vvName v
  let b' = renameExpr vvName v b 
  let c' = map (renameClauseChild vvName v) c
  let h' = renameExpr vvName v h

  -- generate child subtrees
  cinfo <- forM c' $ \(ck,csub,csym) -> do
    (kc', tmps) <- applySubst csub
    local (updateArgMap csub . setKClauses kc') $ do
      -- if csym == VV, then it's the LHS of a constraint
      -- and so csym = the symbol on the head (i.e., v)
      let csym' = if csym == vvName then v else csym
      child <- unroll dmap (ck,csym')
      return (child, tmps)

  let (children, ctmps) = unzip cinfo
  return $ And Nothing (PAnd ([PNot h', b'] ++ (concat ctmps))) children

-- compute the initial rename map for a set of clauses
-- we have to do this smartly; if there is a variable v101, then
-- we have to map v |-> 102
initRenameMap :: UnrollInfo -> RenameMap
initRenameMap (UI _ ss _) = M.map (const 1) ss

-- interface function that unwraps Unroll monad
genInterpQuery :: Int -> UnrollInfo -> Query -> (InterpQuery, SymSorts, UnrollSubs)
genInterpQuery n uinfo@(UI kcs ss am) query@(_,_,(_,argSort)) = 
  let rm = initRenameMap uinfo in
  -- we have to insert the type of "VV" (the RHS of a query)
  let ss' = M.insert argName argSort ss in
  let ustate = URS M.empty rm M.empty in
  let smonad = unrollQuery n query in
  let (diquery, URS cs _ us) = runState (runReaderT smonad (UI kcs ss' am)) ustate in
  (diquery, cs, us)

----------------------------------------------------
-- | DISJUNCTIVE INTERPOLATION TO TREE INTERPOLATION
----------------------------------------------------

-- remove OR nodes from AOTree by converting disjunctive interp query
-- to a set of tree interp queries
expandTree :: InterpQuery -> [InterpQuery]
expandTree (And info root children) =
  map (And info root) (sequence $ map expandTree children)
expandTree (Or info children) =
  children >>= expandOr info
  where expandOr info (And _ root children) =
          expandTree (And info root children)
        expandOr _ t = expandTree t

-- generate a tree interp query
-- there shouldn't be an OR node processed in the tree
genQueryFormula :: InterpQuery -> Expr
genQueryFormula (Or _ children) =
  POr (map genQueryFormula children)
genQueryFormula (And _ root children) =
  PAnd $ root:(map genQueryFormula' children)
  where genQueryFormula' c@(And _ _ _) = Interp $ genQueryFormula c
        genQueryFormula' c@(Or _ _) = genQueryFormula c

----------------------------------------
-- | TREE INTERPOLANTS TO KVAR SOLUTIONS
----------------------------------------

popInterp :: State [Expr] Expr
popInterp = do
  (x:xs) <- get
  put xs
  return x

-- construct a tree interpolant from a list of interpolants
-- returned by Z3
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

-- map a tree interpolant to candidate solutions
-- we do this by substituting the following at an interpolant:
-- * the symbol at the head |--> v (or nu)
-- * sub symbols (e.g. tmp) generated from unrolling |--> original symbol
extractSol :: Subst -> TreeInterp -> CandSolutions
extractSol usubs t =
  let subtree = mapAOTree (\i e -> subUnroll i $ subNu i e) t in 
  collectSol subtree M.empty
  where subUnroll _ = (subst :: Subst -> Expr -> Expr) usubs
        subNu (Just (_, sym)) e =
          flip (subst1 :: Expr -> (Symbol,Expr) -> Expr) (sym,EVar vvName) e
        subNu Nothing e = e
        collectSol (And Nothing _ children) m = 
          foldr collectSol m children
        collectSol (And (Just (k,_)) v children) m =
          let m' = M.insertWith (++) k [v] m in 
          foldr collectSol m' children
        -- this is supposed to be called on tree interps only,
        -- so we set a dummy value for OR nodes
        collectSol (Or _ _) m = m

-- manually run tree interpolation here in pieces
-- this is to prune the tree query, since many queries
-- have huge numbers of variables
-- the idea is to run DFS on the tree, computing interpolants for each
-- node one by one and then for each interpolation query discarding
-- binders that are redundant within one side of a cut

genCandSolutions :: Fixpoint a => SInfo a -> UnrollSubs -> InterpQuery -> IO CandSolutions
genCandSolutions sinfo u dquery = do
  -- convert disjunctive interp query to a set of tree interp queries
  let tqueries = expandTree dquery
  tinterps <- forM tqueries $ \tquery -> do
    -- let sinfo = either die id $ sanitize $ convertFormat finfo
    -- let sinfo = convertFormat finfo
    let formula = genQueryFormula tquery
    -- putStrLn "Tree Interp query:"
    -- putStrLn $ show formula
    let smap = foldr (\s acc -> (uncurry M.insert) (uninternSym s) acc) M.empty (exprSyms formula)
    interps <- interpolation (def :: Config) sinfo formula
    -- unintern symbols
    let interps' = map (cleanSymbols smap) interps
    let tinterp = evalState (genTreeInterp tquery) $ interps' ++ [PFalse]
    return tinterp

  let usubs   = Su $ M.fromList $ map (\(x,orig) -> (x,EVar orig)) $ M.toList u
  let cands   = map (extractSol usubs) tinterps 
  let cands'  = foldr (M.unionWith (uniqAdd)) M.empty cands
  -- let cands'' = M.fromList $ map (\(k,exprs) -> (k,map numberifyCand exprs)) cands'
  return cands'
  where uniqAdd a b = nub $ a ++ b
        uninternSym s =
          let uninterned = symbol $ encode $ symbolText s in
          (uninterned, s)
        cleanSymbols smap e = foldr (uncurry renameExpr) e (M.toList smap)

qarg = symbol "QARG"
        
renameQualParams :: Qualifier -> Qualifier
-- rename params so that redundant qualifiers may be discarded
renameQualParams (Q name params body loc) =
  let n = length params in
  let renamedParams = map (intSymbol qarg) [1..n] in
  let zipParam      = zip params renamedParams in
  let newParams     = map (\((_,sort),sym') -> (sym',sort)) zipParam in
  let subs          = mkSubst $ map (uncurry paramSubst) zipParam in
  Q name newParams (subst subs body) loc
  where paramSubst (sym,_) sym' = (sym, EVar sym')

exprToQual :: (Symbol -> Sort) -> Expr -> [Qualifier]
exprToQual symsort e =
  let syms        = exprSyms e in
  let params      = map (\s -> (s,symsort s)) syms in
  -- don't include uninterpreted functions as parameters!
  let params'     = filter (not . isFunc . snd) params in
  let params''    = paramSorts 0 M.empty params' in
  -- let params''    = map (\(i,(p,s)) -> (p,realSort i s)) (zip [1..] params') in
  let loc         = dummyPos "no location" in
  let name        = dummySymbol in
  -- trace ("PARAMS:" ++ show params') $ map (\p -> Q name p e loc) (permutations params'')
  map (\p -> Q name p e loc) (permutations params'')
  where -- convert tySort to a variable type
        -- FIXME: Ask Jhala about this
        -- realSort _ _          = FVar 0
        -- realSort FNum      = FNum
        -- realSort (FTC _)   = 
        -- realSort x         = x
        paramSorts _ _ []     = []
        paramSorts i m ((p,s):pps) =
          case M.lookup s m of
            Nothing -> (p,FVar i):(paramSorts (i+1) (M.insert s i m) pps)
            Just n -> (p,FVar n):(paramSorts i m pps)
        isFunc s              = maybe False (const True) (functionSort s)
        -- isFunc s          = False

sanitizeQualifiers :: [Qualifier] -> [Qualifier]
sanitizeQualifiers quals = 
  let validQuals = filter validQual quals in
  let quals      = map renameQualParams validQuals in
  nub $ quals
  where validQual q = hasArgs q && nonTrivial q && nonVar q
        -- qualifier is not a kvar or a regular var
        nonVar (Q _ _ (PKVar _ _) _) = False
        nonVar (Q _ _ (EVar _) _)    = False
        nonVar (Q _ _ _ _)           = True
        -- don't add true or false as qualifiers
        nonTrivial q
          | Q _ _ (PAnd []) _ <- q  = False
          | Q _ _ PTrue _ <- q      = False
          | Q _ _ (POr []) _ <- q   = False
          | Q _ _ PFalse _<- q      = False
          | otherwise               = True
        hasArgs (Q _ (_:_) _ _) = True
        hasArgs (Q _ [] _ _)    = False


maxDisj = 3

-- generate qualifiers from candidate solutions
-- ss should contain the sorts for
-- * kvars
-- * created variables during unrolling
-- * variables in finfo
extractQualifiers :: SymSorts -> CandSolutions -> [Qualifier]
extractQualifiers ss cs = sanitizeQualifiers $ concatMap kquals (M.toList cs)
  where kquals (k,es) =
          let atoms = nub $ concatMap atomicExprs (es :: [Expr]) in
          -- create disjunction of qualifiers
          let exprs = if length atoms > 1 && length atoms <= maxDisj
                      then (POr atoms):atoms else atoms in
          concatMap (concatMap (exprToQual (symSort k)). atomicExprs) exprs
        -- get atomic expressions from conjunctions and disjunctions
        -- we want qualifiers to be simple (atomic) predicates
        ksym (KV k) = k
        symSort k s =
          let ksort = maybe intSort id (M.lookup (ksym k) ss) in
          let ssort = maybe intSort id (M.lookup s ss) in
          if s == vvName then ksort else ssort

queryQuals :: SymSorts -> [Query] -> [Qualifier]
queryQuals ss queries =
  sanitizeQualifiers $ concatMap (concatMap (exprToQual symSort) . atomicExprs . queryHead) queries
  where queryHead (_, _, (e,_)) = e
        symSort s = maybe intSort id (M.lookup s ss)

genQualifiers :: Fixpoint a => M.HashMap Integer (Symbol,Sort) -> SInfo a -> Int -> IO [Qualifier]
genQualifiers csyms sinfo n = do
  let (ss, kcs, queries) = genUnrollInfo csyms sinfo
  {-
  putStrLn "BindEnv:"
  putStrLn $ show $ bs finfo
  putStrLn "Lits::"
  putStrLn $ show $ lits finfo
  putStrLn "KClauses:"
  printKClauses kcs
  -}
  quals  <- forM queries $ \query -> do
    -- unroll
    let (diquery, cs, usubs) = genInterpQuery n (UI kcs ss M.empty) query
    {-
    putStrLn "Interp query:"
    putStrLn $ show $ genQueryFormula diquery
    putStrLn "Created symbols:"
    putStrLn $ show cs
    putStrLn "usubs:"
    putStrLn $ show usubs
    -}

    -- add created vars back to finfo
    -- let vars = toListSEnv (lits finfo)
    -- let allvars = M.union (M.fromList vars) cs
    let allvars = M.union ss cs
    let si' = sinfo { lits = fromListSEnv (nub $ M.toList allvars) }
    {-
    putStrLn "AFTER Lits:"
    print (lits si')
    putStrLn "AFTER BindEnv:"
    print (bs si')
    -}

    -- run tree interpolation to compute possible kvar solutions
    candSol <- genCandSolutions si' usubs diquery
    {-
    putStrLn "candidate solutions:"
    putStrLn $ show candSol
    -}

    -- extract qualifiers 
    return $ extractQualifiers allvars candSol

  let rhsQuals = queryQuals ss queries
  let allquals = nub $ concat $ rhsQuals:quals
  -- let allquals2 = nub $ concat $ [rhsQuals]
  -- putStrLn "RHSQUALS:"
  -- forM rhsQuals print
  -- putStrLn "INTERP QUALS:"
  -- forM (concat quals) print
  return $ nub $ allquals
  {-
  let rhsQuals = catMaybes $ rhsQual (snd<$>csyms) <$> M.toList (cm sinfo)
  return $ nub $ concat $ rhsQuals:quals
  -}

imain n = do
  let ksym = symbol "k"
  let ssym = symbol "s"
  {-
  let vsym = symbol "v"
  let vars = [(ksym,intSort),(vvName,intSort),(ssym,intSort),
              (vsym,intSort)]
  -}
  -- FInfo, used for generating SMT context (var declarations, etc.)

  let int i = ECon (I i)
  let ksum = KV (symbol "sum")
  let k = EVar ksym
  let s = EVar ssym
  let v = EVar vvName
  -- let v' = EVar vsym
  let r1 = (PAnd [PAtom Le k (int 0),PAtom Eq v (int 0)], [], (ksum,Su M.empty))
  let childr2 = [(ksum, Su $ M.fromList [(ksym,EBin Minus k (int 1))], ssym)]
  let r2 = (PAnd [PAtom Gt k (int 0),PAtom Eq v (EBin Plus s k)], childr2, (ksum,Su M.empty))
  let rules = [r1,r2]
  let kcs = genKClauses rules
  let query = (PTrue, [(ksum, Su $ M.empty, vvName)], (PAtom Ge v k, intSort))
  let uinfo = UI kcs M.empty M.empty
  let (diquery, _, _) = genInterpQuery n uinfo query
  let tiqueries = expandTree diquery
  forM tiqueries $ \tiquery -> do
    putStrLn "tiquery:"
    print tiquery
    putStrLn "cuts:"
    -- print $ generateCuts tiquery

