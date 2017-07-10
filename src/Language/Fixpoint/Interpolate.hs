-- | This module uses Craig interpolation to compute qualifiers
  -- Q name (reverse params'') e loc
-- | that can be used to solve constraint sets
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

module Language.Fixpoint.Interpolate ( genQualifiers ) where

import qualified Data.HashMap.Strict as M
import Data.List (intercalate, nub, permutations)
import Data.Maybe (fromMaybe, maybeToList, isNothing, catMaybes)
import Data.Function ((&))
import qualified Data.Set as Set

import Control.Arrow ((&&&), (>>>), second)
import Control.Monad.State
import Control.Monad.Reader

import System.Console.CmdArgs (def)
import Language.Fixpoint.Types hiding (renameSymbol)
import Language.Fixpoint.Solver.Solve (interpolation, solverInfo)
import qualified Language.Fixpoint.Types.Visitor as V



data AOTree b a = And b a [AOTree b a]
                | Or b [AOTree b a]

instance (Show a, Show b) => Show (AOTree b a) where
  show (And b a children) = "And " ++ show b ++ " " ++ show a ++
                            " [" ++ intercalate "," (show <$> children) ++ "]"
  show (Or b children) = "Or " ++ show b ++ " " ++
                         " [" ++ intercalate "," (show <$> children) ++ "]"

instance (Eq a, Eq b) => Eq (AOTree b a) where
  (And x1 y1 c1) == (And x2 y2 c2)  = x1 == x2 && y1 == y2 && c1 == c2
  (Or x1 c1) == (Or x2 c2)          = x1 == x2 && c1 == c2
  And{} == Or{}                     = False
  Or{} == And{}                     = False

mapAOTree :: (b -> a -> c) -> AOTree b a -> AOTree b c
mapAOTree f (And i n children) = And i (f i n) $ map (mapAOTree f) children
mapAOTree f (Or i children) = Or i $ map (mapAOTree f) children



instance Functor ((,,) a b) where
  fmap f (a,b,c) = (a,b,f c)



-- the corresponding HC head of a node (non-root nodes correspond to HC bodies)
type HeadInfo = (KVar, Symbol)
type Interp = AOTree (Maybe HeadInfo) Expr
type CandSolutions = M.HashMap KVar [Expr]
-- body, children, head (computed from SubC)
type ClauseChild = (KVar, Subst, Symbol)
type Rule = (Expr, [ClauseChild], (KVar, Subst))
type Query = (Expr, [ClauseChild], (Expr,Sort))
-- new substitutions generated from unrolling ( v |-> tmp_v )
type UnrollSubs = M.HashMap Symbol Symbol
-- mapping from kvars to rec/nonrec-clauses with head as the kvar
type KClauses = M.HashMap KVar ([Rule], [Rule])
type SymSorts = M.HashMap Symbol Sort
type ArgMap   = M.HashMap Symbol (Symbol, Maybe Symbol)
data UnrollInfo = UI {
                    kcs :: KClauses
                  , ss :: SymSorts
                  , argmap :: M.HashMap Symbol (Symbol, Maybe Symbol)
                  }
type RenameMap = M.HashMap Symbol Int
data UnrollState = URS { createdSymbols :: SymSorts
                       , renameMap :: RenameMap
                       , unrollSubs :: UnrollSubs
                       }
type UnrollM a = ReaderT UnrollInfo (State UnrollState) a

-- UnrollInfo get/set
---------------------
setKClauses kcs (UI _ ss am) = UI kcs ss am
setArgMap argmap' uinfo = uinfo { argmap = argmap' }
updateArgMap subs uinfo =
  uinfo { argmap = foldr insertArg (argmap uinfo) $ substToList subs }

-- FIXME: this seems very slow... is it?
insertArg (s,EVar v) am =
  case M.keys $ M.filter ((== s).fst) am of
    [] -> M.insert s (v,Nothing) am
    xs -> foldr (`M.insert` (v,Nothing)) am xs
insertArg _ _ = error "substitution should be a variable!"

-- UnrollM get/set
------------------
getSymSort :: Symbol -> UnrollM (Maybe Sort)
getSymSort s = do
  ss <- ss <$> ask
  case M.lookup s ss of
    Just sort -> return (Just sort)
    Nothing -> M.lookup s . createdSymbols <$> get
getSubCount :: Symbol -> UnrollM Int
-- FIXME: CHECK IF s has number suffix
getSubCount s = M.lookupDefault 1 (tidySymbol s) . renameMap <$> get

updateRenameMap :: RenameMap -> UnrollM ()
updateRenameMap rm = modify $ \x -> x {renameMap = rm}
updateCreatedSymbols :: SymSorts -> UnrollM ()
updateCreatedSymbols cs = modify $ \x -> x {createdSymbols = cs}
updateUnrollSubs :: UnrollSubs -> UnrollM ()
updateUnrollSubs us = modify $ \x -> x {unrollSubs = us}
updateSubCount :: Symbol -> Int -> UnrollM ()
updateSubCount s n = updateRenameMap =<< M.insert s n . renameMap <$> get

-- Misc functions
-----------------

interpLoc   = dummyPos "interpolated"
maxDisj = 3
qarg = symbol "QARG"
argName = symbol "ARG"

ordNub :: (Ord a) => [a] -> [a]
ordNub l = go Set.empty l
  where
    go _ [] = []
    go s (x:xs) = if x `Set.member` s then go s xs
                                      else x : go (Set.insert x s) xs
substToList :: Subst -> [(Symbol, Expr)]
substToList (Su map) = M.toList map

atomicExprs :: Expr -> [Expr]
atomicExprs (PAnd ps) = ps >>= atomicExprs
atomicExprs e         = [e]

isExprSym (EVar s') s = s' == s
isExprSym _ _         = False

isKVar :: Expr -> Bool
isKVar (PKVar _ _)    = True
isKVar _              = False

kenv :: SInfo a -> KVar -> [Symbol]
kenv si k = map (fst . flip lookupBindEnv (bs si)) $
              elemsIBindEnv . wenv =<<
              maybeToList (M.lookup k $ ws si)

exprSyms :: Expr -> [Symbol]
exprSyms = nub . V.fold (dv { V.accExpr = getSymbol }) () []
  where dv = V.defaultVisitor :: V.Visitor [Symbol] ()

getSymbol _ (EVar s)       = [s]
getSymbol _ (PKVar _ subs) = ks ++ (sexprs >>= exprSyms)
  where (ks, sexprs) = unzip $ substToList subs
getSymbol _ _              = []

isNotFunc s = isNothing $ functionSort s

validQual q = hasArgs q && nonTrivial q && nonVar q
-- qualifier is not a kvar or a regular var
-- shouln't need this... @TODO fix what breaks when we don't
nonVar (Q _ _ (PKVar _ _) _) = False
nonVar (Q _ _ (EVar _) _)    = False
nonVar  Q{}                  = True
-- don't add true or false as qualifiers
nonTrivial q
  | Q _ _ (PAnd []) _ <- q  = False
  | Q _ _ PTrue _ <- q      = False
  | Q _ _ (POr []) _ <- q   = False
  | Q _ _ PFalse _<- q      = False
  | otherwise               = True
hasArgs (Q _ (_:_) _ _) = True
hasArgs (Q _ [] _ _)    = False

--------------------------------
-- | PRELIMINARIES FOR UNROLLING
--------------------------------

getKVar :: Expr -> (KVar, Subst)
getKVar (PKVar k s)   = (k, s)
getKVar e             = error $ "expr " ++ show e ++ " is not a kvar"

bindSym :: BindEnv -> BindId -> Symbol
bindSym env id = fst $ lookupBindEnv id env

bsym symrhs s = if s == symrhs then vvName else s

clauseInfo :: (Symbol,Sort) -> SInfo a -> SimpC a -> Query
clauseInfo (symrhs,sortrhs) sinfo c = (PAnd body, kvars, (rhs,sortrhs))
  where body     = filter (not . isKVar) . fst =<< bindings
        kvars    = getKVarSym =<< bindings
        rhs      = cleanSubs globals sinfo $ subst1 (crhs c) (symrhs, EVar vvName)

        bindings :: [([Expr], Symbol)]
        bindings = (filter cleanExprs . substVv . (atomicExprs =<<) . lookupBind
                           &&& bsym symrhs . bindSym (bs sinfo)) <$>
                   elemsIBindEnv (senv c)

        lookupBind :: BindId -> [Expr]
        lookupBind = bindExprs $ bs sinfo
        substVv    = map (`subst1` (symrhs, EVar vvName))

        globals           = fst <$> toListSEnv (gLits sinfo)
        getKVarSym (es,s) = packHead s <$> filter isKVar es
        packHead s pk     = (k, subsInScope globals sinfo (filterConSym e s) k, s)
          where (k,e) = getKVar pk

bindExprs :: BindEnv -> BindId -> [Expr]
bindExprs be i = [p `subst1` (v, eVar x) | Reft (v, p) <- rs ]
  where
    (x, sr)          = lookupBindEnv i be
    rs               = reftConjuncts $ sr_reft sr

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
-- finfo gLits
cleanSubs globals si = V.trans (subVisitor vvName) () ()
  where
  subVisitor s          = V.defaultVisitor { V.txExpr = cleanSubs' s }
  cleanSubs' s _ (PKVar k subs) = PKVar k $
                    subsInScope globals si (filterConSym subs s) k
  cleanSubs' _ _ e = e

-- sanitizer (1)
filterConSym subs s   = filterSubst (\_ e -> not $ isExprSym e s) subs

-- sanitizer (2)
subsInScope :: Foldable t => t Symbol -> SInfo a -> Subst -> KVar -> Subst
subsInScope globals si subs k =
  filterSubst (\s _ -> s `elem` kenv si k || s `elem` globals) subs

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
      | isRec r = addRule' (insertRec r) h kmap
      | otherwise           = addRule' (insertNRec r) h kmap

insertRec r (rec,nrec)  = (r:rec,nrec)
insertNRec r (rec,nrec) = (rec,r:nrec)

addRule' f h kmap = M.insert h (f $ M.lookupDefault mempty h kmap) kmap

-- create a map of binding and kvar sorts
symSorts :: SInfo a -> SymSorts
symSorts sinfo = M.fromList $ bindsyms ++ wfsyms
  where bindsyms = getBindSort <$> bindEnvToList (bs sinfo)
        wfsyms = getKSort <$> M.elems (ws sinfo)

getBindSort (_,s,RR sort _)         = (s,sort)
getKSort (WfC _ (_, sort, KV s) _)  = (s,sort)
getKSort (GWfC _ (_, sort, KV s) _ _ _)  = (s,sort)
-- convert SInfo to data structures used for unrolling

-- A Query is the root of the unrolling tree: subtyes of the form  Gamma /\ k_1 /\ k_2 <: { v /= 0 }
-- A Rule is the rest of the nodes of the unrolling tree, of the form Gamma /\ k_3 <: k_2
--
-- the KClauses map kvars to (recursive, nonrec) rules that correspond to them. For example it would map k_2
-- to the latter rule.

genUnrollInfo :: M.HashMap Integer (Symbol,Sort) -> SInfo a -> (SymSorts, KClauses, [Query])
genUnrollInfo csyms sinfo = (sorts, genKClauses rules, queries)
  where (rules, queries) = foldr addCon ([],[]) $ M.toList $ cm sinfo
        sorts = M.fromList (toListSEnv $ gLits sinfo) `M.union` symSorts sinfo

        addCon (i,c) (rules,queries)
          | PKVar _ _ <- crhs c =
              ((getKVar . fst <$> clauseInfo (symsort i) sinfo c):rules, queries)
          | otherwise           =
              (rules, clauseInfo (symsort i) sinfo c:queries)
        symsort i = fromMaybe (dummyName,intSort) $ M.lookup i csyms

--------------
-- | UNROLLING
--------------

-- rename instances of symbol in substitutions
renameSubst :: Symbol -> Symbol -> Subst -> Subst
renameSubst s s' subs = Su . M.fromList $ renameSub <$> substToList subs
  where renameSub (sk,se) = (if sk == s then s' else sk, renameExpr s s' se)

-- rename all instances of symbol in body
renameExpr :: Symbol -> Symbol -> Expr -> Expr
renameExpr s s' = V.trans (dv { V.txExpr = rename }) () ()
  where rename _ e@(EVar s'')
          | s == s''  = EVar s'
          | otherwise = e
        rename _ (PKVar k subs) = PKVar k $ renameSubst s s' subs
        rename _ e    = e
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
  updateUnrollSubs $ M.insert s' (M.lookupDefault s s usubs) usubs

renameSymbol :: Symbol -> UnrollM Symbol
renameSymbol s = do
  let spref = tidySymbol s
  n <- getSubCount spref
  updateSubCount spref (n+1)
  let s' = intSymbol spref n
  cs <- createdSymbols <$> get
  msort <- getSymSort s
  -- if sort cannot be found, assume it's an int
  let sort = fromMaybe (error $ "renameSymbol: Sort not found " ++ show s') msort
  updateCreatedSymbols (M.insert s' sort cs)
  return s'

generateHeadSubst :: ArgMap -> [(Symbol,Symbol)]
generateHeadSubst am = catMaybes $ (\(a,b) -> (,a)<$>b) <$> M.elems am

-- update argmap information and return
-- a new set of head substitutions
updateHeadSubs :: Subst -> M.HashMap Symbol (Symbol, Maybe Symbol) -> ([(Symbol,Symbol)], ArgMap)
updateHeadSubs hsubs am = (generateHeadSubst &&& id) (foldl updateHeadSub am $ substToList hsubs)

updateHeadSub am (s,EVar v) =
  case M.lookup s am of
    Nothing -> am
    Just (v',_) -> M.insert s (v',Just v) am
updateHeadSub _ _ = error "head substitution must be a variable!"

applyHeadSubsBody :: [(Symbol,Symbol)] -> Expr -> Expr
applyHeadSubsBody hsubs b = foldr (uncurry renameExpr) b hsubs

applyHeadSubsChildren :: [(Symbol,Symbol)] -> [ClauseChild] -> [ClauseChild]
applyHeadSubsChildren hsubs = map applyHeadSubsChild
  where applyHeadSubsChild (ck, csubs, csyms) = (ck, csubs', csyms)
           where csubs' = foldr (uncurry renameSubst) csubs hsubs

-- apply pending substitutions
applySubst :: Subst -> UnrollM (KClauses, [Expr])
applySubst subs = do
  uinfo <- ask
  (uinfo', es) <- foldM applySub1 (uinfo,[]) $ substToList subs
  return (kcs uinfo', es)

-- FIXME: black magic
applySub1 (ui,tmpexprs) (ssym,sexpr) =
  case sexpr of
    EVar ssym' -> do
      tmp <- renameSymbol ssym
      newSub ssym ssym'
      newSub ssym' tmp
      return (renameClauses ssym ssym' (renameClauses ssym' tmp ui), tmpexprs)

    _ -> do
      tmp <- renameSymbol ssym
      newSub ssym tmp
      return (renameClauses ssym tmp ui, PAtom Eq (EVar tmp) sexpr:tmpexprs)

type UnrollDepth = M.HashMap KVar Int
-- generate disjunctive interpolation query
unroll :: UnrollDepth -> HeadInfo -> UnrollM Interp
unroll dmap (k,sym) = (kcs <$> ask >>=) $ M.lookup k >>> \case
  Nothing -> return $ Or Nothing []
  Just (crec, cnrec) ->
    let depth = M.lookupDefault 0 k dmap in
    let cs = if depth > 0 then crec ++ cnrec else cnrec in
    let dmap' = M.insert k (depth-1) dmap in

    -- generate children
    Or (Just (k,sym)) <$> forM cs (\(b, c, (_,hsubs)) -> do
      am <- argmap <$> ask
      let (hsubs2, argmap') = updateHeadSubs hsubs am
      -- rename body to prevent capture
      sym' <- renameSymbol sym
      let c' = renameClauseChild sym sym' <$> applyHeadSubsChildren hsubs2 c
      -- apply argument i.e. [nu/x]
      let b' = renameExpr vvName sym $ renameExpr sym sym' $ applyHeadSubsBody hsubs2 b

      local (renameClauses sym sym' . setArgMap argmap') $ do
        (gchildren, gtmps) <- fmap unzip $ forM c' $ \(ck,csub,csym) ->
           collect csub $ unroll dmap' (ck,if vvName == csym then sym else csym)
        return $ And Nothing (PAnd $ b':concat gtmps) gchildren)

-- generate a disjunctive interpolation query for a query clause
unrollQuery :: Int -> Query -> UnrollM Interp
unrollQuery n (b, c, (h,_)) = do
  kc <- kcs <$> ask
  let dmap = foldr (uncurry M.insert) M.empty $ (,n) <$> M.keys kc

  -- rename instances of VV in query, since it's treated specially
  -- in unrolling
  v <- renameSymbol argName
  newSub vvName v
  let b' = renameExpr vvName v b
  let c' = renameClauseChild vvName v <$> c
  let h' = renameExpr vvName v h

  -- generate child subtrees
  (children, ctmps) <- fmap unzip $ forM c' $ \(ck,csub,csym) ->
    -- if csym == VV, then it's the LHS of a constraint
    -- and so csym = the symbol on the head (i.e., v)
    collect csub $ unroll dmap (ck,if csym == vvName then v else csym)
  -- add substitution predicates to body
  return $ And Nothing (PAnd ([PNot h', b'] ++ concat ctmps)) children

collect :: Subst -> UnrollM t -> UnrollM (t, [Expr])
collect csub urm = do
    (kc', tmps) <- applySubst csub
    local (updateArgMap csub . setKClauses kc') $ (,tmps) <$> urm

-- interface function that unwraps Unroll monad
genInterpQuery :: Int -> UnrollInfo -> Query -> (Interp, SymSorts, UnrollSubs)
genInterpQuery n (UI kcs ss am) query@(_,_,(_,argSort)) = (diquery, cs, us)
  where
  (diquery, URS cs _ us) = runState (runReaderT (unrollQuery n query)
                             $ UI kcs ss' am) $ URS M.empty rm M.empty
  rm = const 1 <$> ss
  ss' = M.insert argName argSort ss

----------------------------------------------------
-- | DISJUNCTIVE INTERPOLATION TO TREE INTERPOLATION
----------------------------------------------------

-- remove OR nodes from AOTree by converting disjunctive interp query
-- to a set of tree interp queries
expandTree :: Interp -> [Interp]
expandTree (And info root children) =
  And info root <$> mapM expandTree children
expandTree (Or info children) =
  children >>= expandOr info
  where expandOr info (And _ root children) =
          expandTree (And info root children)
        expandOr _ t = expandTree t

-- generate a tree interp query
-- there shouldn't be an OR node processed in the tree
genQueryFormula :: Interp -> Expr
genQueryFormula (Or _ children) =
  POr $ genQueryFormula <$> children
genQueryFormula (And _ root children) =
  PAnd $ root:(genQueryFormula' <$> children)
  where genQueryFormula' c@And{} = Interp $ genQueryFormula c
        genQueryFormula' c@Or{} = genQueryFormula c

----------------------------------------
-- | TREE INTERPOLANTS TO KVAR SOLUTIONS
----------------------------------------

popInterp :: State [Expr] Expr
popInterp = state $ \(x:xs) -> (x,xs)

-- construct a tree interpolant from a list of interpolants
-- returned by Z3
genTreeInterp query = evalState (go query) . (++ [PFalse])
  where go :: Interp -> State [Expr] Interp
        go (And info _ children) = flip (And info) <$> mapM go children <*> popInterp
           -- this is for tree interpolants, so we don't
           -- do anything for OR nodes
        go (Or info children) = Or info <$> mapM go children

-- map a tree interpolant to candidate solutions
-- we do this by substituting the following at an interpolant:
-- * the symbol at the head |--> v (or nu)
-- * sub symbols (e.g. tmp) generated from unrolling |--> original symbol
extractSol :: Subst -> Interp -> CandSolutions
extractSol usubs t = collectSol (mapAOTree (\i e -> subUnroll $ subNu i e) t) M.empty
  where subUnroll = subst usubs
        subNu (Just (_, sym)) e = subst1 e (sym,EVar vvName)
        subNu Nothing e = e
        collectSol (And Nothing _ children) m =
          foldr collectSol m children
        collectSol (And (Just (k,_)) v children) m =
          let m' = M.insertWith (++) k [v] m in
          foldr collectSol m' children
        -- this is supposed to be called on tree interps only,
        -- so we set a dummy value for OR nodes
        collectSol (Or _ _) m = m

genCandSolutions :: Fixpoint a => SInfo a -> UnrollSubs -> Interp -> IO CandSolutions
genCandSolutions sinfo u dquery =
  -- FIXME: This `nub` might be slow
  foldr (M.unionWith (nub & fmap.fmap $ (++))) M.empty <$>
  forM (expandTree dquery) (\tquery ->
    extractSol (Su $ M.fromList $ second EVar <$> M.toList u) .
    genTreeInterp tquery <$>
    interpolation def sI sinfo (genQueryFormula tquery))
  where sI = solverInfo def sinfo

renameQualParams :: Qualifier -> Qualifier
renameQualParams (Q name params body loc) = Q name newParams newBody loc
  where zipParam      = zip params $ intSymbol qarg <$> [1 .. length params]
        newParams     = (\((_,sort),sym') -> (sym',sort)) <$> zipParam
        newBody       = subst (mkSubst $ paramSubst <$> zipParam) body
paramSubst ((sym,_), sym') = (sym, EVar sym')

exprToQual :: M.HashMap Symbol Sort -> Expr -> [Qualifier]
exprToQual symsort e = (\p -> Q dummySymbol p e interpLoc) <$> permutations params
  where -- don't include uninterpreted functions as parameters!
        params    = filter (isNotFunc . snd) $
                      (id &&& lookupSymsort) <$> exprSyms e
        lookupSymsort s = M.lookupDefault intSort s symsort

sanitizeQualifiers :: [Qualifier] -> [Qualifier]
sanitizeQualifiers quals = nub $ renameQualParams <$> filter validQual quals

extractQualifiers :: SymSorts -> CandSolutions -> [Qualifier]
extractQualifiers ss cs = sanitizeQualifiers $ kquals =<< M.toList cs
  where kquals (k,es) = let atoms = nub $ atomicExprs =<< es in
                         -- create disjunction of qualifiers (evil hack)
                        let expr = if length atoms > 1 && length atoms <= maxDisj
                                     then POr atoms : atoms
                                     else atoms in
                        exprToQual (symSort k) =<< atomicExprs =<< expr
        symSort k = M.insert vvName (M.lookupDefault (error "exprToPred: no such KV")
                                                     (kv k) ss)
                                    ss

queryQuals :: SymSorts -> [Query] -> [Qualifier]
queryQuals ss queries = sanitizeQualifiers $ do
    query <- queries
    e <- atomicExprs $ queryHead query
    exprToQual (symSort query) e
  where queryHead (_, _, (e,_)) = e
        symSort (_,_,(_,s)) = M.insert vvName s ss

genQualifiers :: Fixpoint a => M.HashMap Integer (Symbol,Sort) -> SInfo a -> Int -> IO [Qualifier]
genQualifiers csyms sinfo n = nub . concat . (rhsQuals:) <$>
  forM queries (\query ->
    -- unroll
    let (diquery, ssyms, usubs) = genInterpQuery n (UI kcs ss M.empty) query in
    -- add created vars back to finfo
    let allvars = M.union ss ssyms in
    let si' = sinfo { gLits = fromListSEnv (ordNub $ M.toList allvars) } in
    -- run tree interpolation to compute possible kvar solutions
    extractQualifiers allvars <$> genCandSolutions si' usubs diquery)
  where (ss, kcs, queries) = genUnrollInfo csyms sinfo
        -- Ranjit's "seeding" trick
        rhsQuals = queryQuals ss queries
