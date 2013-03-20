
-- | This module has the functions that perform sort-checking, and related
-- operations on Fixpoint expressions and predicates.

module Language.Fixpoint.Sort  ( 
  -- * Checking Well-Formedness
    checkSortedReft
  , checkSortedReftFull
  ) where

import Language.Fixpoint.Types
import Language.Fixpoint.Misc
import Text.PrettyPrint.HughesPJ
import Text.Printf
import Control.Monad.Error (throwError)
import Control.Monad
import Control.Applicative


-- | Types used throughout checker

type CheckM a = Either String a
type Env      = Symbol -> Maybe Sort
fBool         = FApp boolFTyCon [] 
fProp         = FApp propFTyCon [] 

-------------------------------------------------------------------------
-- | Checking Refinements -----------------------------------------------
-------------------------------------------------------------------------

checkSortedReft :: SEnv SortedReft -> [Symbol] -> SortedReft -> Maybe Doc
checkSortedReft env xs sr = applyNonNull Nothing error unknowns 
  where 
    error                 = Just . (text "Unknown symbols:" <+>) . toFix 
    unknowns              = [ x | x <- syms sr, not (x `elem` v : xs), not (x `memberSEnv` env)]    
    Reft (v,_)            = sr_reft sr 

checkSortedReftFull :: SEnv SortedReft -> SortedReft -> Maybe Doc
checkSortedReftFull = error "TODO: HEREHEREHEREHEREHEREHEREHEREHERE"

-------------------------------------------------------------------------
-- | Checking Expressions -----------------------------------------------
-------------------------------------------------------------------------

checkExpr                  :: Env -> Expr -> CheckM Sort 

checkExpr _ EBot           = throwError "Type Error: Bot"
checkExpr _ (ECon _)       = return FInt 
checkExpr f (EVar x)       = checkSym f x
checkExpr f (EBin o e1 e2) = checkOp f e1 o e2
checkExpr f (EIte p e1 e2) = checkIte f p e1 e2
checkExpr f (ECst e t)     = checkCst f e t
checkExpr f (EApp g es)    = checkApp f Nothing g es
checkExpr f (ELit _ t)     = return t

-- | Helper for checking symbol occurrences

checkSym f x               
  = maybe (throwError $ errUnbound x) return (f x)

-- | Helper for checking if-then-else expressions

checkIte f p e1 e2 
  = do tp <- checkPred p
       t1 <- checkExpr e1
       t2 <- checkExpr e2
       if t1 == t2 
         then return t1
         else throwError (errIte e1 e2 t1 t2) 

-- | Helper for checking cast expressions 

checkCst f t (EApp g es) 
  = checkApp f (Just t) g es
checkCst f t e           
  = do t' <- checkExpr f e
       if t == t' 
         then return t
         else throwError (errCast e t' t)

-- | Helper for checking uninterpreted function applications

checkApp' f to g es 
  = do gt           <- checkSym f g
       (n, its, ot) <- sortFunction gt
       unless (length its == length es) $ throwError (errArgArity g its es)
       ets          <- mapM (checkExpr f) es
       θ            <- unify its ets
       let t         = apply θ ot
       case to of
         Nothing    -> return (θ, t)
         Just t'    -> do θ' <- unifyMany θ [t] [t']
                          return (θ', apply θ' t)

checkApp f to g es
  = snd <$> checkApp' f to g es


-- | Helper for checking binary (numeric) operations

checkOp f e1 o e2 
  = liftM2 (checkOpTy f e o) (checkExpr f e1) (checkExpr f e2)
    where e = EBin e1 o e2

checkOpTy f _ _ FInt FInt          
  = return FInt

checkOpTy f e _ t@(FObj l) t'@(FObj l')
  | l == l'
  = checkNumeric l >> return t

checkOpTy f e _ t t'
  = throwError $ errOp e t t'

checkNumeric f l 
  = do t <- checkSym f l
       unless (t == FNum) (throwError $ errNonNumeric t l)
       return ()

-------------------------------------------------------------------------
-- | Checking Predicates ------------------------------------------------
-------------------------------------------------------------------------

checkPred                  :: Env -> Pred -> CheckM () 

checkPred f PTrue          = return ()
checkPred f PFalse         = return ()
checkPred f (PBexp e)      = checkPredBExp f e 
checkPred f (PNot p)       = checkPred f p
checkPred f (PImp p p')    = mapM_ (checkPred f) [p, p'] 
checkPred f (PIff p p')    = mapM_ (checkPred f) [p, p']
checkPred f (PAnd ps)      = mapM_ (checkPred f) ps
checkPred f (POr ps)       = mapM_ (checkPred f) ps
checkPred f (PAtom r e e') = checkRel f r e e'
checkPred f p              = throwError $ errUnexpectedPred p

checkPredBExp f e          = do t <- checkExpr f e
                                unless (t == fProp) (throwError $ errBExp e t)
                                return ()
  

-- | Checking Relations

checkRel f Eq (EVar x) (EApp g es) = checkRelEqVar f x g es
checkRel f Eq (EApp g es) (EVar x) = checkRelEqVar f x g es
checkRel f r  e1 e2                = do t1 <- checkExpr f e1
                                        t2 <- checkExpr f e2
                                        checkRelTy (PAtom r e1 e2) r t1 t2

checkRelTy _ _ FInt (FObj l)       = checkNumeric l
checkRelTy _ _ (FObj l) FInt       = checkNumeric l
checkRelTy e Eq t1 t2              = unless (t1 == t2 && t1 /= fProp) (throwError $ errRel e t1 t2)
checkRelTy e Ne t1 t2              = unless (t1 == t2 && t1 /= fProp) (throwError $ errRel e t1 t2)
checkRelTy _ _  t1 t2              = unless (t1 == t2)                (throwError $ errRel e t1 t2)


-- | Special case for polymorphic singleton variable equality e.g. (x = Set_emp) 

checkRelEqVar f x g es             = do tx <- checkSym f x
                                        _  <- checkApp f (Just tx) g es
                                        return ()




-------------------------------------------------------------------------
-- | Error messages -----------------------------------------------------
-------------------------------------------------------------------------

errOp e t t' 
  | t == t'          = printf "Operands have non-numeric types %s in %s"  
                         (showFix t) (showFix e)
  | otherwise        = printf "Operands have different types %s and %s in %s" 
                         (showFix t) (showFix t') (showFix e)

errArgArity g its es = printf "Measure %s expects %d args but gets %d in %s" 
                         (showFix g) (length its) (length es) (showFix (EApp g es))

errIte e1 e2 t1 t2   = printf "Mismatched branches in Ite: then %s : %s, else %s : %s" 
                         (showFix e1) (showFix t1) (showFix e2) (showFix t2) 

errCast e t' t       = printf "Cannot cast %s of sort %s to incompatible sort %t" 
                         (showFix e) (showFix t') (showFix t)

errUnbound x         = printf "Unbound Symbol %s" (showFix x)

errNonFunction t     = printf "Sort %s is not a function" (showFix t)

errNonNumeric _ l    = printf "FObj sort %s is not numeric" (showFix l)

errUnexpectedPred p  = printf "Sort Checking: Unexpected Predicate %s" (showFix p)

-------------------------------------------------------------------------
-- | Utilities for working with sorts -----------------------------------
-------------------------------------------------------------------------

-- | Unification of Sorts

unify   = unifyMany (Th M.empty)

unifyMany 0 ts ts' 
  | length ts == length ts'        = foldM (uncurry . unify1) θ $ zip ts ts'
  | otherwise                      = throwError $ errUnifyMany ts ts'

unify1 _ FNum _                    = Nothing
unify1 θ (FVar i) t                = unifyVar θ i t
unify1 θ t (FVar i)                = unifyVar θ i t
unify1 θ (FApp c ts) (FApp c' ts')  
  | c == c'                        = unifyMany θ ts ts' 
unify1 θ t1 t2  
  | t1 == t2                       = return θ
  | otherwise                      = throwError $ errUnify t1 t2

unifyVar θ i t 
  = case lookupVar i Θ of
      Just t' -> if t == t' then Just θ else Nothing 
      Nothing -> Just $ updateVar i t Θ

-- | Sort Substitutions
newtype TVSubst      = Th (M.HashMap Int Sort) 

-- | API for manipulating substitutions
lookupVar i (Th m)   = M.lookup i m
updateVar i t (Th m) = Th (M.insert i t m)

-------------------------------------------------------------------------
-- | Applying a Type Substitution ---------------------------------------
-------------------------------------------------------------------------

apply θ = error "TODO"

sortMap f (FFunc n ts) = FFunc n (sortMap f <$> ts)
sortMap f (FApp  c ts) = FApp  c (sortMap f <$> ts)
sortMap f t            = f t

------------------------------------------------------------------------
-- | Deconstruct a function-sort ---------------------------------------
------------------------------------------------------------------------

sortFunction (FFunc n ts') = return (n, ts, t) 
  where 
    ts                     = take numArgs ts'
    t                      = last ts'
    numArgs                = length ts' - 1

sortFunction t             = throwError $ errNonFunction t 




-- let uf_arity f uf =  
--   match sortcheck_sym f uf with None -> None | Some t -> 
--     match Sort.func_of_t t with None -> None | Some (i,_,_) -> 
--       Some i
--  
-- (* API *)
-- let sortcheck_app f t uf es = 
--   match uf_arity f uf, sortcheck_app_sub f t uf es with 
--     | (Some n , Some (s, t)) -> 
--         if Sort.check_arity n s then Some (s, t) else
--            assertf "Ast.sortcheck_app: type args not fully instantiated %s" 
--              (expr_to_string (eApp (uf, es)))
--     | _ -> None

-- TODO: forall, but this will make sure we DONT use it. Ha!
--
-- | Forall (qs,p) ->
-- (* let f' = fun x -> try List.assoc x qs with _ -> f x in *)
-- let f' = fun x -> match Misc.list_assoc_maybe x qs with None -> f x | y -> y
-- in sortcheck_pred f' p
-- | _ -> failwith "Unexpected: sortcheck_pred"

