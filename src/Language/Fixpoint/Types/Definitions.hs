{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE PatternGuards              #-}

module Language.Fixpoint.Types.Definitions (
  Definition (..),
  subExprs
) where

import Language.Fixpoint.Types.Names
import Language.Fixpoint.Types.Refinements

import qualified Data.HashMap.Strict       as M
import           Data.Monoid

import           GHC.Generics              (Generic)
import qualified Data.Binary as B
import           Control.DeepSeq

data Definition = Dfn
  { dName :: Symbol
  , dArgs :: [Symbol]
  , dDefs :: [(Pred, Expr)]
  } deriving (Eq, Show, Generic)

instance B.Binary Definition
instance NFData   Definition

{-@ Lazy subExprs @-}
subExprs :: M.HashMap Symbol Definition -> Expr -> [(Symbol,[Expr])]
subExprs m e@(EApp _ _)
  | (EVar f, es) <- splitEApp e
  , Just _ <- M.lookup f m
  = (f,es):(subExprs m =<< es)
subExprs m (ELam _ e)      = subExprs m e
subExprs m (ECst e _)      = subExprs m e
subExprs m (EApp e1 e2)    = subExprs m e1 <> subExprs m e2
subExprs _ (ESym _)        = mempty
subExprs _ (ECon _)        = mempty
subExprs _ (EVar _)        = mempty
subExprs m (ENeg e)        = subExprs m e
subExprs m (EBin _ e1 e2)  = subExprs m e1 <> subExprs m e2
subExprs m (EIte e e1 e2)  = subExprs m e <> subExprs m e1 <> subExprs m e2
subExprs m (ETAbs e _)     = subExprs m e
subExprs m (ETApp e _)     = subExprs m e
subExprs m (PAnd es)       = subExprs m =<< es
subExprs m (POr es)        = subExprs m =<< es
subExprs m (PNot e)        = subExprs m e
subExprs m (PImp e1 e2)    = subExprs m e1 <> subExprs m e2
subExprs m (PIff e1 e2)    = subExprs m e1 <> subExprs m e2
subExprs m (PAtom _ e1 e2) = subExprs m e1 <> subExprs m e2
subExprs m (PAll _ e)      = subExprs m e
subExprs m (PExist _ e)    = subExprs m e
subExprs _ (PKVar _ _)     = mempty
subExprs _ PGrad           = mempty
