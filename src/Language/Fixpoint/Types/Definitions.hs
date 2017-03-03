{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE PatternGuards              #-}

module Language.Fixpoint.Types.Definitions (
  Definition (..)
) where

import Language.Fixpoint.Types.Names
import Language.Fixpoint.Types.Refinements

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
