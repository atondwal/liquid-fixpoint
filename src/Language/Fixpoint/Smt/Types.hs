{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains the types defining an SMTLIB2 interface.

module Language.Fixpoint.Smt.Types (

    -- * Serialized Representation
      Raw

    -- * Commands
    , Command  (..)

    -- * Responses
    , Response (..)

    -- * Typeclass for SMTLIB2 conversion
    , SMTLIB2 (..)
    , runSmt2

    -- * SMTLIB2 Process Context
    , Context (..)

    -- * Theory Symbol
    , TheorySymbol (..)
    , SMTEnv
    ) where

import           Language.Fixpoint.Types
-- import           Language.Fixpoint.Misc   (traceShow)
import qualified Data.Text                as T
import qualified Data.Text.Lazy           as LT
import qualified Data.Text.Lazy.Builder   as LT
import           System.IO                (Handle)
import           System.Process

--------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------
--------------------------------------------------------------------------

type Raw          = LT.Text

-- | Commands issued to SMT engine

data Command      = Push
                  | Pop
                  | CheckSat
                  | Declare   !Symbol [Sort] !Sort
                  | Define    !Sort
                  | Assert    !(Maybe Int) !Expr
                  | Interpolate Int Expr
                  | Distinct  [Expr] -- {v:[Expr] | 2 <= len v}
                  | GetValue  [Symbol]
                  | CMany [Command]
                  deriving (Eq, Show)

-- | Responses received from SMT engine
data Response     = Ok
                  | Sat
                  | Unsat
                  | Unknown
                  | Values [(Symbol, T.Text)]
                  | Error !T.Text
                  | Interpolant [Expr]
                  deriving (Eq, Show)

-- | Information about the external SMT process
data Context = Ctx
  { ctxPid     :: !ProcessHandle
  , ctxCin     :: !Handle
  , ctxCout    :: !Handle
  , ctxLog     :: !(Maybe Handle)
  , ctxVerbose :: !Bool
  , ctxExt     :: !Bool              -- ^ flag to enable function extentionality axioms
  , ctxAeq     :: !Bool              -- ^ flag to enable lambda a-equivalence axioms
  , ctxBeq     :: !Bool              -- ^ flag to enable lambda b-equivalence axioms
  , ctxNorm    :: !Bool              -- ^ flag to enable lambda normal form equivalence axioms
  , ctxSmtEnv  :: !SMTEnv
  }

type SMTEnv = SEnv Sort

-- | Theory Symbol
data TheorySymbol  = Thy { tsSym  :: !Symbol
                         , tsRaw  :: !Raw
                         , tsSort :: !Sort
                         }
                     deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- | AST Conversion: Types that can be serialized ------------------------------
--------------------------------------------------------------------------------

class SMTLIB2 a where
  smt2 :: a -> LT.Builder

runSmt2 :: (SMTLIB2 a) => a -> LT.Builder
runSmt2 = smt2
