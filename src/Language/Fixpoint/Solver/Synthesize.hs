module Language.Fixpoint.Solver.Synthesize (
    synthesize
) where

import           Language.Fixpoint.Types

synthesize :: SInfo a -> SInfo a
synthesize a = a