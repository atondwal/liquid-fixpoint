{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards     #-}

module Language.Fixpoint.Solver.Synthesize where

import           Language.Fixpoint.Types
-- GROSS!!! unfuck later, if I feel like it
import qualified Data.Text                as T
import qualified Data.List                       as L
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Types.Visitor as Vis
import           Language.Fixpoint.Types.Config  as FC
import           Language.Fixpoint.Defunctionalize
import           Language.Fixpoint.SortCheck
import qualified Language.Fixpoint.Types           as F
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Graph.Types


import Control.Monad.State.Strict
import Control.Applicative ((<|>))
import Data.Char
import Data.Attoparsec.Internal.Types (Parser)
import Data.Monoid
import qualified Data.Attoparsec.Text as A
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S
import           Data.Text.Read (decimal)
import           Data.Foldable
import           Data.Maybe


opDenote Plus  = (+)
opDenote Minus = (-)
opDenote Times = (*)
opDenote Div   = (/)
opDenote r     = error $ "くそ Op: " ++ show r

relDenote Gt = (>)
relDenote Ge = (>=)
relDenote Lt = (<)
relDenote Le = (<=)
relDenote r  = error $ "くそ Rel: " ++ show r

boolDenote PTrue  = True
boolDenote PFalse = False
boolDenote e      = error $ "くそ Bool: " ++ show e

fromLeft (Left a) = a
fromLeft (Right a) = error $ show a

eval :: Expr -> Either Bool Double
eval (EIte b e1 e2)
  = if b' then eval e1 else eval e2
  where Left b' = eval b
eval (PAtom r e1 e2)
  = Left $ relDenote r a b
  where Left a = eval e1
        Left b = eval e2
eval (EBin o e1 e2)
  | (Right a) <- eval e1
  , (Right b) <- eval e2
  = Right $ opDenote o a b
eval (ENeg e)
  | (Right a) <- eval e
  = Right $ negate a
eval (PNot e)
  = Left $ not b
  where Left b = eval e
eval (PImp e1 e2)
  = Left $ b <= a
  where Left a = eval e1
        Left b = eval e2
eval (PIff e1 e2)
  = Left $ b == a
  where Left a = eval e1
        Left b = eval e2
eval (PAnd es)
  = Left $ and es'
  where es' = fromLeft . eval <$> es
eval (POr es)
  = Left $ or es'
  where es' = fromLeft . eval <$> es
eval e = error $ "くそ " ++ show e


synthesisProject cfg fi cD res rondonSol (pts,init) = do
  lift $ print cons
  lift $ print kprevs
  lift $ print failingKVars
  foldrM (synthKVar cfg fi cD rondonSol) (pts,init) failingKVars
  where cons = case F.resStatus res of
          F.Crash{} -> error "CRASH BEFORE SYNTH!!"
          F.Safe -> error "LOL WHY SO SYNTH? ALRDY SAFE!!!"
          F.Unsafe xs -> fst <$> xs
        kprevs = cPrev cD
        -- we should remove kvars that are redundant or nonkut
        failingKVars = join $ catMaybes $ flip M.lookup kprevs <$> cons

synthKVar cfg fi cD rS k0 = synthKVar' cfg fi cD rS (S.singleton k0) k0

synthKVar' cfg fi cD rS ks k0 (pts,sol) = do
  lift $ putStrLn $ "\x1b[32m" ++ "SYNTH BABY SYNTH " ++ show k0 ++ "\x1b[0m"
  lift $ print prevs
  lift $ print kprevs
  lift $ print prevkvars
  lift $ print reck
  -- lift $ print $ apply sol k0
  (pts',sol') <- foldrM (synthKVar' cfg fi cD rS ks') (pts,sol) reck
  return (pts',sol')
  where prevkvars = join $ catMaybes $ flip M.lookup kprevs <$> prevs
        ks' = S.insert k0 ks
        reck = S.difference (S.fromList prevkvars) ks'

        kprevs = cPrev cD
        prevs = mfromJust (error "NO CONSID") <$>
           (map (F.sid . snd) . M.toList .
           flip M.filter (F.cm fi) $ -- Should probably cache this
           writes k0)
        writes x c = x `elem` Vis.kvars (F.crhs c)

synthesize :: Config -> SInfo a -> IO (SInfo a)
synthesize cfg fi = do
      qs <- qualForK
      return fi { quals = qs }
  where (KS kvars) = kuts fi
        cons k = M.filter (hasKvar k) (cm fi)
        qualForK :: IO [Qualifier]
        qualForK = concat <$>
           sequence ((\k -> synthesizeKvar cfg k (cons k))
                     <$> S.toList kvars)

-- Yeah, these qualifiers should acutally be known types wrapped inside a
-- solverInfo, but I really don't understand that solverInfo/Eliminate codebase
-- that well... maybe then
synthesizeKvar :: Config -> KVar -> M.HashMap SubcId (SimpC a) -> IO [Qualifier]
synthesizeKvar cfg k0 cs = sequence
    $ (\_c -> let _γ = makeCtx cfg undefined in undefined)
    . snd
    <$> M.toList cs
  where _clear :: Vis.Visitable a => a -> a
        _clear = Vis.mapKVars (\k -> if k == k0 then Nothing else Just PTrue)
hasKvar k a = elem k (Vis.kvars a)

-- The thing to do is to find all the kut KVars and then

-- This context needs to be spun up for every actual context Γ.
-- In practice this means that we need one for each constraint
-- that uses a kut Kvar
data SynthesisConext
  = SC { scContext :: IO SMT.Context
       , scPreds   :: !([(Symbol, Sort)] -> Expr -> SMT.Context -> IO [(Symbol, Expr)])
       , scLams    :: [(Symbol, Sort)]
       }

dumbContext :: IO SMT.Context -> SynthesisConext
dumbContext ctx = SC ctx (\_ _ _ -> error "HAHA") []

isValid :: SynthesisConext -> Expr -> IO [(Symbol, Expr)]
isValid γ b = scPreds γ (scLams γ) b =<< scContext γ

makeCtx :: Config -> SMT.Context -> [(Symbol, SortedReft)] -> SynthesisConext
makeCtx cfg ctx es = (dumbContext context) { scPreds  = \bs e c -> askSMT c bs e }
  where
    context :: IO SMT.Context
    context = do
      SMT.smtPop ctx
      SMT.smtPush ctx
      SMT.smtAssert ctx $
        pAnd $ filter (null . Vis.kvars) ((toSMT [] . expr . snd) <$> es)
      return ctx

    toSMT bs = defuncAny cfg (SMT.ctxSymEnv ctx) . elaborate "makeSynCtx" (elabEnv bs)
    elabEnv  = L.foldl' (\env (x, s) -> insertSymEnv x s env) (SMT.ctxSymEnv ctx)

    askSMT :: SMT.Context -> [(Symbol, Sort)] -> Expr -> IO [(Symbol, Expr)]
    askSMT ctx bs e
      -- Fix this to work nicely with Eliminate?
      | null (Vis.kvars e) = do
          SMT.smtPush ctx
          b <- SMT.getValues ctx [] (toSMT bs e) (fst <$> bs)
          SMT.smtPop ctx
          return b
      | otherwise      = error "Synthesis tried to write a KVar to SMT"
 

type SmtParser a = Parser T.Text a

decode :: T.Text -> T.Text
decode s = T.concat $ zipWith ($) (cycle [id, T.singleton . chr . fromRight . decimal]) (T.split (=='$') s)

fromRight (Right (x,_)) = x
fromRight (Left _) = error "Invalid hashcons format"

valueP :: SmtParser T.Text
valueP = {-# SCC "valueP" #-} negativeP
      <|> A.takeWhile1 (\c -> not (c == ')' || isSpace c))

negativeP :: SmtParser T.Text
negativeP
  = do
      v <- A.char '(' *> A.takeWhile1 (/=')') <* A.char ')'
      return $ "(" <> v <> ")"
