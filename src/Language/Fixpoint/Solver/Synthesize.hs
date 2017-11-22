{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Fixpoint.Solver.Synthesize (
    synthesize
) where

import           Language.Fixpoint.Types
-- GROSS!!! unfuck later, if I feel like it
import qualified Data.Text                as T
import qualified Data.List                       as L
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Types.Visitor as Vis
import           Language.Fixpoint.Types.Config  as FC
import           Language.Fixpoint.Defunctionalize
import           Language.Fixpoint.SortCheck
import Control.Applicative ((<|>))
import Data.Char
import Data.Attoparsec.Internal.Types (Parser)
import Data.Monoid
import qualified Data.Attoparsec.Text as A
import qualified Data.HashMap.Strict       as M
import qualified Data.HashSet              as S
import           Text.PrettyPrint.HughesPJ (text)
import           Text.Read (readMaybe)
import Data.Text.Read (decimal)

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
    $ (\c -> let γ = makeCtx cfg undefined in undefined)
    . snd
    <$> M.toList cs
  where clear :: Vis.Visitable a => a -> a
        clear = Vis.mapKVars (\k -> if k == k0 then Nothing else Just PTrue)

hasKvar k a = elem k (Vis.kvars a)

-- The thing to do is to find all the kut KVars and then

-- This context needs to be spun up for every actual context Γ.
-- In practice this means that we need one for each constraint
-- that uses a kut Kvar
data SynthesisConext
  = SC { scContext :: IO SMT.Context
       , scPreds   :: !([(Symbol, Sort)] -> Expr -> SMT.Context -> IO [(Symbol, T.Text)])
       , scLams    :: [(Symbol, Sort)]
       }

dumbContext :: IO SMT.Context -> SynthesisConext
dumbContext ctx = SC ctx (\_ _ _ -> error "HAHA") []

isValid :: SynthesisConext -> Expr -> IO [(Symbol, T.Text)]
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

    askSMT :: SMT.Context -> [(Symbol, Sort)] -> Expr -> IO [(Symbol, T.Text)]
    askSMT ctx bs e
      -- Fix this to work nicely with Eliminate?
      | null (Vis.kvars e) = do
          SMT.smtPush ctx
          b <- SMT.getValues ctx [] (toSMT bs e) (fst <$> bs)
          SMT.smtPop ctx
          return b
      | otherwise      = error "Synthesis tried to write a KVar to SMT"


space2 c = isSpace c && not (A.isEndOfLine c)

predP = {-# SCC "predP" #-}
        (Lisp <$> (A.char '(' *> A.sepBy' predP (A.skipWhile space2) <* A.char ')'))
    <|> (Sym <$> symbolP)

data Lisp = Sym Symbol | Lisp [Lisp] deriving (Eq,Show)

binOpStrings :: [T.Text]
binOpStrings = [ "+", "-", "*", "/", "mod"]

strToOp :: T.Text -> Bop
strToOp "+" = Plus
strToOp "-" = Minus
strToOp "*" = Times
strToOp "/" = Div
strToOp "mod" = Mod
strToOp _ = error "Op not found"

binRelStrings :: [T.Text]
binRelStrings = [ ">", "<", "<=", ">="]

strToRel :: T.Text -> Brel
strToRel ">" = Gt
strToRel ">=" = Ge
strToRel "<" = Lt
strToRel "<=" = Le
-- Do I need Ne Une Ueq?
strToRel _ = error "Rel not found"

parseLisp :: Lisp -> Expr
parseLisp (Sym s)
  | symbolText s == "true"  = PTrue
  | symbolText s == "false" = PFalse
  | Just n <- readMaybe (symbolString s) :: Maybe Integer = (ECon (I n))
  | Just n <- readMaybe (symbolString s) :: Maybe Double  = (ECon (R n))
  | otherwise               = EVar s
parseLisp l@(Lisp xs)
  | [Sym s, x] <- xs, symbolText s == "not"     =
    PNot (parseLisp x)
  | [Sym s, x] <- xs, symbolText s == "-"       =
    ENeg (parseLisp x)
  | [Sym s, x, y] <- xs, symbolText s == "=>"   =
    PImp (parseLisp x) (parseLisp y)
  | [Sym s, x, y] <- xs, symbolText s == "="    =
    PAtom Eq (parseLisp x) (parseLisp y)
  | [Sym s, x, y] <- xs, symbolText s `elem` binOpStrings  =
    EBin (strToOp $ symbolText s) (parseLisp x) (parseLisp y)
  | [Sym s, x, y] <- xs, symbolText s `elem` binRelStrings =
    PAtom (strToRel $ symbolText s) (parseLisp x) (parseLisp y)
  | [Sym s,x,y,z] <- xs, symbolText s == "ite"  =
    EIte (parseLisp x) (parseLisp y) (parseLisp z)
  | (Sym s:xs) <- xs, symbolText s == "and"     =
    PAnd $ L.map parseLisp xs
  | (Sym s:xs) <- xs, symbolText s == "or"      =
    POr $ L.map parseLisp xs
  | otherwise                                   =
    lispToFunc l
  where lispToFunc (Lisp xs) = foldr1 EApp $ map parseLisp xs
        -- this should not be called
        lispToFunc (Sym s)   = EVar s

type SmtParser a = Parser T.Text a

responseP :: SmtParser SMT.Response
responseP = {-# SCC "responseP" #-} A.char '(' *> sexpP
          <|> A.string "sat"     *> return SMT.Sat
          <|> A.string "unsat"   *> return SMT.Unsat
          <|> A.string "unknown" *> return SMT.Unknown

sexpP :: SmtParser SMT.Response
sexpP = {-# SCC "sexpP" #-} A.string "error" *> (SMT.Error <$> errorP)
      <|> SMT.Values <$> valuesP

errorP :: SmtParser T.Text
errorP = A.skipSpace *> A.char '"' *> A.takeWhile1 (/='"') <* A.string "\")"

valuesP :: SmtParser [(Symbol, T.Text)]
valuesP = A.many1' pairP <* A.char ')'

pairP :: SmtParser (Symbol, T.Text)
pairP = {-# SCC "pairP" #-}
  do
      A.skipSpace
      A.char '('
      !x <- symbolP
      A.skipSpace
      !v <- valueP
      A.char ')'
      return (x,v)

symbolP :: SmtParser Symbol
symbolP = {-# SCC "symbolP" #-} symbol . decode <$> A.takeWhile1 (\x -> x /= ')' && not (isSpace x) && not (A.isEndOfLine x))

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