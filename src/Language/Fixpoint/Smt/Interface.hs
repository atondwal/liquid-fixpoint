{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE LambdaCase                #-}

-- | This module contains an SMTLIB2 interface for
--   1. checking the validity, and,
--   2. computing satisfying assignments
--   for formulas.
--   By implementing a binary interface over the SMTLIB2 format defined at
--   http://www.smt-lib.org/
--   http://www.grammatech.com/resource/smt/SMTLIBTutorial.pdf

module Language.Fixpoint.Smt.Interface (

    -- * Commands
      Command  (..)

    -- * Responses
    , Response (..)

    -- * Typeclass for SMTLIB2 conversion
    , SMTLIB2 (..)

    -- * Creating and killing SMTLIB2 Process
    , Context (..)
    , makeContext
    , makeContextNoLog
    , cleanupContext

    -- * Execute Queries
    , command
    , smtWrite

    -- * Query API
    , smtDecl
    , smtAssert
    , smtCheckUnsat
    , smtBracket
    , smtDistinct
    , smtDoInterpolate
    , smtInterpolate

    -- * Theory Symbols
    -- , theorySymbols
      -- smt_set_funs

    ) where

import           Language.Fixpoint.Config (SMTSolver (..))
import           Language.Fixpoint.Errors
import           Language.Fixpoint.Files
import           Language.Fixpoint.Types
import           Language.Fixpoint.Smt.Types
import           Language.Fixpoint.Smt.Theories (preamble)
import           Language.Fixpoint.Smt.Serialize()



import           Control.Applicative      ((*>), (<$>), (<*), (<|>))
import           Control.Monad
import           Control.Arrow
import           Data.Char
import qualified Data.List                as L
import           Data.Monoid
import           Data.Maybe
import qualified Data.Text                as T
import           Data.Text.Format
import qualified Data.Text.IO             as TIO
import qualified Data.Text.Lazy           as LT
import qualified Data.Text.Lazy.IO        as LTIO
import qualified Data.HashMap.Strict      as M
import           System.Directory
import           System.Exit              hiding (die)
import           System.FilePath
import           System.IO                (IOMode (..), hClose, hFlush, openFile)
import           System.Process
import qualified Data.Attoparsec.Text     as A

{- Usage:
runFile f
  = readFile f >>= runString

runString str
  = runCommands $ rr str

runCommands cmds
  = do me   <- makeContext Z3
       mapM_ (T.putStrLn . smt2) cmds
       zs   <- mapM (command me) cmds
       return zs
-}

--------------------------------------------------------------------------
-- | SMT IO --------------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
command              :: Context -> Command -> IO Response
--------------------------------------------------------------------------
command me !cmd      = {-# SCC "command" #-} say me cmd >> hear me cmd
  where
    say me               = smtWrite me . smt2
    hear me CheckSat     = smtRead me
    hear me (GetValue _) = smtRead me
    hear me (Interpolate fi p q) = smtRead me >>= \case
      Unsat -> smtPred fi me
      Sat -> error "Not UNSAT. No interpolation needed. Why did you call upon me?"
      e -> error $ show e
    hear me _            = return Ok



smtWrite :: Context -> LT.Text -> IO ()
smtWrite me !s = smtWriteRaw me s

smtRes :: Context -> A.IResult T.Text Response -> IO Response
smtRes me res = case A.eitherResult res of
  Left e  -> error e
  Right r -> do
    maybe (return ()) (\h -> hPutStrLnNow h $ format "; SMT Says: {}" (Only $ show r)) (cLog me)
    when (verbose me) $
      LTIO.putStrLn $ format "SMT Says: {}" (Only $ show r)
    return r

smtParse me parserP = smtReadRaw me >>= A.parseWith (smtReadRaw me) parserP >>= smtRes me

smtRead :: Context -> IO Response
smtRead me = {-# SCC "smtRead" #-} smtParse me responseP

smtPred :: FInfo a -> Context -> IO Response
smtPred fi me = {-# SCC "smtPred" #-} smtParse me (Interpolant <$> parseLisp' fi <$> predP)

predP = {-# SCC "predP" #-} (Lisp <$> (A.char '(' *> listP <* A.char ')')) <|> (Sym . symbol<$> (A.string "true" <|> A.string "false"))
listP = A.many' $ (Sym <$> symbolP) <|> predP

data Lisp = Sym Symbol | Lisp [Lisp] deriving (Eq,Show)
type PorE = Either Pred Expr

binOpStrings :: [T.Text]
binOpStrings = [ "+", "-", "*", "/", "mod"]

strToOp :: T.Text -> Bop
strToOp "+" = Plus
strToOp "-" = Minus
strToOp "*" = Times
strToOp "/" = Div
strToOp "mod" = Mod

binRelStrings :: [T.Text]
binRelStrings = [ ">", "<", "<=", ">="]

strToRel :: T.Text -> Brel
strToRel ">" = Gt
strToRel ">=" = Ge
strToRel "<" = Lt
strToRel "<=" = Le
-- Do I need Ne Une Ueq?

parseLisp' :: FInfo a -> Lisp -> Pred
parseLisp' fi = toPred
  where toPred :: Lisp -> Pred
        toPred x = case parseLisp x of
                     Left p -> p
                     Right e -> error $ "expected Pred, got Expr: " ++ show e
        toExpr :: Lisp -> Expr
        toExpr x = case parseLisp x of
                     Left p -> error $ "expected Expr, got Pred: " ++ show p
                     Right e -> e
        parseLisp :: Lisp -> PorE
        parseLisp (Sym s)
          | symbolText s == "true" = Left PTrue
          | symbolText s == "false" = Left PFalse
          | otherwise = Right $ EVar s
        parseLisp (Lisp (Sym s:xs))
          | symbolText s == "and" = Left $ PAnd $ L.map toPred xs
          | symbolText s == "or" = Left $ POr $ L.map toPred xs
        parseLisp (Lisp [Sym s,x])
          | symbolText s == "not" = Left $ PNot $ toPred x
          | symbolText s == "-" = Right $ ENeg $ toExpr x
          | otherwise           = Right $ ELit (dummyLoc s) $ fromJust $ lookup s (lits fi)
        parseLisp (Lisp [Sym s,x,y])
          | symbolText s == "=>" = Left $ PImp (toPred x) (toPred y)
          | symbolText s `elem` binOpStrings = Right $ EBin (strToOp $ symbolText s) (toExpr x) (toExpr y)
          | symbolText s `elem` binRelStrings = Left $ PAtom (strToRel $ symbolText s) (toExpr x) (toExpr y)
          | symbolText s == "=" = Left $ case (parseLisp x, parseLisp y) of
                                    (Left p, Left q) -> PIff p q
                                    (Right p, Right q) -> PAtom Eq p q
                                    _ -> error $ "Can't compare `" ++ show x ++ "` with`" ++ show y ++ "`. Kind Error."
        parseLisp (Lisp [Sym s, x, y, z])
          | symbolText s == "ite" = Right $ EIte (toPred x) (toExpr y) (toExpr z)
        parseLisp (Lisp (Sym s:xs)) = Right $ EApp (dummyLoc s) $ L.map toExpr xs
        parseLisp x = error $ show x ++ "is Nonsense Lisp!"
        -- PBexp? When do I know to read one of these in?

responseP = {-# SCC "responseP" #-} A.char '(' *> sexpP
         <|> A.string "sat"     *> return Sat
         <|> A.string "unsat"   *> return Unsat
         <|> A.string "unknown" *> return Unknown

sexpP = {-# SCC "sexpP" #-} A.string "error" *> (Error <$> errorP)
     <|> Values <$> valuesP

errorP = A.skipSpace *> A.char '"' *> A.takeWhile1 (/='"') <* A.string "\")"

valuesP = A.many1' pairP <* A.char ')'

pairP = {-# SCC "pairP" #-}
  do A.skipSpace
     A.char '('
     !x <- symbolP
     A.skipSpace
     !v <- valueP
     A.char ')'
     return (x,v)

symbolP = {-# SCC "symbolP" #-} symbol <$> A.takeWhile1 (not . isSpace)

valueP = {-# SCC "valueP" #-} negativeP
      <|> A.takeWhile1 (\c -> not (c == ')' || isSpace c))

negativeP
  = do v <- A.char '(' *> A.takeWhile1 (/=')') <* A.char ')'
       return $ "(" <> v <> ")"

{-@ pairs :: {v:[a] | (len v) mod 2 = 0} -> [(a,a)] @-}
pairs :: [a] -> [(a,a)]
pairs !xs = case L.splitAt 2 xs of
              ([],b)      -> []
              ([x,y], zs) -> (x,y) : pairs zs

smtWriteRaw      :: Context -> LT.Text -> IO ()
smtWriteRaw me !s = {-# SCC "smtWriteRaw" #-} do
  hPutStrLnNow (cOut me) s
  maybe (return ()) (`hPutStrLnNow` s) (cLog me)

smtReadRaw       :: Context -> IO Raw
smtReadRaw me    = {-# SCC "smtReadRaw" #-} TIO.hGetLine (cIn me)

hPutStrLnNow h !s   = LTIO.hPutStrLn h s >> hFlush h

--------------------------------------------------------------------------
-- | SMT Context ---------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
makeContext   :: SMTSolver -> FilePath -> IO Context
--------------------------------------------------------------------------
makeContext s f
  = do me  <- makeProcess s
       pre <- smtPreamble s me
       createDirectoryIfMissing True $ takeDirectory smtFile
       hLog               <- openFile smtFile WriteMode
       let me' = me { cLog = Just hLog }
       mapM_ (smtWrite me') pre
       return me'
    where
       smtFile = extFileName Smt2 f


makeContextNoLog s
  = do me  <- makeProcess s
       pre <- smtPreamble s me
       mapM_ (smtWrite me) pre
       return me

makeProcess s
  = do (hOut, hIn, _ ,pid) <- runInteractiveCommand $ smtCmd s
       return $ Ctx pid hIn hOut Nothing False

--------------------------------------------------------------------------
cleanupContext :: Context -> IO ExitCode
--------------------------------------------------------------------------
cleanupContext me@(Ctx {..})
  = do smtWrite me "(exit)"
       code <- waitForProcess pId
       hClose cIn
       hClose cOut
       maybe (return ()) hClose cLog
       return code

{- "z3 -smt2 -in"                   -}
{- "z3 -smtc SOFT_TIMEOUT=1000 -in" -}
{- "z3 -smtc -in MBQI=false"        -}

smtCmd Z3      = "z3 -smt2 -in"
smtCmd Mathsat = "mathsat -input=smt2"
smtCmd Cvc4    = "cvc4 --incremental -L smtlib2"

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
smtPreamble Z3 me
  = do smtWrite me "(get-info :version)"
       v:_ <- T.words . (!!1) . T.splitOn "\"" <$> smtReadRaw me
       if T.splitOn "." v `versionGreater` ["4", "3", "2"]
         then return $ z3_432_options ++ preamble Z3
         else return $ z3_options     ++ preamble Z3
smtPreamble s  _
  = return $ preamble s

versionGreater (x:xs) (y:ys)
  | x >  y = True
  | x == y = versionGreater xs ys
  | x <  y = False
versionGreater xs [] = True
versionGreater [] ys = False

-----------------------------------------------------------------------------
-- | SMT Commands -----------------------------------------------------------
-----------------------------------------------------------------------------

smtPush, smtPop   :: Context -> IO ()
smtPush me        = interact' me Push
smtPop me         = interact' me Pop


smtDecl :: Context -> Symbol -> Sort -> IO ()
smtDecl me x t = interact' me (Declare x ins out)
  where
    (ins, out) = deconSort t

deconSort :: Sort -> ([Sort], Sort)
deconSort t = case functionSort t of
                Just (_, ins, out) -> (ins, out)
                Nothing            -> ([] , t  )

smtAssert :: Context -> Pred -> IO ()
smtAssert me p    = interact' me (Assert Nothing p)

smtDistinct :: Context -> [Expr] -> IO ()
smtDistinct me az = interact' me (Distinct az)

smtCheckUnsat :: Context -> IO Bool
smtCheckUnsat me  = respSat <$> command me CheckSat

smtBracket :: Context -> IO a -> IO a
smtBracket me a   = do smtPush me
                       r <- a
                       smtPop me
                       return r

smtDoInterpolate :: Context -> FInfo a -> Pred -> Pred -> IO Pred
smtDoInterpolate me fi p q = --smtLoadEnv me env >>
                                  respInterp <$> command me (Interpolate fi p q)
  where env = M.elems $ beBinds $ bs fi

smtLoadEnv :: Context -> [(Symbol, SortedReft)] -> IO ()
smtLoadEnv me env = mapM_ smtDecl' $ L.map (second sr_sort) env
  where smtDecl' = uncurry $ smtDecl me

smtInterpolate :: Context -> FInfo () -> Pred -> Pred -> IO Pred
smtInterpolate me fi p q = respInterp <$> command me (Interpolate fi p q)

respInterp (Interpolant p') = p'
respInterp r = die $ err dummySpan $ "crash: SMTLIB2 respInterp = " ++ show r

respSat Unsat   = True
respSat Sat     = False
respSat Unknown = False
respSat r       = die $ err dummySpan $ "crash: SMTLIB2 respSat = " ++ show r

interact' me cmd  = void $ command me cmd

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
z3_432_options
  = [ "(set-option :auto-config false)"
    , "(set-option :model true)"
    , "(set-option :model.partial false)"
    , "(set-option :smt.mbqi false)" ]

z3_options
  = [ "(set-option :auto-config false)"
    , "(set-option :model true)"
    , "(set-option :model-partial false)"
    , "(set-option :mbqi false)" ]
