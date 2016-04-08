{-# LANGUAGE PatternGuards             #-}
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
    , makeContextWithSEnv
    , cleanupContext

    -- * Execute Queries
    , command
    , smtWrite

    -- * Query API
    , smtDecl
    , smtAssert
    , smtCheckUnsat
    , smtCheckSat
    , smtBracket
    , smtDistinct
    , smtDoInterpolate
    , smtInterpolate

    -- * Theory Symbols
    -- , theorySymbols
      -- smt_set_funs

    -- * Check Validity
    , checkValid, checkValidWithContext
    , checkValids
    , makeZ3Context

    ) where

import           Language.Fixpoint.Types.Config (SMTSolver (..))
import           Language.Fixpoint.Misc   (errorstar)
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Visitor
import           Language.Fixpoint.Smt.Types
import           Language.Fixpoint.Smt.Theories  (preamble)
import           Language.Fixpoint.Smt.Serialize (initSMTEnv)


import           Control.Applicative      ((<|>))
import           Control.Monad
import           Control.Monad.State
import           Data.Char
import           Data.Monoid
import           Data.List                as L
import qualified Data.Text                as T
import           Data.Text.Format         hiding (format)
import qualified Data.Text.IO             as TIO
import           Data.Interned
-- import qualified Data.Text.Lazy           as LT
-- import qualified Data.Text.Lazy.IO        as LTIO
import           System.Directory
import           System.Console.CmdArgs.Verbosity
import           System.Exit              hiding (die)
import           System.FilePath
import           System.IO                (IOMode (..), hClose, hFlush, openFile)
import           System.Process
import qualified Data.Attoparsec.Text     as A
-- import qualified Debug.Trace as DT
import           Text.PrettyPrint.HughesPJ (text)
import           Text.Read (readMaybe)

{-
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


-- TODO take makeContext's Bool from caller instead of always using False?
makeZ3Context :: FilePath -> [(Symbol, Sort)] -> IO Context
makeZ3Context f xts
  = do me <- makeContextWithSEnv False Z3 f $ fromListSEnv xts
       smtDecls me (toListSEnv initSMTEnv)
       smtDecls me xts
       return me

checkValidWithContext :: Context -> [(Symbol, Sort)] -> Expr -> Expr -> IO Bool
checkValidWithContext me xts p q
  = smtBracket me $ do smtDecls me xts
                       smtAssert me $ pAnd [p, PNot q]
                       smtCheckUnsat me


-- | type ClosedPred E = {v:Pred | subset (vars v) (keys E) }
-- checkValid :: e:Env -> ClosedPred e -> ClosedPred e -> IO Bool
checkValid :: Bool -> FilePath -> [(Symbol, Sort)] -> Expr -> Expr -> IO Bool
checkValid u f xts p q
  = do me <- makeContext u Z3 f
       smtDecls me xts
       smtAssert me $ pAnd [p, PNot q]
       smtCheckUnsat me

-- | If you already HAVE a context, where all the variables have declared types
--   (e.g. if you want to make MANY repeated Queries)

-- checkValid :: e:Env -> [ClosedPred e] -> IO [Bool]
checkValids :: Bool -> FilePath -> [(Symbol, Sort)] -> [Expr] -> IO [Bool]
checkValids u f xts ps
  = do me <- makeContext u Z3 f
       smtDecls me xts
       forM ps $ \p ->
          smtBracket me $
            smtAssert me (PNot p) >> smtCheckUnsat me

-- debugFile :: FilePath
-- debugFile = "DEBUG.smt2"

--------------------------------------------------------------------------
-- | SMT IO --------------------------------------------------------------
--------------------------------------------------------------------------


--------------------------------------------------------------------------
command              :: Context -> Command -> IO Response
--------------------------------------------------------------------------
command me !cmd      = {-# SCC "command" #-} say cmd >> hear cmd
  where
    say cmd           = smtWrite me $ runSmt2 (smtenv me) cmd
    hear CheckSat     = smtRead me
    hear (GetValue _) = smtRead me
    hear (Interpolate n _) = do
      -- write the interpolation query to interp.out
      -- withFile "interp.out" WriteMode $ \handle -> do
        -- hPutStrLnNow handle $ runSmt2 (smtenv me) cmd

      resp <- smtRead me
      case resp of
        Unsat -> smtPred n me
        Sat -> error "Not UNSAT. No interpolation needed. Why did you call me?"
        e -> error $ show e
 
    hear _            = return Ok


smtWrite :: Context -> T.Text -> IO ()
smtWrite me !s = smtWriteRaw me s

smtRes :: Context -> A.IResult T.Text Response -> IO Response
smtRes me res = case A.eitherResult res of
  Left e  -> error e
  Right r -> do
    maybe (return ()) (\h -> hPutStrLnNow h $ format "; SMT Says: {}" (Only $ show r)) (cLog me)
    when (verbose me) $
      TIO.putStrLn $ format "SMT Says: {}" (Only $ show r)
    return r


-- smtParse me parserP = DT.traceShowId <$> smtReadRaw me >>= A.parseWith (smtReadRaw me) parserP >>= smtRes me
smtParse me parserP = do
  t <- smtReadRaw me
  p <- A.parseWith (smtReadRaw me) parserP t
  smtRes me p

smtParse' me parserP = do
  t <- smtReadRaw me
  let t' = t `T.append` (T.singleton '\n')
  p <- return $ A.parse parserP t'
  smtRes me p

{-
smtReadRawLines me = smtReadRawLines_ me []
  where smtReadRawLines_ me acc = do
          t <- smtReadRaw me
          if t == T.empty then return acc else smtReadRawLines_ me (t:acc)

smtParse' me parserP = do
  ts <- smtReadRawLines me
  putStrLn "Interpolants (RAW):"
  forM ts Prelude.print
  -- ps <- return $ A.parse parserP t
  let ps = map (A.parse parserP) ts
  forM ps (smtRes me)
-}

smtRead :: Context -> IO Response
smtRead me = {-# SCC "smtRead" #-} smtParse me responseP

smtPred :: Int -> Context -> IO Response
smtPred n me = {-# SCC "smtPred" #-} do
  responses <- forM [1..n] $ \_ -> parseInterp
  return $ Interpolant $ concatMap getInterps responses
  -- responses <- parseInterp
  -- return $ Interpolant $ concatMap getInterps responses
  where parseInterp = do
          -- ps <- smtParse me (Interpolant <$> map parseLisp' <$> predP)
          p <- smtParse' me (Interpolant <$> (\e -> [e]) <$> parseLisp' <$> predP)
          return p
        getInterps (Interpolant e) = e
        getInterps _ = []
-- smtPred n me = {-# SCC "smtPred" #-} smtParse me (Interpolant <$> (\x -> [x]) <$> parseLisp' <$> predP)

-- space that 
space2 c = isSpace c && not (A.isEndOfLine c)

predP = {-# SCC "predP" #-}
        (Lisp <$> (A.char '(' *> A.sepBy' predP (A.skipWhile space2) <* A.char ')'))
    <|> (Sym <$> symbolP)

data Lisp = Sym Symbol | Lisp [Lisp] deriving (Eq,Show)
-- type PorE = Either Expr Expr

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

parseLisp' = parseLisp

parseLisp :: Lisp -> Expr
parseLisp (Sym s)
  | symbolText s == "true"  = PTrue
  | symbolText s == "false" = PFalse
  | Just n <- readMaybe (symbolString s) :: Maybe Integer = (ECon (I n))
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

{-

parseLisp' :: Lisp -> Expr
parseLisp' = toPred
  where toPred :: Lisp -> Expr
        toPred x = case parseLisp x of
                     Left p -> p
                     Right e -> error $ "expected Pred, got Expr: " ++ show e
        toExpr :: Lisp -> Expr
        toExpr x = case parseLisp x of
                     Left p -> error $ "expected Expr, got Pred: " ++ show p
                     Right e -> e
          | symbolText s == "true" = Left PTrue
          | symbolText s == "false" = Left PFalse
          | otherwise = Right $ EVar s
        parseLisp (Lisp (Sym s:xs))
          | symbolText s == "and" = Left $ PAnd $ L.map toPred xs
          | symbolText s == "or" = Left $ POr $ L.map toPred xs
        parseLisp (Lisp [Sym s,x])
          | symbolText s == "not" = Left $ PNot $ toPred x
          | symbolText s == "-" = Right $ ENeg $ toExpr x
          | otherwise           = Right $ EVar s -- ELit (dummyLoc s) $ fromJust $ lookup s (lits fi)
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
        -- parseLisp (Lisp (Sym s:xs)) = Right $ EApp (dummyLoc s) $ L.map toExpr xs
        parseLisp x = error $ show x ++ "is Nonsense Lisp!"
        -- PBexp? When do I know to read one of these in?
-}

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

symbolP = {-# SCC "symbolP" #-} textSymbol <$> unintern <$> symbol <$> A.takeWhile1 (\x -> x /= ')' && not (isSpace x) && not (A.isEndOfLine x))

valueP = {-# SCC "valueP" #-} negativeP
      <|> A.takeWhile1 (\c -> not (c == ')' || isSpace c))

negativeP
  = do v <- A.char '(' *> A.takeWhile1 (/=')') <* A.char ')'
       return $ "(" <> v <> ")"

-- {- pairs :: {v:[a] | (len v) mod 2 = 0} -> [(a,a)] -}
-- pairs :: [a] -> [(a,a)]
-- pairs !xs = case L.splitAt 2 xs of
--              ([],_)      -> []
--              ([x,y], zs) -> (x,y) : pairs zs

smtWriteRaw      :: Context -> T.Text -> IO ()
smtWriteRaw me !s = {-# SCC "smtWriteRaw" #-} do
  hPutStrLnNow (cOut me) s
  -- whenLoud $ TIO.appendFile debugFile (s <> "\n")
  maybe (return ()) (`hPutStrLnNow` s) (cLog me)

smtReadRaw       :: Context -> IO Raw
smtReadRaw me    = {-# SCC "smtReadRaw" #-} TIO.hGetLine (cIn me)

hPutStrLnNow h !s   = TIO.hPutStrLn h s >> hFlush h

--------------------------------------------------------------------------
-- | SMT Context ---------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
makeContext   :: Bool -> SMTSolver -> FilePath -> IO Context
--------------------------------------------------------------------------
makeContext u s f
  = do me   <- makeProcess s
       pre  <- smtPreamble u s me
       createDirectoryIfMissing True $ takeDirectory smtFile
       hLog <- openFile smtFile WriteMode
       let me' = me { cLog = Just hLog }
       mapM_ (smtWrite me') pre
       return me'
    where
       smtFile = extFileName Smt2 f

makeContextWithSEnv :: Bool -> SMTSolver -> FilePath  -> SMTEnv -> IO Context
makeContextWithSEnv u s f env
  = (\cxt -> cxt {smtenv = env}) <$> makeContext u s f

makeContextNoLog :: Bool -> SMTSolver -> IO Context
makeContextNoLog u s
  = do me  <- makeProcess s
       pre <- smtPreamble u s me
       mapM_ (smtWrite me) pre
       return me

makeProcess :: SMTSolver -> IO Context
makeProcess s
  = do (hOut, hIn, _ ,pid) <- runInteractiveCommand $ smtCmd s
       loud <- isLoud
       return Ctx { pId     = pid
                  , cIn     = hIn
                  , cOut    = hOut
                  , cLog    = Nothing
                  , verbose = loud
                  , smtenv  = initSMTEnv
                  }

--------------------------------------------------------------------------
cleanupContext :: Context -> IO ExitCode
--------------------------------------------------------------------------
cleanupContext (Ctx {..})
  = do hClose cIn
       hClose cOut
       maybe (return ()) hClose cLog
       waitForProcess pId

{- "z3 -smt2 -in"                   -}
{- "z3 -smtc SOFT_TIMEOUT=1000 -in" -}
{- "z3 -smtc -in MBQI=false"        -}

smtCmd Z3      = "z3 pp.single-line=true -smt2 -in"
smtCmd Mathsat = "mathsat -input=smt2"
smtCmd Cvc4    = "cvc4 --incremental -L smtlib2"

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
smtPreamble u Z3 me
  = do smtWrite me "(get-info :version)"
       v:_ <- T.words . (!!1) . T.splitOn "\"" <$> smtReadRaw me
       if T.splitOn "." v `versionGreater` ["4", "3", "2"]
         then return $ z3_432_options ++ preamble u Z3
         else return $ z3_options     ++ preamble u Z3
smtPreamble u s _
  = return $ preamble u s

versionGreater (x:xs) (y:ys)
  | x >  y = True
  | x == y = versionGreater xs ys
  | x <  y = False
versionGreater _  [] = True
versionGreater [] _  = False
versionGreater _ _ = errorstar "Interface.versionGreater called with bad arguments"

-----------------------------------------------------------------------------
-- | SMT Commands -----------------------------------------------------------
-----------------------------------------------------------------------------

smtPush, smtPop   :: Context -> IO ()
smtPush me        = interact' me Push
smtPop me         = interact' me Pop


smtDecls :: Context -> [(Symbol, Sort)] -> IO ()
smtDecls me xts = forM_ xts (\(x,t) -> smtDecl me x t)

smtDecl :: Context -> Symbol -> Sort -> IO ()
smtDecl me x t = interact' me (Declare x ins out)
  where
    (ins, out) = deconSort t

deconSort :: Sort -> ([Sort], Sort)
deconSort t = case functionSort t of
                Just (_, ins, out) -> (ins, out)
                Nothing            -> ([] , t  )

smtCheckSat :: Context -> Expr -> IO Bool
smtCheckSat me p
-- hack now this is used only for checking gradual condition.
 = smtAssert me p >> (ans <$> command me CheckSat)
 where
   ans Sat = True
   ans _   = False

smtAssert :: Context -> Expr -> IO ()
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

-- the number of interpolants we expect from Z3
countInterp :: Expr -> Int
countInterp e = getSum $ execState (visit visitInterp () e) (Sum 0)
  where incInterp _ (Interp _)  = Sum 1
        incInterp _ _           = Sum 0
        visitInterp :: Visitor (Sum Int) ()
        visitInterp = (defaultVisitor :: Visitor (Sum Int) ()) { accExpr = incInterp } 

smtDoInterpolate :: Context -> SInfo a -> Expr -> IO [Expr]
smtDoInterpolate me _ p = do
  -- icontext <- makeZ3Context "interp.out" (toListSEnv $ lits sinfo)
  -- smtWrite icontext $ runSmt2 (smtenv icontext) p

  respInterp <$> command me (Interpolate n p)
  where n = countInterp p 

{-
smtLoadEnv :: Context -> [(Symbol, SortedReft)] -> IO ()
smtLoadEnv me env = mapM_ smtDecl' $ L.map (second sr_sort) env
  where smtDecl' = uncurry $ smtDecl me
-}

smtInterpolate :: Context -> SInfo () -> Expr -> IO [Expr]
smtInterpolate me _ p = respInterp <$> command me (Interpolate n p)
  where n = countInterp p 

respInterp (Interpolant ps) = ps
respInterp r = die $ err dummySpan $ text ("crash: SMTLIB2 respInterp = " ++ show r)

respSat Unsat   = True
respSat Sat     = False
respSat Unknown = False
respSat r       = die $ err dummySpan $ text ("crash: SMTLIB2 respSat = " ++ show r)

interact' me cmd  = void $ command me cmd

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
z3_432_options
  = [ "(set-option :auto-config false)"
    , "(set-option :model true)"
    , "(set-option :model.partial false)"
    , "(set-option :smt.mbqi false)"
    -- add these options so Z3 doesn't let-simplify interpolants
    , "(set-option :pp.max-depth 1000)"
    , "(set-option :pp.min-alias-size 1000)"]

z3_options
  = [ "(set-option :auto-config false)"
    , "(set-option :model true)"
    , "(set-option :model-partial false)"
    , "(set-option :mbqi false)"
    -- add these options so Z3 doesn't let-simplify interpolants
    , "(set-option :pp.max-depth 1000)"
    , "(set-option :pp.min-alias-size 1000)"]
