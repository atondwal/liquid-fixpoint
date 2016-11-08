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
    , checkValid
    , checkValidWithContext
    , checkValids
    , makeZ3Context

    ) where

import           Language.Fixpoint.Types.Config (SMTSolver (..), Config, solver
                                                , extensionality, alphaEquivalence, betaEquivalence, normalForm
                                                , stringTheory)
import           Language.Fixpoint.Misc   (errorstar)
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Types hiding (allowHO)
import           Language.Fixpoint.Types.Visitor
import           Language.Fixpoint.Smt.Types
import           Language.Fixpoint.Smt.Theories  (preamble)
import           Language.Fixpoint.Smt.Serialize (initSMTEnv)


import           Control.Applicative      ((<|>))
import           Control.Monad
import           Control.Monad.State.Strict
import           Data.Char
import           Data.Monoid
import           Data.List                as L
import qualified Data.Text                as T
import           Data.Text.Format
import qualified Data.Text.IO             as TIO
import qualified Data.Text.Lazy           as LT
import qualified Data.Text.Lazy.Builder   as Builder
import qualified Data.Text.Lazy.IO        as LTIO
import           System.Directory
import           System.Console.CmdArgs.Verbosity
import           System.Exit              hiding (die)
import           System.FilePath
import           System.IO                (Handle, IOMode (..), hClose, hFlush, openFile)
import           System.Process
import qualified Data.Attoparsec.Text     as A
import           Data.Attoparsec.Internal.Types (Parser)
import           Text.PrettyPrint.HughesPJ (text)
import           Text.Read (readMaybe)
import           Data.Text.Read (decimal)

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
makeZ3Context :: Config -> FilePath -> [(Symbol, Sort)] -> IO Context
makeZ3Context cfg f xts
  = do me <- makeContextWithSEnv cfg f $ fromListSEnv xts
       smtDecls me (toListSEnv initSMTEnv)
       smtDecls me xts
       return me

checkValidWithContext :: Context -> [(Symbol, Sort)] -> Expr -> Expr -> IO Bool
checkValidWithContext me xts p q =
  smtBracket me $
    checkValid' me xts p q
    
-- | type ClosedPred E = {v:Pred | subset (vars v) (keys E) }
-- checkValid :: e:Env -> ClosedPred e -> ClosedPred e -> IO Bool
checkValid :: Config -> FilePath -> [(Symbol, Sort)] -> Expr -> Expr -> IO Bool
checkValid cfg f xts p q = do
  me <- makeContext cfg f
  checkValid' me xts p q

checkValid' :: Context -> [(Symbol, Sort)] -> Expr -> Expr -> IO Bool
checkValid' me xts p q = do
  smtDecls me xts
  smtAssert me $ pAnd [p, PNot q]
  smtCheckUnsat me

-- | If you already HAVE a context, where all the variables have declared types
--   (e.g. if you want to make MANY repeated Queries)

-- checkValid :: e:Env -> [ClosedPred e] -> IO [Bool]
checkValids :: Config -> FilePath -> [(Symbol, Sort)] -> [Expr] -> IO [Bool]
checkValids cfg f xts ps
  = do me <- makeContext cfg f
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
command me !cmd       = say cmd >> hear cmd
  where
    say               = smtWrite me . Builder.toLazyText . runSmt2
    hear CheckSat     = smtRead me
    hear (GetValue _) = smtRead me
    hear (Interpolate n _) = do
      -- write the interpolation query to interp.out
      -- withFile "interp.out" WriteMode $ \handle -> do
        -- hPutStrLnNow handle $ runSmt2 (smtenv me) cmd

      resp <- smtRead me
      case resp of
        Unsat -> smtPred n me
        Sat -> putStrLn "Not UNSAT." >> return Sat
        e -> error $ show e
    hear _            = return Ok


smtWrite :: Context -> Raw -> IO ()
smtWrite me !s = smtWriteRaw me s

smtRes :: Context -> A.IResult T.Text Response -> IO Response
smtRes me res = case A.eitherResult res of
  Left e  -> error e
  Right r -> do
    maybe (return ()) (\h -> hPutStrLnNow h $ format "; SMT Says: {}" (Only $ show r)) (cLog me)
    when (verbose me) $
      LTIO.putStrLn $ format "SMT Says: {}" (Only $ show r)
    return r


smtParse me parserP = do
  t <- smtReadRaw me
  p <- A.parseWith (smtReadRaw me) parserP t
  smtRes me p

smtParse' me parserP = do
  t <- smtReadRaw me
  let t' = t `T.append` (T.singleton '\n')
  p <- return $ A.parse parserP t'
  smtRes me p

smtRead :: Context -> IO Response
smtRead me = {-# SCC "smtRead" #-} smtParse me responseP

smtPred :: Int -> Context -> IO Response
smtPred n me = {-# SCC "smtPred" #-} do
  responses <- forM [1..n] $ \_ -> parseInterp
  return $ Interpolant $ concatMap getInterps responses
  where parseInterp = do
          p <- smtParse' me (Interpolant <$> (\e -> [e]) <$> parseLisp <$> predP)
          return p
        getInterps (Interpolant e) = e
        getInterps _ = []

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

responseP :: SmtParser Response
responseP = {-# SCC "responseP" #-} A.char '(' *> sexpP
         <|> A.string "sat"     *> return Sat
         <|> A.string "unsat"   *> return Unsat
         <|> A.string "unknown" *> return Unknown

sexpP :: SmtParser Response
sexpP = {-# SCC "sexpP" #-} A.string "error" *> (Error <$> errorP)
     <|> Values <$> valuesP

errorP :: SmtParser T.Text
errorP = A.skipSpace *> A.char '"' *> A.takeWhile1 (/='"') <* A.string "\")"

valuesP :: SmtParser [(Symbol, T.Text)]
valuesP = A.many1' pairP <* A.char ')'

pairP :: SmtParser (Symbol, T.Text)
pairP = {-# SCC "pairP" #-}
  do A.skipSpace
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
  = do v <- A.char '(' *> A.takeWhile1 (/=')') <* A.char ')'
       return $ "(" <> v <> ")"

-- {- pairs :: {v:[a] | (len v) mod 2 = 0} -> [(a,a)] -}
-- pairs :: [a] -> [(a,a)]
-- pairs !xs = case L.splitAt 2 xs of
--              ([],_)      -> []
--              ([x,y], zs) -> (x,y) : pairs zs

smtWriteRaw      :: Context -> Raw -> IO ()
smtWriteRaw me !s = {-# SCC "smtWriteRaw" #-} do
  hPutStrLnNow (cOut me) s
  -- whenLoud $ TIO.appendFile debugFile (s <> "\n")
  maybe (return ()) (`hPutStrLnNow` s) (cLog me)

smtReadRaw       :: Context -> IO T.Text
smtReadRaw me    = {-# SCC "smtReadRaw" #-} TIO.hGetLine (cIn me)

hPutStrLnNow     :: Handle -> LT.Text -> IO ()
hPutStrLnNow h !s = LTIO.hPutStrLn h s >> hFlush h

--------------------------------------------------------------------------
-- | SMT Context ---------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
makeContext   :: Config -> FilePath -> IO Context
--------------------------------------------------------------------------
makeContext cfg f
  = do me   <- makeProcess cfg
       pre  <- smtPreamble cfg (solver cfg) me
       createDirectoryIfMissing True $ takeDirectory smtFile
       hLog <- openFile smtFile WriteMode
       let me' = me { cLog = Just hLog }
       mapM_ (smtWrite me') pre
       return me'
    where
       smtFile = extFileName Smt2 f

makeContextWithSEnv :: Config -> FilePath  -> SMTEnv -> IO Context
makeContextWithSEnv cfg f env
  = (\cxt -> cxt {smtenv = env}) <$> makeContext cfg f

makeContextNoLog :: Config -> IO Context
makeContextNoLog cfg
  = do me  <- makeProcess cfg
       pre <- smtPreamble cfg (solver cfg) me
       mapM_ (smtWrite me) pre
       return me

makeProcess :: Config -> IO Context
makeProcess cfg
  = do (hOut, hIn, _ ,pid) <- runInteractiveCommand $ smtCmd (solver cfg)
       loud <- isLoud
       return Ctx { pId     = pid
                  , cIn     = hIn
                  , cOut    = hOut
                  , cLog    = Nothing
                  , verbose = loud
                  , c_ext   = extensionality cfg
                  , c_aeq   = alphaEquivalence cfg  
                  , c_beq   = betaEquivalence  cfg  
                  , c_norm  = normalForm       cfg 
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

smtCmd         :: SMTSolver -> String --  T.Text
smtCmd Z3      = "z3 pp.single-line=true -smt2 -in"
smtCmd Mathsat = "mathsat -input=smt2"
smtCmd Cvc4    = "cvc4 --incremental -L smtlib2"

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
smtPreamble :: Config -> SMTSolver -> Context -> IO [LT.Text]
smtPreamble cfg Z3 me
  = do smtWrite me "(get-info :version)"
       v:_ <- T.words . (!!1) . T.splitOn "\"" <$> smtReadRaw me
       checkValidStringFlag Z3 v cfg
       if T.splitOn "." v `versionGreaterEq` ["4", "3", "2"]
         then return $ z3_432_options ++ makeMbqi cfg ++ preamble cfg Z3
         else return $ z3_options     ++ makeMbqi cfg ++ preamble cfg Z3
smtPreamble cfg s _
  = checkValidStringFlag s "" cfg >> (return $ preamble cfg s)

checkValidStringFlag :: SMTSolver -> T.Text -> Config -> IO ()
checkValidStringFlag smt v cfg 
  = if    (stringTheory cfg) 
       && not (smt == Z3 && (T.splitOn "." v `versionGreaterEq` ["4", "4", "2"]))
      then die $ err dummySpan (text $ "stringTheory is only supported by z3 version >=4.2.2")
      else return ()

versionGreaterEq :: Ord a => [a] -> [a] -> Bool
versionGreaterEq (x:xs) (y:ys)
  | x >  y = True
  | x == y = versionGreaterEq xs ys
  | x <  y = False
versionGreaterEq _  [] = True
versionGreaterEq [] _  = False
versionGreaterEq _ _ = errorstar "Interface.versionGreater called with bad arguments"

-----------------------------------------------------------------------------
-- | SMT Commands -----------------------------------------------------------
-----------------------------------------------------------------------------

smtPush, smtPop   :: Context -> IO ()
smtPush me        = interact' me Push
smtPop me         = interact' me Pop

smtDecls :: Context -> [(Symbol, Sort)] -> IO ()
smtDecls = mapM_ . uncurry . smtDecl

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
smtBracket me a   = do
  smtPush me
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
respInterp Sat = []
respInterp r = die $ err dummySpan $ text ("crash: SMTLIB2 respInterp = " ++ show r)

respSat :: Response -> Bool
respSat Unsat   = True
respSat Sat     = False
respSat Unknown = False
respSat r       = die $ err dummySpan $ text ("crash: SMTLIB2 respSat = " ++ show r)

interact' :: Context -> Command -> IO ()
interact' me cmd  = void $ command me cmd

makeMbqi :: Config -> [LT.Text]
makeMbqi cfg
  | extensionality cfg = [""]
  | otherwise          = ["\n(set-option :smt.mbqi false)"]

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
z3_432_options :: [LT.Text]
z3_432_options
  = [ "(set-option :auto-config false)"
    , "(set-option :model true)"
    , "(set-option :model.partial false)"
    , "(set-option :smt.mbqi false)"
    -- add these options so Z3 doesn't let-simplify interpolants
    , "(set-option :pp.max-depth 1000)"
    , "(set-option :pp.min-alias-size 1000)"]

z3_options :: [LT.Text]
z3_options
  = [ "(set-option :auto-config false)"
    , "(set-option :model true)"
    , "(set-option :model-partial false)"
    , "(set-option :mbqi false)"
    -- add these options so Z3 doesn't let-simplify interpolants
    , "(set-option :pp.max-depth 1000)"
    , "(set-option :pp.min-alias-size 1000)"]
