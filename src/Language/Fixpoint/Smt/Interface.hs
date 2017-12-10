{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE PatternGuards             #-}
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
    , smtDecls
    , smtAssert
    -- , smtDataDecl
    , smtFuncDecl
    , smtAssertAxiom
    , smtCheckUnsat
    , smtCheckSat
    , smtBracket, smtBracketAt
    , smtDistinct
    , smtPush, smtPop

    -- * Check Validity
    , checkValid
    , checkValid'
    , checkValidWithContext
    , checkValids
    , getValuesText
    , getValuesExpr

    -- * Evaluate SMT2LIB Lisp
    , eval
    , SpecVal (..)
    , toBool
    , toDouble
    ) where

import           Language.Fixpoint.Types.Config ( SMTSolver (..)
                                                , Config
                                                , solver
                                                , extensionality
                                                , alphaEquivalence
                                                , betaEquivalence
                                                , normalForm
                                                , stringTheory)
import qualified Language.Fixpoint.Misc          as Misc
import qualified Language.Fixpoint.Types.Visitor as Vis
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Types         hiding (allowHO)
import qualified Language.Fixpoint.Types         as F
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy
import           Language.Fixpoint.Smt.Serialize ()
import           Control.Applicative      ((<|>))
import           Control.Arrow
import           Control.Monad
import           Control.Exception
import           Data.Char
import qualified Data.HashMap.Strict      as M
import           Data.Maybe                  (fromMaybe)
import qualified Data.Text                as T
import           Data.Text.Format
import qualified Data.Text.IO             as TIO
import qualified Data.Text.Lazy           as LT
import qualified Data.Text.Lazy.Builder   as Builder
import qualified Data.Text.Lazy.IO        as LTIO
import           Data.Text.Read              (decimal)
import           System.Directory
import           System.Console.CmdArgs.Verbosity
import           System.Exit              hiding (die)
import           System.FilePath
import           System.IO                (Handle, IOMode (..), hClose, hFlush, openFile)
import           System.Process
import qualified Data.Attoparsec.Text     as A
-- import qualified Data.HashMap.Strict      as M
import           Data.Attoparsec.Internal.Types (Parser)
import           Text.PrettyPrint.HughesPJ (text)
import           Text.Read (readMaybe)
import           Language.Fixpoint.SortCheck
-- import qualified Language.Fixpoint.Types as F
-- import           Language.Fixpoint.Types.PrettyPrint (tracepp)
import           Control.Monad.IO.Class

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

checkValidWithContext :: Context -> [(Symbol, Sort)] -> Expr -> Expr -> IO Bool
checkValidWithContext me xts p q =
  smtBracket me "checkValidWithContext" $
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
          smtBracket me "checkValids" $
            smtAssert me (PNot p) >> smtCheckUnsat me

getValuesText :: Context -> [(Symbol, Sort)] -> Expr -> [Symbol] -> IO [(Symbol, T.Text)]
getValuesText me xts p xs = do
  smtDecls me xts
  smtAssert me p
  smtCheckUnsat me
  map (second lispToText) <$> smtGetValues me xs

getValuesExpr :: Context -> [Symbol] -> IO CntrEx
getValuesExpr me xs = smtBracket me "getDefModel" $ do
  smtCheckUnsat me
  M.fromList <$> map (second lispToExpr) <$> smtGetValues me xs


-- debugFile :: FilePath
-- debugFile = "DEBUG.smt2"

--------------------------------------------------------------------------------
-- | SMT IO --------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
command              :: Context -> Command -> IO Response
--------------------------------------------------------------------------------
command me !cmd       = say cmd >> hear cmd
  where
    env               = ctxSymEnv me
    say               = smtWrite me . Builder.toLazyText . runSmt2 env
    hear CheckSat     = smtRead me
    hear (GetValue _) = smtRead me
    hear (GetModel)   = smtRead me
    hear _            = return Ok


smtWrite :: Context -> Raw -> IO ()
smtWrite me !s = smtWriteRaw me s

smtRead :: Context -> IO Response
smtRead me = {-# SCC "smtRead" #-} do
  when (ctxVerbose me) $ LTIO.putStrLn "SMT READ"
  ln  <- smtReadRaw me
  res <- A.parseWith (smtReadRaw me) responseP ln
  case A.eitherResult res of
    Left e  -> Misc.errorstar $ "SMTREAD:" ++ e
    Right r -> do
      maybe (return ()) (\h -> hPutStrLnNow h $ format "; SMT Says: {}" (Only $ show r)) (ctxLog me)
      when (ctxVerbose me) $ LTIO.putStrLn $ format "SMT Says: {}" (Only $ show r)
      return r

type SmtParser a = Parser T.Text a

responseP :: SmtParser Response
responseP = {-# SCC "responseP" #-} A.peekChar' >>= \case
              '(' -> responseBodyP
              _ ->     A.string "sat"     *> return Sat
                   <|> A.string "unsat"   *> return Unsat
                   <|> A.string "unknown" *> return Unknown

responseBodyP :: SmtParser Response
responseBodyP = {-# SCC "responseBodyP" #-} A.string "(error" *> (Error <$> errorP)
     <|> modelOrValues <$> lispP

modelOrValues :: Lisp -> Response
modelOrValues (Lisp ((Sym s):ls))
  | symbolText s == "model" = toModel $ ls
modelOrValues (Lisp ls) = Values $ map (\(Lisp [(Sym sym), e]) -> (sym, e)) ls
modelOrValues (Sym s) = error $ "unknown symbol when expecting Model or Values" ++ show s

lispToText :: Lisp -> T.Text
lispToText (Lisp xs) = "(" `T.append` foldr (\ x y -> x `T.append` " " `T.append` y) ")" (lispToText <$> xs)
lispToText (Sym s) = symbolText s

toModel ls = Model $ M.fromList $ lispToModel <$> ls

lispToModel (Lisp [_,Sym sym, Lisp args,_,expr]) = (sym, foldr abstract (lispToExpr expr) args)
      where abstract (Lisp [Sym x,_]) e = ELam (x,FInt) e
            abstract _ _ = error "reading in a bad list of formals"

            -- Since we can't recover full typing information from the SMT
            -- Sovler, we just give up and give it FInt. Hopefully this make
            -- everyone who tries to use it wrong crash.

lispToModel l = error $ "Expecting Lisp Define-fun, Got " ++ show l


errorP :: SmtParser T.Text
errorP = A.skipSpace *> A.char '"' *> A.takeWhile1 (/='"') <* A.string "\")"

symbolP :: SmtParser Symbol
symbolP = {-# SCC "symbolP" #-} symbol . decode <$> A.takeWhile1 (\x -> x /= ')' && not (isSpace x) && not (A.isEndOfLine x))

fromRight (Right a) = a
fromRight (Left _) = error "FROMRIGHT LEFT"

decode :: T.Text -> T.Text
decode s = T.concat $ zipWith ($) (cycle [id, T.singleton . chr . fst . fromRight . decimal]) (T.split (=='$') s)

lispP = {-# SCC "lispP" #-}
      (Lisp <$> (A.char '(' *> A.sepBy' lispP (A.skipWhile space2) <* A.char ')'))
  <|> (Sym <$> symbolP)

space2 c = isSpace c && not (A.isEndOfLine c)

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

lispToExpr :: Lisp -> Expr
lispToExpr (Sym s)
  | symbolText s == "true"  = PTrue
  | symbolText s == "false" = PFalse
  -- | Just n <- readMaybe (symbolString s) :: Maybe Integer = (ECon (I n))
  | Just n <- readMaybe (symbolString s) :: Maybe Double  = (ECon (R n))
  | otherwise               = EVar s
lispToExpr l@(Lisp xs)
  | [Sym s, x] <- xs, symbolText s == "not"     =
    PNot (lispToExpr x)
  | [Sym s, x] <- xs, symbolText s == "-"       =
    ENeg (lispToExpr x)
  | [Sym s, x, y] <- xs, symbolText s == "=>"   =
    PImp (lispToExpr x) (lispToExpr y)
  | [Sym s, x, y] <- xs, symbolText s == "="    =
    PAtom Eq (lispToExpr x) (lispToExpr y)
  | [Sym s, x, y] <- xs, symbolText s `elem` binOpStrings  =
    EBin (strToOp $ symbolText s) (lispToExpr x) (lispToExpr y)
  | [Sym s, x, y] <- xs, symbolText s `elem` binRelStrings =
    PAtom (strToRel $ symbolText s) (lispToExpr x) (lispToExpr y)
  | [Sym s,x,y,z] <- xs, symbolText s == "ite"  =
    EIte (lispToExpr x) (lispToExpr y) (lispToExpr z)
  | (Sym s:xs) <- xs, symbolText s == "and"     =
    PAnd $ lispToExpr <$> xs
  | (Sym s:xs) <- xs, symbolText s == "or"      =
    POr $ lispToExpr <$> xs
  | otherwise                                   =
    lispToFunc l
  where lispToFunc (Lisp xs) = foldr1 EApp $ map lispToExpr xs
        -- this should not be called
        lispToFunc (Sym s)   = EVar s

opDenote :: Bop -> Double -> Double -> Double
opDenote Plus  = (+)
opDenote Minus = (-)
opDenote Times = (*)
opDenote Div   = (/)
-- Below here, untested
opDenote Mod   = \a b -> fromIntegral $ mod (floor a) (floor b)
opDenote RTimes = (*)
opDenote RDiv  = (/)

relDenote Gt = (>)
relDenote Ge = (>=)
relDenote Lt = (<)
relDenote Le = (<=)
relDenote Eq = (==)
relDenote Ne = (/=)
-- Not sure what these two do
relDenote Ueq = (/=)
relDenote Une = (/=)

data SpecVal = B_ Bool | I_ Integer | D_ Double | L_ (Expr -> Maybe SpecVal)

toBool :: Maybe SpecVal -> Maybe Bool
toBool (Just (B_ b)) = Just b
toBool _ = Nothing

toDouble :: Maybe SpecVal -> Maybe Double
toDouble (Just (D_ d)) = Just d
toDouble (Just (I_ d)) = Just $ fromIntegral d
toDouble _ = Nothing


lookupDM (m1, m2) s = M.lookup s m1 <|> M.lookup s m2

eval :: (CntrEx,CntrEx) -> Expr -> Maybe SpecVal
eval ctx (EIte b e1 e2)
  = (\b' -> if b' then eval ctx e1 else eval ctx e2) =<<
    toBool (eval ctx b)
eval ctx (PAtom r e1 e2)
  = fmap B_ $ relDenote r <$> a <*> b
  where a = toDouble $ eval ctx e1
        b = toDouble $ eval ctx e2
eval ctx (EBin o e1 e2)
  = fmap D_ $ opDenote o <$> a <*> b
  where a = toDouble $ eval ctx e1
        b = toDouble $ eval ctx e2
eval ctx (ENeg e)
  = fmap D_ $ negate <$> toDouble (eval ctx e)
eval ctx (PNot e)
  = fmap B_ $ not <$> toBool (eval ctx e)
eval ctx (PImp e1 e2)
  = fmap B_ $ (<=) <$> b <*> a
  where a = toBool $ eval ctx e1
        b = toBool $ eval ctx e2
eval ctx (PIff e1 e2)
  = fmap B_ $ (==) <$> a <*> b
  where a = toBool $ eval ctx e1
        b = toBool $ eval ctx e2
eval ctx (PAnd es)
  = B_ . and <$> sequence (toBool . eval ctx <$> es)
eval ctx (POr es)
  = B_ . or <$> sequence (toBool . eval ctx <$> es)

eval ctx (ECst e _) = eval ctx e
eval _ (ECon (I n)) = Just $ I_ n
eval _ (ECon (R n)) = Just $ D_ n
eval ctx (ETApp e _) = eval ctx e
eval ctx (ETAbs e _) = eval ctx e

eval _ PKVar{}  = error "Someone forgot to subst a KVar.\n\
                     \ Please file a bug!               \
                     \ http://github.com/ucsd-progsys/liquid-fixpoint"
eval ctx (EVar s) = eval ctx $ flip fromMaybe (lookupDM ctx s) $ error $ "Unknown variable: " ++ (show s)

eval ctx (ELam (x,_) e)  = Just $ L_ $ \ex -> eval ctx $ subst1 e (x,ex)
-- eval ctx (EApp e'@EApp{} ex)       = eval ctx $ EApp (eval ctx e') x
eval ctx (EApp f e)  = f' e
  where Just (L_ f') = eval ctx f
-- eval ctx e@EApp{} = error $ "EApp not implemented in CEGIS for " ++ show e

eval _ PAll{}   = error "quantifiers are incompatible with --cegis"
eval _ PExist{} = error "quantifiers are incompatible with --cegis"

eval _ PGrad{}  = error "--cegis is incompatible with --gradual"
eval _ (ESym _) = error "--cegis doesn't yet support string lits"
eval _ (ECon (L _ _)) = error "--cegis doesn't yet support string lits"


smtWriteRaw      :: Context -> Raw -> IO ()
smtWriteRaw me !s = {-# SCC "smtWriteRaw" #-} do
  -- whenLoud $ do LTIO.appendFile debugFile (s <> "\n")
  --               LTIO.putStrLn ("CMD-RAW:" <> s <> ":CMD-RAW:DONE")
  hPutStrLnNow (ctxCout me) s
  maybe (return ()) (`hPutStrLnNow` s) (ctxLog me)

smtReadRaw       :: Context -> IO T.Text
smtReadRaw me    = {-# SCC "smtReadRaw" #-} TIO.hGetLine (ctxCin me)

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
       let me' = me { ctxLog = Just hLog }
       mapM_ (smtWrite me') pre
       return me'
    where
       smtFile = extFileName Smt2 f

makeContextWithSEnv :: Config -> FilePath -> SymEnv -> IO Context
makeContextWithSEnv cfg f env = do
  ctx     <- makeContext cfg f
  let ctx' = ctx {ctxSymEnv = env}
  declare ctx'
  return ctx'
  -- where msg = "makeContextWithSEnv" ++ show env

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
       return Ctx { ctxPid     = pid
                  , ctxCin     = hIn
                  , ctxCout    = hOut
                  , ctxLog     = Nothing
                  , ctxVerbose = loud
                  , ctxExt     = extensionality cfg
                  , ctxAeq     = alphaEquivalence cfg
                  , ctxBeq     = betaEquivalence  cfg
                  , ctxNorm    = normalForm       cfg
                  , ctxSymEnv  = mempty
                  }

--------------------------------------------------------------------------
cleanupContext :: Context -> IO ExitCode
--------------------------------------------------------------------------
cleanupContext (Ctx {..}) = do
  hCloseMe "ctxCin"  ctxCin
  hCloseMe "ctxCout" ctxCout
  maybe (return ()) (hCloseMe "ctxLog") ctxLog
  waitForProcess ctxPid

hCloseMe :: String -> Handle -> IO ()
hCloseMe msg h = hClose h `catch` (\(exn :: IOException) -> putStrLn $ "OOPS, hClose breaks: " ++ msg ++ show exn)

{- "z3 -smt2 -in"                   -}
{- "z3 -smtc SOFT_TIMEOUT=1000 -in" -}
{- "z3 -smtc -in MBQI=false"        -}

smtCmd         :: SMTSolver -> String --  T.Text
smtCmd Z3      = "z3 -smt2 -in"
smtCmd Mathsat = "mathsat -input=smt2"
smtCmd Cvc4    = "cvc4 --incremental -L smtlib2"

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
smtPreamble :: Config -> SMTSolver -> Context -> IO [LT.Text]
smtPreamble cfg Z3 me
  = do smtWrite me "(get-info :version)"
       v:_ <- T.words . (!!1) . T.splitOn "\"" <$> smtReadRaw me
       checkValidStringFlag Z3 v cfg
       if T.splitOn "." v `versionGreaterEq` ["4", "3", "2"]
         then return $ z3_432_options ++ makeMbqi cfg ++ Thy.preamble cfg Z3
         else return $ z3_options     ++ makeMbqi cfg ++ Thy.preamble cfg Z3
smtPreamble cfg s _
  = checkValidStringFlag s "" cfg >> return (Thy.preamble cfg s)

checkValidStringFlag :: SMTSolver -> T.Text -> Config -> IO ()
checkValidStringFlag smt v cfg
  = when (noString smt v cfg) $
      die $ err dummySpan (text "stringTheory is only supported by z3 version >=4.2.2")

noString :: SMTSolver -> T.Text -> Config -> Bool
noString smt v cfg
  =  stringTheory cfg
  && not (smt == Z3 && (T.splitOn "." v `versionGreaterEq` ["4", "4", "2"]))


versionGreaterEq :: Ord a => [a] -> [a] -> Bool
versionGreaterEq (x:xs) (y:ys)
  | x >  y = True
  | x == y = versionGreaterEq xs ys
  | x <  y = False
versionGreaterEq _  [] = True
versionGreaterEq [] _  = False
versionGreaterEq _ _ = Misc.errorstar "Interface.versionGreater called with bad arguments"

-----------------------------------------------------------------------------
-- | SMT Commands -----------------------------------------------------------
-----------------------------------------------------------------------------

smtPush, smtPop   :: Context -> IO ()
smtPush me        = interact' me Push
smtPop me         = interact' me Pop

smtDecls :: Context -> [(Symbol, Sort)] -> IO ()
smtDecls = mapM_ . uncurry . smtDecl

smtDecl :: Context -> Symbol -> Sort -> IO ()
smtDecl me x t = interact' me (Declare x ins' out')
  where
    ins'       = sortSmtSort False env <$> ins
    out'       = sortSmtSort False env     out
    (ins, out) = deconSort t
    env        = seData (ctxSymEnv me)

smtFuncDecl :: Context -> Symbol -> ([SmtSort],  SmtSort) -> IO ()
smtFuncDecl me x (ts, t) = interact' me (Declare x ts t)

smtDataDecl :: Context -> DataDecl -> IO ()
smtDataDecl me d = interact' me (DeclData d)

deconSort :: Sort -> ([Sort], Sort)
deconSort t = case functionSort t of
                Just (_, ins, out) -> (ins, out)
                Nothing            -> ([] , t  )

-- hack now this is used only for checking gradual condition.
smtCheckSat :: Context -> Expr -> IO Bool
smtCheckSat me p
 = smtAssert me p >> (ans <$> command me CheckSat)
 where
   ans Sat = True
   ans _   = False

smtAssert :: Context -> Expr -> IO ()
smtAssert me p  = interact' me (Assert Nothing p)

smtAssertAxiom :: Context -> Triggered Expr -> IO ()
smtAssertAxiom me p  = interact' me (AssertAx p)

smtDistinct :: Context -> [Expr] -> IO ()
smtDistinct me az = interact' me (Distinct az)

smtCheckUnsat :: Context -> IO Bool
smtCheckUnsat me  = respSat <$> command me CheckSat

smtGetValues :: Context -> [Symbol] -> IO [(Symbol, Lisp)]
smtGetValues me xs = (\(Values x) -> x) <$> command me (GetValue xs)

smtBracketAt :: SrcSpan -> Context -> String -> IO a -> IO a
smtBracketAt sp x y z = smtBracket x y z `catch` dieAt sp


smtBracket :: MonadIO io => Context -> String -> io a -> io a
smtBracket me _msg a   = do
  liftIO $ smtPush me
  r <- a
  liftIO $ smtPop me
  return r

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
    , "(set-option :model.partial false)"]

z3_options :: [LT.Text]
z3_options
  = [ "(set-option :auto-config false)"
    , "(set-option :model true)"
    , "(set-option :model-partial false)"]



--------------------------------------------------------------------------------
declare :: Context -> IO () -- SolveM ()
--------------------------------------------------------------------------------
declare me = do
  forM_ ds     $           smtDataDecl me
  forM_ thyXTs $ uncurry $ smtDecl     me
  forM_ qryXTs $ uncurry $ smtDecl     me
  forM_ ats    $ uncurry $ smtFuncDecl me
  forM_ ess    $           smtDistinct me
  forM_ axs    $           smtAssert   me
  where
    env        = ctxSymEnv me
    ds         = dataDeclarations          env
    lts        = F.toListSEnv . F.seLits $ env
    ess        = distinctLiterals  lts
    axs        = Thy.axiomLiterals lts
    thyXTs     =                    filter (isKind 1) xts
    qryXTs     = Misc.mapSnd tx <$> filter (isKind 2) xts
    isKind n   = (n ==)  . symKind env . fst
    xts        = symbolSorts (F.seSort env) -- F.toListSEnv           (F.seSort env)
    tx         = elaborate    "declare" env
    ats        = funcSortVars env

symbolSorts :: F.SEnv F.Sort -> [(F.Symbol, F.Sort)]
symbolSorts env = [(x, tx t) | (x, t) <- F.toListSEnv env ]
 where
  tx t@(FObj a) = fromMaybe t (F.lookupSEnv a env)
  tx t          = t

dataDeclarations :: SymEnv -> [DataDecl]
dataDeclarations = -- (if True then orderDeclarations else id) .
                   orderDeclarations . map snd . F.toListSEnv . F.seData

funcSortVars :: F.SymEnv -> [(F.Symbol, ([F.SmtSort], F.SmtSort))]
funcSortVars env  = [(var applyName  t       , appSort t) | t <- ts]
                 ++ [(var lambdaName t       , lamSort t) | t <- ts]
                 ++ [(var (lamArgSymbol i) t , argSort t) | t@(_,F.SInt) <- ts, i <- [1..Thy.maxLamArg] ]
  where
    var n         = F.symbolAtSmtName n env ()
    ts            = M.keys (F.seAppls env)
    appSort (s,t) = ([F.SInt, s], t)
    lamSort (s,t) = ([s, t], F.SInt)
    argSort (s,_) = ([]    , s)

-- | 'symKind' returns {0, 1, 2} where:
--   0 = Theory-Definition,
--   1 = Theory-Declaration,
--   2 = Query-Binder

symKind :: F.SymEnv -> F.Symbol -> Int
symKind env x = case F.tsInterp <$> F.symEnvTheory x env of
                  Just F.Theory   -> 0
                  Just F.Ctor     -> 0
                  Just F.Test     -> 0
                  Just F.Field    -> 0
                  Just F.Uninterp -> 1
                  Nothing         -> 2
              -- Just t  -> if tsInterp t then 0 else 1


-- assumes :: [F.Expr] -> SolveM ()
-- assumes es = withContext $ \me -> forM_  es $ smtAssert me

-- | `distinctLiterals` is used solely to determine the set of literals
--   (of each sort) that are *disequal* to each other, e.g. EQ, LT, GT,
--   or string literals "cat", "dog", "mouse". These should only include
--   non-function sorted values.
distinctLiterals :: [(F.Symbol, F.Sort)] -> [[F.Expr]]
distinctLiterals xts = [ es | (_, es) <- tess ]
   where
    tess             = Misc.groupList [(t, F.expr x) | (x, t) <- xts, notFun t]
    notFun           = not . F.isFunctionSortedReft . (`F.RR` F.trueReft)
    -- _notStr          = not . (F.strSort ==) . F.sr_sort . (`F.RR` F.trueReft)

--------------------------------------------------------------------------------
-- | 'orderDeclarations' sorts the data declarations such that each declarations
--   only refers to preceding ones.
--------------------------------------------------------------------------------
orderDeclarations :: [F.DataDecl] -> [F.DataDecl]
--------------------------------------------------------------------------------
orderDeclarations ds = reverse (Misc.topoSortWith f ds)
  where
    dM               = M.fromList [(F.ddTyCon d, d) | d <- ds]
    f d              = (F.ddTyCon d, dataDeclDeps dM d)

dataDeclDeps :: M.HashMap F.FTycon F.DataDecl -> F.DataDecl -> [F.FTycon]
dataDeclDeps dM = filter (`M.member` dM) . Misc.sortNub . dataDeclFTycons

dataDeclFTycons :: F.DataDecl -> [F.FTycon]
dataDeclFTycons = concatMap dataCtorFTycons . F.ddCtors

dataCtorFTycons :: F.DataCtor -> [F.FTycon]
dataCtorFTycons = concatMap dataFieldFTycons . F.dcFields

dataFieldFTycons :: F.DataField -> [F.FTycon]
dataFieldFTycons = sortFTycons . F.dfSort

sortFTycons :: Sort -> [FTycon]
sortFTycons = Vis.foldSort go []
  where
    go cs (FTC c) = c : cs
    go cs _       = cs
