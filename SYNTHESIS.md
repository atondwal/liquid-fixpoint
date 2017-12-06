# Overview

Given a graph of cut kvars, we want to perform synthesis on them.

```
    /> κ₁\
   /      \
κ₀/ -> κ₂->> κ₃ -> .
```

Now, we start with some computed solution (at the end of `solve_`), and then we take the "query clauses". The ones we care about will always be failing constraints! So just sweep over those and grab the ones that don't have any kvars on the rhs (later: just grab all of them, not just the ones with kvarless rhs).

We recurse back to the previous kvar where we strengthen with crap[0] until it satisfies the subsequent fellas.

If it doesn't satisfy the subsequent fellas, we backtrack (in actuality we just have all the paths in a list maybe?; grab the first working solution)

If we've backtracked all the way to the query node, then we fail? or just get more counterexamples to run it with

# Stengthening

Okay what's this crap that we're strengthening with?

Well, we take everything directly succ of the kvar in the graph and ask if the kvar implies it. If it does, we're done. If it doesn't we get a counter-example (TODO: get more than one), try some synthesis with our duderinos, and try again.

# Instrumenting

Inside of `Sol.solve`, where we call `solve_` is actually a pretty good place to do our business; we have both a `SolverInfo` and a `Result`, so we know what kvars to solve for, how to get `cSucc` boiz, and where we're starting from. It's even in the IO monad directly already, so we won't have to do too much fucking with shit.

# Writing some code

Let's start with the damn simple `bool00.fq` and see if we can ``synthesize'' the simple *conjuntive* invariant before we get all fancy with condition abduction 'n' shiz.

> Wait, that's sort of dumb... we're already going to have a conjuctive solution coming in. Throw it away? Let's throw it away.

No, that still doesn't work. Let's pretend that constraint `[3]` is the failing one for now. We can actually force it to do that by *actually* failing (by commenting out the quals), and thereby test all the code leading up to the actual synthesis before that. Then, when we have that working, we can comment out the code that figures out what cons to start on and the old sol, hardcode it, and write synthesis on the conjuctive boi.

TODO: this won't (at all) test the path where the code extracts solutions.

# Getting the fools from the data structure

        sucs = cSucc (siDeps sI)
        kprevs = cPrev (siDeps sI)

the `sucs` are straightforward, but they're actually the opposite of what we need. The prevs, unlike the sucs are actually read-from kvars, not cids. (WHY?) This is going to be work :(

        cons = case F.resStatus res of
          F.Crash{} -> error "CRASH"
          F.Safe -> error "ALREADY SAFE"
          F.Unsafe xs -> fst <$> xs

On the other hand, extracting the failing constraints is straightforward.

    prevs = mfromJust (error "NO CONSID") <$>
     (map (F.sid . snd) . M.toList . flip M.filter (F.cm fi) . writes
      =<< mfromJust stupidError . flip M.lookup kprevs
      =<< cons)
    writes x c = x `elem` V.kvars (F.crhs c)

So we extract the predecessor information we need from taking the kvars read from in the constraint. we're going to need this again SOON, so I'll generalize it over cons in just a sec.

# Getting the counterexamples from z3

Well, there are three bits here: making the query, actually passing it off to z3, and then reading it in. We should be able to build the query by applying the solution to the `sucs`s and then compiling the constraint. Passing off to z3... well, let's hope those hacks that we spent all of October fighting z3 for work now. At least for reading it in we can reuse some of the code from my Masters' thesis.

### Building the query

How do we apply a FixSolution? Something like `mapKvars (flip M.lookup sol)`

Oh, but we don't just need *a* constraint; we need all of the constraints that this one writes to! So instead of prev constraints I should've built up a bunch of failing KVars.

        failingKVars = mfromJust stupidError . flip M.lookup kprevs =<< cons

Okay, that wasn't so bad!

    synthesisProject fi sI res = do
      print cons
      print kprevs
      print failingKVars
      foldrM (synthKVar fi sI) res failingKVars
      where cons = case F.resStatus res of
              F.Crash{} -> error "CRASH SYNTH!!"
              F.Safe -> error "LOL ALRDY SAFE!!!"
              F.Unsafe xs -> fst <$> xs
            kprevs = cPrev (siDeps sI)
            failingKVars = mfromJust stupidError . flip M.lookup kprevs =<< cons

    synthKVar fi _sI k res = do
      putStrLn $ "\x1b[32m" ++ "SYNTH BABY SYNTH " ++ show k ++ "\x1b[0m"
      print sol
      print prevs
      print k
      return res
      where prevs = mfromJust (error "NO CONSID") <$>
               (map (F.sid . snd) . M.toList .
               flip M.filter (F.cm fi) $
               writes k)
            writes x c = x `elem` V.kvars (F.crhs c)
            sol = F.resSolution res

Avoid the temptation to use res and rés as variable names.

Oh boy, that stupidError should've been a catMaybes. And while we're at it, we should have previous kvars if we really do want to recurse. And while we're recursing we should not go into an infinite loop, so we need to keep track of visited.


```
synthKVar cfg fi sI k0 res = synthKVar' cfg fi sI (S.singleton k0) k0 res

synthKVar' cfg fi sI ks k0 res = do
  putStrLn $ "\x1b[32m" ++ "SYNTH BABY SYNTH " ++ show k0 ++ "\x1b[0m"
  res' <- foldrM (synthKVar' cfg fi sI ks') res reck
  return res'
  where prevkvars = join $ catMaybes $ flip M.lookup kprevs <$> prevs
        sol = F.resSolution res
        ks' = S.insert k0 ks
        reck = S.difference (S.fromList prevkvars) ks'
  
        kprevs = cPrev (siDeps sI)
        prevs = mfromJust (error "NO CONSID") <$>
           (map (F.sid . snd) . M.toList .
           flip M.filter (F.cm fi) $ -- Should probably cache this
           writes k0)
        writes x c = x `elem` Vis.kvars (F.crhs c)
```

Praise be to the worst implementation of dfs I've ever seen, that took me two days to write!

Now we should test this recursion scheme on some test with more cyclic shit to make sure it's terminating

```
bind 0 a  : {v: int  | $k0}
bind 1 tt : {v: bool | v}
bind 2 b  : {v: int  | b == 3}

constraint:
  env [ ]
  lhs {v : int | v = 10}
  rhs {v : int | $k0}
  id 1 tag []

constraint:
  env [ ]
  lhs {v : int | v = 20}
  rhs {v : int | $k0}
  id 2 tag []

constraint:
  env [ 0 ]
  lhs {v : int | v = a}
  rhs {v : int | 10 <= v}
  id 3 tag []

constraint:
  env [ ]
  lhs {v : int | $k1}
  rhs {v : int | $k0}
  id 4 tag []

constraint:
  env [ ]
  lhs {v : int | $k0}
  rhs {v : int | $k1}
  id 5 tag []

constraint:
  env [ ]
  lhs {v : int | v<4}
  rhs {v : int | $k1}
  id 6 tag []

wf:
  env [ ]
  reft {v: int | $k0}

wf:
  env [ ]
  reft {v: int | $k1}
```

Then we should just have it pop shit in qual to emulate the Rondon et algorithm (easy, right? :P)

### Enumerative Search

Well, we probably want to reuse the worklist from Rondon et al, but we still need to reimplement the whole EUSolver algorithm. Among other things, that means running the fucking semantics, which we can maybe just use instantiate's eval for in a pinch, but that'll be extremely slow, so at some point we're going to have to write an interpreter for smt2lib lisp.

The whole EUSolver algorithm is pretty complex, so let's start by just implementing enumerative search, as show in in algorithm 1 of the paper.

```
Algorithm 1
Enumerative Solver
Require: Grammar G = 〈N ,S, R〉
Require: Specification Φ
Ensure: e s.t. e ∈ [[ G ]] ∧ e | = Φ
1: pts ← emp
2: while true do
3:   for e ∈ enumerate ( G, pts) do
4:   if e |/= Φ|pts then continue
5:   cexpt ← verify (e,Φ)
6:   if cexpt = ⊥ then return e
7:   pts ← pts ∪ cexpt
```

We should grab the enumerated list from Language.Fixpoint.Solver.Solution.init

We need to change our code to operate on Solutions, not Results!

```
solve_ cfg fi s0 ks cD wkl = do
  let s1  = mappend s0 $ {-# SCC "sol-init" #-} S.init cfg fi ks
  s       <-  refine s1 wkl
  res     <-  result cfg wkl s
  lift$putStrLn$"\x1b[32m"++"LESSA-GO-GO"++"\x1b[0m"
  (_,s')<- Q.synthesisProject cfg fi cD res s ([],s1)
  st      <- stats
  res     <-  result cfg wkl s'
  let res' =  tidyResult res
  return $!! (res', st)
```

Now we need to check each conjunct against the points.


OH FUCK ME WE'RE TRAVERSING IN THE GFP DIRECTION, NOT THE LFP DIRECTION. FUCK ME FUCK ME FUCK ME.

.... okay starting over.

We need to iterate on constraints, not kvars!!!!

# A Fresh Start

Okay, so we fucked up. Not bad, we can start over. That's what grad school is for, right? Eternally writing and rewriting code? Well, I'm actually sort of starting to enjoy this now, so it's not so bad, but I wish I didn't make so many mistakes.

Alright so our problem was that we didn't consider the possibility that each SimpC could have multiple KVars on the lhs.So our "build a graph of KVars and bfs it" strategy isn't going to work. Instead we have to traverse the constraint graph constraint-by-constraint, in lfp order, just like the algorithm of Rondon et al does.

> So we could start by CEGIS-ifying their search?

Maybe. Ultimately we're going to have to add

1. Condition Adbuction
2. Backtracking

So when we exhaustively search conditionals for a solution, and still don't find one, that just means we have to give ourselves a bigger support (ie, strengthen the solution to the last fella), right?

> Wait, can that ever even help?

Hmm, perhaps not... Well, the idea is that we eventually hit a ConcC, and at that point, we can CA the kvars leading into it until we find something, and we backtrack and CA the ones before it.

> That seems reasonable, but I'm not sure there's an upgrade path from Rondon et al's recursion scheme to one that backtracks.

I wouldn't be so hasty! Since in haskell pretty much all iteration happen by recursion, we just add stuff to after the recursive call. This will be a problem when they have things like folds and filters, but we can unwrap them, and do our thing inside them.

So let's GOGOGO

# Adding CEGIS to Rondon et al

Okay so the solving code here is actually pretty (unnecessarily) complex. So let's start by just inserting print statements. The basic idea is that they generate an initial solution that's the bottom of the lattice, and then they work upwards to get to a fixpoint solution. In code, they start with a `Solution`, and then `refine` it by going through the `wkl` worklist.

So what we should do is hang out inside this `refine` fella, and maybe add a monad (or a record in some monad) to keep track of the counterexamples (call 'em `pts`) thus far. Then we check that the constraint is satisfied for each counter example before asking the SMT solver to do their biz.

> Alright you've made it pretty far into this bullshit stream of conciousness text file. I hope Future Anish isn't going to try to pass this off as documentation. Fuck that guy. Anyhow, here's a [politically charged meme](https://www.facebook.com/ShitBootlickersSay/photos/a.816217618461246.1073741828.816213195128355/1594993447250322/?type=3) for your efforts.

Alright that was mildly inappropriate for this sort of document, but I'll go with it.

Anyhow the `refine` function is a bitchass motherfucker.
To be clear, I mean the one in Solve.hs. Call us `refine` for we are many.

The actual refining happens in a function called `refineC`, which returns a bool that tell us if we should add this constraint back to the worklist, and a new Solution (all wrapped inside the `SolveM` monad). It does its business by calling this `filterValid` fellow, which just does the deed and also inside the SolveM Monad.

This seems to make a good case for adding the list of counterexamples as a bit of SolverState. I still want a way to keep track of the inital solution (and the hittīng-sets sort of deal with each of the EQuals), but we can add that after we CEGIS-ify.

## The new SolverState

```
{-# LANGUAGE ExplicitForAll    #-}
{-# LANGUAGE RankNTypes        #-}
type CntrExs = forall a. [a]

data SolverState = SS { ssCtx     :: !Context      
                      , ssBinds   :: !F.SolEnv     
                      , ssStats   :: !Stats        
                      , ssPts     :: !CntrExs      
                      }
```

> Woah, it turns out there's acutally a better way to do this
>
> ```
> type CntrEx = GHC.Prim.Anu
> ```

Uhhh, fix this later, I have no idea what type the counterexamples are going to be. We'll figure it out after we read them in from Z3, I guess. Def fix this before actually committing anything.

Okay let's read those motherfuckers in!

## Reading in counterexamples

```
filterValid :: F.SrcSpan -> F.Expr -> F.Cand a -> SolveM [a]
filterValid sp p qs = do
  qs' <- withContext $ \me ->
           smtBracket me "filterValidLHS" $
             filterValid_ sp p qs me
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  return qs'

filterValid_ :: F.SrcSpan -> F.Expr -> F.Cand a -> Context -> IO [a]
filterValid_ sp p qs me = catMaybes <$> do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracketAt sp me "filterValidRHS" $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ if valid then Just x else Nothing

```

This boi seems ready for some CEGIS action! We should replace the `Maybe a` with `Either a CounterExample`... after we figure out what the fuck the counterexample type is.

Until then, we should just see if we can add onto smtCheckUnsat to grab the model while we're at it!

Okay, I think I got all the parse stuff right, (good thing I still had it laying around from my Master's Thesis hahahhaha...). But I want to compose parsers in a way that I'm unsure about.

```
pairP :: SmtParser (Symbol, Expr)
pairP = {-# SCC "pairP" #-}
  do A.skipSpace
     A.char '('
     !x <- symbolP
     A.skipSpace
     !v <- (valueP >>= lispP)
     A.char ')'
     return (x,v)
```

Parser is a monad, so there should be a way to do this thing, right? I'm just going to say fuck it and git rid of the ValuesP. We can rewrite Target to take real Exprs when the time comes, if need be.

Alright now for filterValid. I don't need it to actually return the counterexamples, just add them to the SolveM Monad. (under a flag, I guess)

```
filterValid :: F.SrcSpan -> F.Expr -> F.Cand a -> SolveM [a]
filterValid sp p qs = do
  qs' <- withContext $ \me ->
           smtBracket me "filterValidLHS" $
             filterValid_ sp p qs me
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  ss <- get
  put (ss { ssPts = (snd <$> qs') ++ ssPts ss })
  return (fst <$> qs')

filterValid_ :: F.SrcSpan -> F.Expr -> F.Cand a -> Context -> IO [(a, CntrEx)]
filterValid_ sp p qs me = catMaybes <$> do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracketAt sp me "filterValidRHS" $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ if valid then Just (x,undefined) else Nothing
```


BAH. If I want to getValues, I have to pass around the values that I need and think ahead. I could go and change the whole thing now to just use getModel, but that would mean a performance hit, and I'd have to write a whole bunch of code єither way. It *is* more complex to write the code to figure out and keep what xs I need AND it means that I need a new filterValid specifically for synthesis, but I'm afraid of spending all <s>day</s> night rewriting the SMT interface.

So here goes.

Split into a new codepath called filterValidCEGIS, and all tests passing! so that's a good sign.

Now let's actually start reading in these motherfucking counterexamples from Z3.

```
filterValidCEGIS_ :: F.SrcSpan -> F.Expr -> F.Cand a -> Context -> IO ([a],[CntrEx])
filterValidCEGIS_ sp p qs me = partitionEithers <$> do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracketAt sp me "filterValidRHS" $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      if valid
        then return $ Left x
        else Right <$> smtGetValues me undefined
```

Alright we resolved `CtnrEx = [(Symbol,Expr)]`!! But this still  means that we have to pass around the symbols that we want to get the values for in the counterexample.

Uhm, we actually need all the vålues in the environment if we're going to evaluate the expression ANYWAYS. So we could've totally done getModel instead of getValues. But I just remembered that the soverstate keeps track of the bindenv, so maybe we can just use those? They probably have things that aren't in Z3's model so it'll throw an error. We can ask rise4fun if that's kosh.

Okay, after playing around with the Z3 webapp it looks like we're fine as long as it's declared

Oh boy we're having some parser trouble. Let's hope we don't have to revisit that stuff where ## was getting read in as some encoding into acsii

Okay we had it do it, but it wasn't so bad

```
decode :: T.Text -> T.Text
decode s = T.concat $ zipWith ($) (cycle [id, T.singleton . chr . fst . fromRight . decimal]) (T.split (=='$') s)
```

Yeah, it looks like reading them in is going to be very slow because we can't not just read in everything in the env and that's a TON of stuff for constraints actually generated by LH.

## Evaluating the Counterexamples

This is actually not as bad as I thought іt would be because we don't have any uninterpreted functions in the values we read in. We may well have some in the constraint, though, and I'm not sure what to do about that.

OH HELL. I'm going to have to read in functions, won't I?
Fuck me with a chainsaw, get-value doesn't even tell me about functions. So I'm actually going to have to go through all the effort to use getModel instead, the moment I have uninterpreted functions.

Well, I think I might be able to avoid that using defunctionalization, but then I still can't fucking run the semantics without getting z3 to spit out the Gődel encoding it used.

Okay, let's soldier on and see if we get fucked by this. If not, everything will work just fine and dandy, right? It hasn't failed any testcases, and it would've done that by now if we were fucked on them. Let's run the bigger tests found in lh. Those will come back in an hour.

Meanwhile, let's start slapping down some code to evaluate the counterexamples.

Well, the liquidhaskell tests came back and I broke Target, so I can't run it. I guess we should unbreak it later (maybe for now just throw an undefined in the right place)

Alright, I now have a function that typechecks that should evaluate the expressions we get from lisp. So in order to make our simple enumerative search into CEGIS, we need to run these counterexamples. This means that inside filterValidCEGIS_ we need to have a bit that's checks the felas against our counterexamples before it checks them against z3.

Haha if I just try to evaluate the whole thing and crash whenever I see something strange, I only break half the tests!

```
filterValidCEGIS_ :: [F.Symbol] -> F.SrcSpan -> F.Expr -> F.Cand a -> Context -> IO ([a],[CntrEx])
filterValidCEGIS_ xs sp p qs me = partitionEithers <$> do
  smtAssert me p
  forM (filter ((<= p') . fromLeft . eval . fst) qs) $ \(q, x) ->
    smtBracketAt sp me "filterValidRHS" $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      if valid
        then return $ Left x
        else Right . traceShowId <$> smtGetValues me xs
    where Left p' = eval p
          fromLeft (Left a) = a
          fromLeft (Right _) = error "fromLeft"
```

Alright, we need to split that into a function:

```
filterStaticCEGIS pts p qs = foldr filterOne qs pts
  where filterOne pt = filter $ (<= (fromLeft $ eval $ ev pt p)) .
                                     fromLeft . eval . ev pt . fst

```
ooh, pretty! Here ev does evaluation at a point.

So it runs, and doesn't crash.... but still somehow causes some tests to fail. Need to debug it...

# Debugging CEGIS

Okay I fixed a few cases, include that Op takes Nums as args, but I was right to worry about uninterpreted functions --- they do appear everywhere! I'm just surprised I didn't already crash on them, but I guess the deal іs that we don't ever read in an uninterpreted function, so that was fine, but now that we're evaluating everything, I don't know what to do.

This is the reason that the following regression tests are crashing:
- MergeSort.fq
- test00.hs.fq
- listqual.hs.fq
- elim00.hs.fq

wl00.fq & test2.fq are failing with Unsafe! We did something unsound, oops!

Looks like we'll have to borrow reflection code from Instantiate to figure out how to run those functions?

Woah, this should actually be an interesting (paper-worthy?) contribution itself! I should talk to nadia about it. I'll call it "Speeding up Horn Constraint Solving with Logical Normalization"


## `get-value` vs `get-model`

SMT's `get-value` command won't actually give us values for function types. To do this we need to use `get-model`. It's not clear how much these will help --- in the worst case CEGIS with this sort of thing become adversarial (See paper that Nadia sent us). Worse still, SMT solvers don't really support curried/higher-order functions, so the examples for those we get out will very very likley be useless.

We could use PLE. It would be expensive, but maybe worth it? A cool thing to include in our paper would be a comparison of PLE with just throwing them out, vs getting counterexamples, vs doing whatever (ICE?) thing that the papers Nadia sent us do.

Which reminds me, we should really read the VS3 paper to figure out what they're doing and how we're different from them.

Alright, I made the obvious things go through, without adding anything new to the parser, and it compiles, but for some reason it doesn't break *every* test. I have no fucking clue why. I guess in a lot of these tests we just never call CEGIS?

we have this error: 
```
fixpoint: src/Language/Fixpoint/Smt/Interface.hs:566:19-33: Non-exhaustive patterns in lambda
```

Which happens when we destructure inside smtGetModel. Let's fix it:

```haskell
sexpP :: SmtParser Response
sexpP = {-# SCC "sexpP" #-} A.string "error" *> (Error <$> errorP)
     <|> Values <$> valuesP
     <|> Model <$> modelP
```

Oh fuck that. We're going to parse it as an sexp and then decide if it's a model or a set of values based on the value of the first field.

This does mean that we should ask Eric to see if there are Target tests to make sure we don't break them!

```
sexpP :: SmtParser Response
sexpP = {-# SCC "sexpP" #-} A.string "(error" *> (Error <$> errorP)
     <|> modelOrValues <$> predP

modelOrValues (Lisp ((Sym s):ls))
  | symbolText s == "model" = toModel ls
modelOrValues (Lisp ls) = Values $ pairLisp <$> ls
modelOrValues (Sym s) = error $ "unknown symbol when expecting Model or Values" ++ show s

pairLisp :: Lisp -> (Symbol, T.Text)
pairLisp (Lisp [Sym sym, Sym val]) = (sym, symbolText val)
pairLisp l = error $ "expected pair of (sym,val); found " ++ show l

toModel ls = Model $ defineLisp <$> ls

defineLisp (Lisp [_,Sym sym,_,_,expr]) = (sym, parseLisp expr)
defineLisp l = error $ "Expecting Lisp Define-fun, Got " ++ show l
```

Okay, that wasn't so bad. We should still make sure we don't break Target with this. Ah, balls, we forgot to read in the formals, so we still don't work with EApp. On top of that, there are a number of test cases where we're not reading in all the `EVar`s that we get with get-values.

Here's our status.

The following fail because of eliminate/quantifiers

      listqual.hs.fq:         FAIL (0.12s)
      wl00.fq:                FAIL (0.02s)
      test2.fq:               FAIL (0.02s)

The following fail due to some EApps not being read in by get-model

      listqual.hs.fq:         FAIL (0.10s)
      wl00.fq:                FAIL (0.02s)
      test00.fq:              FAIL (0.01s)
      test00.hs.fq:           FAIL (0.06s)
      test2.fq:               FAIL (0.01s)
      MergeSort.fq:           FAIL (0.50s)
      test000.hs.fq:          FAIL (0.07s)
      elim00.fq:              FAIL (0.10s)
      bad-subst01.fq:         FAIL (0.01s)
      listqual.hs.fq:         FAIL (0.11s)
      wl00.fq:                FAIL (0.02s)
      test2.fq:               FAIL (0.02s)
      MergeSort.fq:           FAIL (0.44s)

The following fail with that, and EApp turned on

      listqual.hs.fq:         FAIL (0.10s)
      wl00.fq:                FAIL (0.02s)
      test00.fq:              FAIL (0.01s)
      test00.hs.fq:           FAIL (0.06s)
      test2.fq:               FAIL (0.01s)
      MergeSort.fq:           FAIL (0.45s)
      test000.hs.fq:          FAIL (0.07s)
      elim00.fq:              FAIL (0.09s)
      bad-subst01.fq:         FAIL (0.01s)
      listqual.hs.fq:         FAIL (0.10s)
      wl00.fq:                FAIL (0.02s)
      test2.fq:               FAIL (0.02s)
      MergeSort.fq:           FAIL (0.45s)

Okay let's tackle each of these one-by-one

### EApps not being read in correctly

We trace as follows:

```haskell
decode :: T.Text -> T.Text
decode s = Misc.traceShow "decode" $ T.concat $ zipWith ($) (cycle [id, T.singleton . chr . fst . fromRight . decimal]) (T.split (=='$') (Misc.traceShow "encode" s))
```

which gives us:

```
Trace: [encode] : "GHC.Types.EQ$36$35$36$6U"
Trace: [decode] : "GHC.Types.EQ$35$6U"
Trace: [encode] : "GHC.Types.LT$36$35$36$6S"
Trace: [decode] : "GHC.Types.LT$35$6S"
Trace: [encode] : "GHC.Types.GT$36$35$36$6W"
Trace: [decode] : "GHC.Types.GT$35$6W"
Trace: [encode] : "VV$36$35$36$424"
Trace: [decode] : "VV$35$424"
```

So when we're reading things back from z3, for some reason we're encoding/decoding the wrong number of times `$35$ -> $36$35$36$ -> $35$`.

Now Anish spends a while debugging a z3 segfault before shravan points out that he should try upgrading z3
