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
