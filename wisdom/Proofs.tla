---- MODULE Proofs ----

EXTENDS TLAPS, NaturalsInduction, Integers

\* I don't have cvc3, so I had to do some extra work.
\* In the toolbox settings, set the "solver" to
\*   /Users/cloncari/.nix-profile/bin/z3 "$file"
\* From the command line, pass
\*   --solver '/Users/cloncari/.nix-profile/bin/z3 "$file"'

fib[n \in Nat] == IF n <= 1 THEN 1 ELSE fib[n-1] + fib[n-2]

\* A proof for a GOAL is exactly one of:
\*  - OBVIOUS
\*  - BY [h1, h2, ...] [PTL] [DEF a, b, ...]
\*  - a sequence of STEPs ending in a QED step
\*
\* A sequence of steps has the form
\*    <N> STEP
\*    <N> STEP
\*    <N> QED [PROOF]
\*
\* The most basic kind of step is a simple assertion of some property:
\*   <N> Formula [PROOF]
\*
\* Usually you will want to give assertions names:
\*   <N>n. Formula [PROOF]
\*
\* Some useful steps:
\*  https://tla.msr-inria.inria.fr/tlaps/content/Documentation/Tutorial/Other_proof_constructs.html
\*  TAKE x [\in S] [, ...]
\*    -- used to prove universal formulas
\*    -- transforms the goal from "\A x [\in S]: P" to "x [\in S] |- P"
\*  WITNESS value [\in S] [, ...]
\*    -- used to prove existence formulas
\*    -- transforms a goal of the form \E x \in S: P(x) to the goal P(value)
\*  SUFFICES P [PROOF]
\*    -- proves that P |- GOAL by the given proof
\*    -- changes the goal to P
\*  DEFINE op(args) == body
\*    -- introduces a local definition
\*
\* Some useful constructs that might look like steps because they involve keywords, but are NOT
\* actually steps:
\*  ASSUME P1, P2, ... PROVE Q [PROOF]
\*    -- this is how you write the formula "P1, P2, ... |- Q"
\*    -- formulas do not nest; you cannot write "ASSUME ... PROVE (ASSUME ... PROVE P)"
\*    -- NOTE: frustratingly, to exploit the hypotheses P1, P2, etc. in proving Q, you usually need
\*       to do a proof "BY <NAME>" where <NAME> is the name of this ASSUME step.  I have no idea why.
\*       It seems to be unnecessary if it is an unnamed step.
\*  CASE P [PROOF]
\*    -- equivalent to ASSUME P PROVE G [PROOF] where G is the current goal
\*    -- NOTE: the same awful note about ASSUME applies here
\*
\* The monsterous TLA+ Hyperbook has a "proofs track" that is the best existing manual for TLAPS.
\* In particular, Section 12.3 "The State of a Proof" is enormously valuable.

THEOREM bar == TRUE
  <1> 0 < 1 OBVIOUS
  <1> ASSUME 0>1 PROVE FALSE OBVIOUS
  <1> QED BY DEF fib

THEOREM baz == \A b \in BOOLEAN: (b = TRUE) \/ (b = FALSE)
  OBVIOUS

THEOREM bazz == \A x \in Int: x < 0 \/ x >= 0
  OBVIOUS

THEOREM foo == \A x \in Nat: x = 0 \/ x = 1 \/ x > 1
  OBVIOUS

THEOREM assume_is_dumb == TRUE
  <1>1. ASSUME NEW x \in Nat, x = 0
      PROVE x = 0
      \* OBVIOUS \* doesn't work????
      BY <1>1
  <1> QED OBVIOUS

\* While TLAPS claims to support recursive functions, they can be really awkward!
\* This seemingly-obvious fact is quite difficult to prove.
THEOREM fib_def == \A n \in Nat: fib[n] = (IF n <= 1 THEN 1 ELSE fib[n-1] + fib[n-2])
  \* These intermediate definitions enable the backends to instantiate the higher-order
  \* theorem "RecursiveFcnOfNat" used below
  <1> DEFINE fib_unfixed(f, n) == IF n <= 1 THEN 1 ELSE f[n-1] + f[n-2]
  <1> DEFINE fib_unrolled[n \in Nat] == fib_unfixed(fib_unrolled, n)
  \* Our auxiliary definition is equal to the official one
  <1>1. fib = fib_unrolled BY DEF fib
  \* We need this lemma for "RecursiveFcnOfNat".  It says that the nth Fibonacci number
  \* only depends on smaller indexes.  This is to say that the Fibonacci function is
  \* "well-founded".
  <1>2. ASSUME NEW n \in Nat, NEW g, NEW h,
                \A i \in 0..(n-1) : g[i] = h[i]
         PROVE  fib_unfixed(g, n) = fib_unfixed(h, n)
         BY <1>2
  \* Using "RecursiveFcnOfNat" and our "well-founded" hypothesis, we can prove that it
  \* is legal to unfold the Fibonacci function once without changing the meaning.
  <1>3. fib_unrolled = [n \in Nat |-> fib_unfixed(fib_unrolled, n)]
    <2> HIDE DEF fib_unfixed \* necessary for unclear reasons
    <2> QED BY <1>2, RecursiveFcnOfNat
  \* Now, we can prove a relationship between the official definition and the definition
  \* we proved unfoldable in step <1>3.
  <1>4. \A n \in Nat: fib[n] = fib_unfixed(fib, n)
    <2> TAKE n \in Nat
    <2> QED BY <1>1, <1>3
  \* Finally, that relationship allows us to prove the overall goal.
  <1> QED BY <1>4

THEOREM base1 == (fib[0] = 1)
  BY fib_def

THEOREM base2 == (fib[1] = 1)
  BY fib_def

THEOREM fib_type == fib \in [Nat -> Nat]

THEOREM \A x \in Nat: fib[x] > 0
  <1> DEFINE P(n) == fib[n] > 0
  <1>1. \A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
    <2> TAKE n \in Nat
    <2>0. SUFFICES ASSUME (\A m \in 0..(n-1) : P(m)) PROVE P(n) OBVIOUS
    <2>1. CASE n <= 1 BY <2>1, fib_def
    <2>2. CASE n > 1
       <3>1. fib[n-1] > 0 BY <2>0, <2>2
       <3>2. fib[n-2] > 0 BY <2>0, <2>2
       <3>3. fib[n] = fib[n-1] + fib[n-2] BY <2>2, fib_def
       <3> QED BY fib_type, <3>1, <3>2, <3>3
    <2> QED BY <2>1, <2>2
  <1>2. \A n \in Nat: P(n)
    <2> HIDE DEF P \* necessary for unclear reasons
    <2> QED BY <1>1, GeneralNatInduction
  <1> QED BY <1>2

=======================
