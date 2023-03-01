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

\* Silly helper definition.  Used in "fib_def" below.
Mention(op(_, _)) == TRUE

\* While TLAPS claims to support recursive functions, they can be really awkward!
\* This seemingly-obvious fact is quite difficult to prove.
THEOREM fib_def == \A n \in Nat: fib[n] = (IF n <= 1 THEN 1 ELSE fib[n-1] + fib[n-2])
  \* First, we define an "unfixed" version of the function.  This is a non-recursive
  \* definition such that `fib = [x \in Nat |-> fib_unfixed(fib, x)]`.
  <1> DEFINE fib_unfixed(f, n) == IF n <= 1 THEN 1 ELSE f[n-1] + f[n-2]

  \* In fact, if we can prove the relationship between fib and fib_unfixed, the
  \* backends have no problem establishing our goal.  This relationship enables the
  \* backends to "unfold" fib for evalution by rewriting
  \*   fib[n] = fib_unfixed(fib, n)
  \*          = IF n <= 1 THEN 1 ELSE fib[n-1] + fib[n-2]
  <1> SUFFICES fib = [n \in Nat |-> fib_unfixed(fib, n)] OBVIOUS

  \* Our goal is to apply the builtin theorem "RecursiveFcnOfNat" which states:
  \*
  \*   ASSUME NEW Def(_,_),
  \*          ASSUME NEW n \in Nat, NEW g, NEW h,
  \*                 \A i \in 0..(n-1) : g[i] = h[i]
  \*          PROVE  Def(g, n) = Def(h, n)
  \*   PROVE  LET f[n \in Nat] == Def(f, n)
  \*          IN  f = [n \in Nat |-> Def(f, n)]
  \*
  \* Notice that, after let-inlining, our goal is close to the conclusion of the
  \* RecursiveFcnOfNat theorem with "Def" replaced by "fib_unfixed".  So, we need
  \* to prove the "well-foundedness" hypothesis required by RecursiveFcnOfNat:
  <1>a. ASSUME
          NEW i \in Nat,
          NEW g,
          NEW h,
          \A j \in 0..(i-1) : g[j] = h[j]
        PROVE
          fib_unfixed(g, i) = fib_unfixed(h, i)
        BY <1>a

  \* Defining fib_fixed makes our goal *exactly* the conclusion of RecursiveFcnOfNat.
  \* This step feels a little silly---the backends have no trouble showing that
  \* "fib_fixed = fib"---but without this step the backends will not correctly
  \* instantiate RecursiveFcnOfNat.
  <1> DEFINE fib_fixed[i \in Nat] == fib_unfixed(fib_fixed, i)
  <1> SUFFICES fib_fixed = [n \in Nat |-> fib_unfixed(fib_fixed, n)] BY DEF fib

  \* Unfortunately, we now need to do a lot of footwork to convince the backends
  \* to apply RecursiveFcnOfNat correctly.  Here are the key points:
  \*   - The statement of RecursiveFcnOfNat uses a binary operator "Def"
  \*   - We want "fib_unfixed" to be used in place of "Def"
  \*   - We need to hide the definition of "fib_unfixed" to have any hope of
  \*     instantiating RecursiveFcnOfNat with fib_unfixed in place of Def.
  \*   - In fact, we need to mention fib_unfixed as an argument to an operator
  \*     to convince the backends that they can use it to substitute a free
  \*     symbol in another theorem (i.e. Def in RecursiveFcnOfNat).  From what
  \*     I have read in the source code, the standard library proofs do this by
  \*     accident a lot of the time.  This tricky requirement can be met using
  \*     the no-op "Mention" operator defined above.
  <1> HIDE DEF fib_unfixed
  <1>b. ASSUME Mention(fib_unfixed) PROVE fib_fixed = [i \in Nat |-> fib_unfixed(fib_fixed, i)] BY <1>a, <1>b, RecursiveFcnOfNat
  <1> QED BY <1>b DEF Mention

THEOREM base1 == (fib[0] = 1)
  BY fib_def

THEOREM base2 == (fib[1] = 1)
  BY fib_def

LEMMA func_type == \A f, D, R: (DOMAIN f = D /\ \A x \in D: f[x] \in R) => f \in [D -> R]
  <1> TAKE f
  <1> TAKE D
  <1> TAKE R
  <1>1. SUFFICES ASSUME DOMAIN f = D, \A x \in D: f[x] \in R PROVE f \in [D -> R]
        OBVIOUS
  <1> QED

THEOREM fib_type == fib \in [Nat -> Nat]
  <1>1. DOMAIN fib = Nat
  <1>2. \A n \in Nat: fib[n] \in Nat
  <1> QED BY func_type, <1>1, <1>2

THEOREM fib_positive == \A x \in Nat: fib[x] > 0
  <1> DEFINE P(n) == fib[n] > 0
  <1>1. \A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
    <2> TAKE n \in Nat
    <2>0. SUFFICES ASSUME (\A m \in 0..(n-1) : P(m)) PROVE P(n) OBVIOUS
    <2>1. CASE n <= 1 BY <2>1, fib_def
    <2>2. CASE n > 1
       <3>1. fib[n-1] > 0 BY <2>0, <2>2
       <3>2. fib[n-2] > 0 BY <2>0, <2>2
       <3>3. fib[n] = fib[n-1] + fib[n-2] BY <2>2, fib_def
       <3> QED BY fib_type, <2>2, <3>1, <3>2, <3>3
    <2> QED BY <2>1, <2>2
  \* ASSUME...PROVE is generally easier for TLAPS than implication or quantification
  <1>2. ASSUME NEW n \in Nat PROVE (\A m \in 0..(n-1) : P(m)) => P(n) BY <1>1
  <1> HIDE DEF P \* necessary for unclear reasons
  <1>3. \A n \in Nat: P(n) BY <1>2, GeneralNatInduction
  <1> QED BY <1>3 DEF P

=======================
