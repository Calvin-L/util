(*

For more on matching, see
  http://adam.chlipala.net/cpdt/html/Cpdt.MoreDep.html

*)

(* ========================================================================= *)
(* ADVANCED MATCHING *)

(*
In Coq, the general form of `match` is:

  match TERM1
  as x0
  in (TYPE x1 x2 ...)
  return TERM2
  with
  | PATTERN => TERM3
  ...
  end

where x0, x1, ... are names that get bound.

Usually you can omit the `as`, `in`, and `return` clauses.  Here's a quick
rundown of why you might want to use each one, starting with `return`:

  - `return` says what you expect the match to return.  It is useful when the
    return type depends on what case is matched---in which case Coq usually
    can't infer the correct return type.

    It is the most important auxiliary clause; `as` and `in` (described below)
    just exist to help with `return`.
*)

Definition return_example (b : bool) :=
  match b
  return (if b then nat else bool)
  with
  | true =>
    (* return type of this branch is `if true then nat else bool`, which is
     * definitionally the same as `nat` *)
    0
  | false =>
    (* return type of this branch is `if false then nat else bool`, which is
     * definitionally the same as `bool` *)
    true
  end.

Check return_example. (* forall b : bool, if b then nat else bool *)

(*
  - `as` gives a name to TERM1 that you can use in the return clause.  If TERM1
    is an identifier then this is pointless---but if TERM1 is complex then it
    might be convenient to give it a short name.
*)
Require Import Bool.
Definition as_example :=
  match (true && false || true)
  as b
  return (if b then nat else bool)
  with
  | true  => 0
  | false => true
  end.
Check as_example. (* if true && false || true then nat else bool *)

(*

To demonstrate `in` we will want a more interesting dependent type (`Dep`):

*)

Inductive AB : Set := A | B.

Inductive Dep : AB -> Set :=
  | IsA : Dep A
  | IsB : Dep B
  .

(*
  - `in` lets you name the arguments of the (potentially dependent) type of
    TERM1.  This is useful if you are matching on a dependent type and you need
    the return type to depend on the type's arguments.
*)
Axiom fizzbuzz : nat -> AB.
Definition in_example (x : nat) (y : Dep (fizzbuzz x)) :=
  match y
  in Dep arg (* `arg` is a fresh name that will be bound to the type argument *)
  return (
    (* the return type can depend on `arg` *)
    match arg with
    | A => nat
    | B => bool
    end)
  with
  | IsA =>
    (* The type of the pattern `IsA` is `Dep A`.
     * So, in this branch arg = `A` and the return type is
     *     match A with
     *     | A => nat
     *     | B => bool
     *     end
     * which is definitionally equal to `nat`.
     *)
    0
  | IsB =>
    (* The type of the pattern `IsB` is `Dep B`.
     * So, in this branch arg = `B` and the return type is
     *     match B with
     *     | A => nat
     *     | B => bool
     *     end
     * which is definitionally equal to `bool`.
     *)
    false
  end.
Check in_example. (* forall x : nat,
                       Dep (fizzbuzz x) ->
                          match (fizzbuzz x) with
                          | A => nat
                          | B => bool
                          end *)


(* ========================================================================= *)
(* CAVEAT #1: REFINING FREE VARIABLES *)

(* helper definition *)
Definition denote (x : AB) : Type :=
  match x with
  | A => nat
  | B => bool
  end.

(*
 * Matching on y, Coq is smart enough to refine the return type for us.
 *)
Definition f (x : AB) (y : Dep x) : denote x :=
  match y with
  | IsA => 1
  | IsB => false
  end.

(*
 * However, Coq is not smart enough to refine the type of `x`: it only refines
 * the return type!  From CPDT:
 *  > there is no way to specify that the types of certain free variables
 *  > should be refined based on which pattern has matched.
 * So, while this definition looks philosophically right, Coq will not accept
 * it:
 *)
Fail Definition f (x : AB) (y : Dep x) : denote x :=
  match y with
  | IsA =>
    match x with
    | A => 1
    (* I shouldn't have to provide a B case here---if y is `IsA` then x can
     * only be `A`, and there are no other possibilities.  But, Coq won't
     * deduce that. *)
    end
  | IsB => false
  end.

(*
 * However, by moving the `y` argument INSIDE the match, it does work.  This is
 * the only way I know of to have the match on `x` refine the type of `y`, or
 * vice-versa.
 *
 * Note that this may require swizzling the order of matches; here we match
 * first on `x` and then on `y`.  Doing it the other way around is possible but
 * trickier; it usually involves exploiting an equality proof, which is messy.
 *)
Definition h (x : AB) (y : Dep x) : denote x :=
  (match x return (Dep x -> denote x) with
  | A => fun z =>
    match z with
    | IsA => 1
    (* IsB is an "impossible" branch, so we can omit it! *)
    end
  | B => fun _ => false
  end) y.


(* ========================================================================= *)
(* CAVEAT #2: INDEXES VS PARAMETERS *)

(*
 * Recall the standard definition of equality from Coq.Init.Logic:
 *
 *     Inductive eq (A:Type) (x:A) : A -> Prop :=
 *       | eq_refl: @eq A x x.
 *
 * That definition is interesting because it contains two "parameters" (`A` and
 * `x`) and one "argument" (the anonymous second argument of type `A`).  When
 * matching on a value of type `eq ...`, only the arguments can be named using
 * the `in` clause, not the parameters.
 *
 * This makes sense because the parameters do not vary based on what
 * constructor was used; they will be the same in every match branch, so naming
 * them would be pointless.
 *
 * This is how you might exploit an equality proof (i.e. a value of type `eq`):
 *)
Definition i1 (x : nat) (y : 0 = x) : fizzbuzz 0 = fizzbuzz x :=
  match y in @eq _ _ x2 return (fizzbuzz 0 = fizzbuzz x2) with
  (*             ^ ^ ^^
   *             | | |
   *             | | First (and only) argument
   *             | Second parameter, always `0`
   *             First parameter, always `nat`
   *)
  | @eq_refl _ _ =>
    (*
     * The type of the pattern is (@eq nat 0 0).
     * Therefore, this branch should return `fizzbuzz 0 = fizzbuzz 0`
     *)
    @eq_refl _ (fizzbuzz 0)
  end.

(*
 * Of course, `i1` only works because the argument depends on the parameter
 * and the parameter is a constructor.
 *
 * Exploiting an equality proof that goes the other direction---where the
 * parameter is a more complicated term or even just a variable---is a little
 * harder.  You might expect this to work (just flip the direction of the = and
 * all occurrences of `x` and `0`):
 *)
Fail Definition i2 (x : nat) (y : x = 0) : fizzbuzz x = fizzbuzz 0 :=
  match y in @eq _ _ x2 return (fizzbuzz x2 = fizzbuzz 0) with
  | @eq_refl _ _ =>
    @eq_refl _ (fizzbuzz x)
  end.

(*
 * The problem is that information "flows" from the parameter to the argument.
 * So when we define our return clause, it has to be in terms of the parameter
 * (`x`) and the argument (`0`, renamed to `x2` by the in-clause).
 *)
Definition i2 (x : nat) (y : x = 0) : fizzbuzz x = fizzbuzz 0 :=
  match y in @eq _ _ x2 return (fizzbuzz x = fizzbuzz x2) with
  | @eq_refl _ _ =>
    (*
     * The type of the pattern is (@eq nat x x).
     * Therefore, this branch should return `fizzbuzz x = fizzbuzz x`
     *)
    @eq_refl _ (fizzbuzz x)
  end.


(* ========================================================================= *)
(* CAVEAT #3: MATCHING PROPS TO RETURN SETS *)

(*
 * Usually Coq does not allow you to to destruct a Prop to obtain a Set value:
 *)
Fail Definition or_to_bool {P Q} (pf : P \/ Q) : bool :=
  match pf with
  | or_introl _ => true
  | or_intror _ => false
  end.

(*
 * However, Coq DOES allow that behavior when the Prop is "uninformative".
 * A Prop with one constructur is considered uninformative:
 *)
Inductive UninformativeProp : AB -> Prop :=
  | IsA'' : UninformativeProp A.

Definition uninformative_to_bool1 (y : UninformativeProp A) : bool :=
  match y with
  | IsA'' => true
  end.

Definition uninformative_to_bool2 (x y : nat) (y : x = y) : bool :=
  match y with
  | @eq_refl _ _ => true
  end.

(*
 * Interestingly, this one-constructor case does NOT work even if you can
 * construct a term that reduces the number of possible branches to one:
 *)

Inductive DepProp : AB -> Prop :=
  | IsA' : DepProp A
  | IsB' : DepProp B
  .

(*
 * Even though we can reduce the number of possible branches to 1, Coq still
 * won't let us destruct a Prop to construct a Set.
 *)
Fail Definition uninformative_to_bool3 (x : AB) (y : DepProp x) : denote x :=
  (match x return (DepProp x -> denote x) with
  | A => fun z =>
    match z with (* <=== Shouldn't this work? `z` sure looks uninformative to me... *)
    | IsA' => 1
    (* IsB is an "impossible" branch, so we can omit it! *)
    end
  | B => fun _ => false
  end) y.


(* ========================================================================= *)
(* OTHER CAVEATS AND GOTCHAS *)

(*
 * Wow! Very obscure problem.  Consider:

Definition jbad (y : DepProp A) : True :=
  match y with
  | IsA' => I
  end.

 * It fails!  See accepted answer here:
 * https://stackoverflow.com/questions/45035891/how-to-pattern-match-on-a-prop-when-proving-in-coq-without-elimination-on-type
 * Coq has incorrectly desugared the match:

Definition jbad_1 (y : DepProp A) : True :=
  match y in DepProp A with
  | IsA' => I
  end.

Definition jbad_2 (y : DepProp A) : True :=
  match y in DepProp _a (match _a return Type with
    | A => True
    | _ => IDProp
    end) with
  | IsA' => I
  end.

 * But we can fix the problem by using that desugared form with s/Type/Prop/.

*)

Definition jgood (y : DepProp A) : True :=
  match y in DepProp _a return (match _a return Prop with
    | A => True
    | B => IDProp
    end) with
  | IsA' => I
  | IsB' => idProp
  end.

(*Set Printing all.*)
Print jgood.
