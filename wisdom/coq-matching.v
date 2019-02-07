(*

For more on matching, see
  http://adam.chlipala.net/cpdt/html/Cpdt.MoreDep.html

*)

Inductive AB : Set := A | B.

Inductive Dep : AB -> Set :=
  | IsA : Dep A
  | IsB : Dep B
  .

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

Definition f (x : AB) (y : Dep x) : denote x :=
  match y with
  | IsA =>
    match x with
    | A => 1
    end
  | IsB => false
  end.
*)

Definition g (x : AB) (y : A = x) : denote x :=
  match y with
  | eq_refl => 1
  end.

(*
 * Oops ! this definition does not work.  However, by moving the `y` argument
 * INSIDE the match, it does work.  This is the only way I know of to have the
 * match on `x` refine the type of `y`, or vice-versa.

Definition h (x : AB) (y : Dep x) : denote x :=
  match x with
  | A =>
    match y with
    | IsA => 1
    end
  | B => false
  end.
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

Inductive DepProp : AB -> Prop :=
  | IsA' : DepProp A
  | IsB' : DepProp B
  .

(*
 * Even though we can reduce the number of possible branches to 1, Coq still
 * won't let us destruct a Prop to construct a Set.

Definition h (x : AB) (y : DepProp x) : denote x :=
  (match x return (DepProp x -> denote x) with
  | A => fun z =>
    match z with
    | IsA' => 1
    (* IsB is an "impossible" branch, so we can omit it! *)
    end
  | B => fun _ => false
  end) y.
*)

Inductive OtherProp : AB -> Prop :=
  | IsA'' : OtherProp A.

Definition i (y : OtherProp A) : bool :=
  match y with
  | IsA'' => true
  end.



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
