(*

Mutually-inductive types are a beast in Coq.  If your type includes lists of
itself, then it is mutally-inductive!  To manage such types you often need to
write your own "induction scheme".  Fortunately this is a formulaic job; see
below.

*)

(* this definition from CPDT [*] is very useful *)
Fixpoint All {T} (l : list T) (P : T -> Prop) : Prop :=
  match l with
  | nil => True
  | cons x l' => P x /\ All l' P
  end.

Definition Var := nat.
Definition Frame := nat.
Inductive Exp : Set :=
  | EVar : Var -> Exp
  | ECall : Exp -> list Exp -> Exp (* mutual induction via list *)
  | ECalling : Frame -> Stm -> Exp
with Stm : Set := (* mutual induction between Stm and Exp *)
  | SSkip
  | SIf : Exp -> Stm -> Stm -> Stm.

Section syntax_ind.

  Variable Pe : Exp -> Prop.
  Variable Ps : Stm -> Prop.

  Hypothesis rec_EVar     : forall var, Pe (EVar var).
  Hypothesis rec_ECall    : forall f args, All args Pe -> Pe (ECall f args).
  Hypothesis rec_ECalling : forall fr s, Ps s -> Pe (ECalling fr s).

  Hypothesis rec_SSkip    : Ps SSkip.
  Hypothesis rec_SIf      : forall e s1 s2, Pe e -> Ps s1 -> Ps s2 -> Ps (SIf e s1 s2).

  Fixpoint exp_mut_ind (e : Exp) : Pe e :=
    match e with
    | EVar var          => rec_EVar var
    | ECall f es        => rec_ECall f es ((fix G es : All es Pe :=
      (* this inline fixpoint handles the mutually-recursive list *)
      match es with
      | nil => I
      | cons e es' => conj (exp_mut_ind e) (G es')
      end) es)
    | ECalling fr s      => rec_ECalling fr s (stm_mut_ind s)
    end
    with stm_mut_ind (s : Stm) : Ps s :=
    match s with
    | SSkip             => rec_SSkip
    | SIf e s1 s2       => rec_SIf e s1 s2 (exp_mut_ind e) (stm_mut_ind s1) (stm_mut_ind s2)
    end.

End syntax_ind.

Lemma test_exp:
  forall (e : Exp),
    True.
Proof.
  intro e.
  induction e using exp_mut_ind with (Ps := fun s => True).
  - trivial.
  - induction args; simpl in *.
    + trivial.
    + apply IHargs.
      destruct H.
      assumption.
  - apply IHe.
  - trivial.
  - apply IHe.
Qed.

Lemma test_stm:
  forall (s : Stm),
    True.
Proof.
  intro s.
  induction s using stm_mut_ind with (Pe := fun e => True); trivial.
Qed.

(*

Refs.
  [*]: Cerified Programming with Dependent Types by Adam Chlipala

*)
