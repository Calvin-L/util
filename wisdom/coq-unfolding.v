Require Import PeanoNat.
Require Import Omega.

(* A complicated definition, as an example.  It so happens that
 * forall n, test n = 0.  However, we won't be using that fact. *)
Fixpoint test (n : nat) :=
  if Nat.eq_dec n 10 then 0 else
  match n with
  | S n' => test n'
  | _ => n
  end.

Lemma goal:
  forall n,
    test n <= n.
Proof.
  intros.
  unfold test.
  (* Oops!  It is impossible to coax Coq to apply `test` to n, as far as I am
   * aware.  Because `test` is a fixpoint, Coq will only apply it when the
   * decreasing argument (`n`, in this case) is a constructor application. *)
Abort.

(* For such cases, it can help to prove an "unfolding" lemma like this one.
 * The lemma's proof is awkward: it destructs `n` even though it doesn't seem
 * to need it.  However, the destruction is necessary to let Coq apply the
 * fixpoint to the argument. *)
Lemma unfold_test:
  forall n,
    test n = (if Nat.eq_dec n 10 then 0 else
      match n with
      | S n' => test n'
      | _ => n
      end).
Proof.
  destruct n; reflexivity.
Qed.

(* Now we can have more success! *)
Lemma goal:
  forall n,
    test n <= n.
Proof.
  intros.
  rewrite unfold_test.
  (* The goal looks much better now! *)
  (* Our example concluded, the rest of the proof is irrelevant. *)
Admitted.
