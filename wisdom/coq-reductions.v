(*
 * Guide to Coq's reduction flags (for `cbv` etc).
 * https://coq.inria.fr/distrib/current/refman/proofs/writing-proofs/rewriting.html?highlight=cbv#coq:tacn.cbv
 *)

Definition z := True.

Goal let x := True in (fun y => x /\ y /\ z) True.

  (* --- `beta` is function application --- *)
  cbv beta.  (* goal is: let x := True in x /\ True /\ z *)
  Undo.

  (* --- `delta` is definition inlining, but not for let-expressions --- *)
  cbv delta. (* goal is: let x := True in (fun y => x /\ y /\ True) True *)
  Undo.

  (* --- `delta` can control what definitions get inlined --- *)
  cbv delta [z].  (* goal is: let x := True in (fun y => x /\ y /\ True) True *)
  Undo.
  cbv delta -[z]. (* goal is: let x := True in (fun y => x /\ y /\ z) True *)
  Undo.

  (* --- `zeta` inlines let-expressions --- *)
  cbv zeta.  (* goal is: (fun y => True /\ y /\ z) True *)
  Undo.

Abort.


Fixpoint recfn n :=
  match n with
  | 0 => True
  | S m => recfn m
  end.

Goal if true then recfn 100 else False.

  (* --- `match` simplifies match- and if-expressions --- *)
  cbv match. (* goal is: recfn 100 *)
  Undo.

  (* --- `beta` does NOT simplify recursive function application! --- *)
  cbv delta [recfn].
  cbv beta. (* goal is: if true then (fix recfn n := [...]) 100 else False *)
  Undo.
  Undo.

  (* --- `fix` converts recursive function application to a form `beta` can handle --- *)
  (* NOTE: `fix` does nothing when its decreasing argument is not a constructor!
   * See coq-unfolding.v *)
  cbv delta [recfn].
  cbv fix. (* goal is: if true then (fun n =>
            *   match n with
            *   | 0 => True
            *   | S m => (fix recfn n0 := [...]) m
            *   end) 100
            * else False *)
  Undo.
  Undo.

  (* --- `iota` = `match fix cofix` --- *)
  cbv delta [recfn].
  cbv iota. (* goal is: (fun n =>
             *   match n with
             *   | 0 => True
             *   | S m => (fix recfn n0 := [...]) m
             *   end) 100 *)
  Undo.
  Undo.

Abort.


Goal True.

  pose (local_defn := True).
  assert local_defn.

  (* NOTE: while `z` appears let-bound in context, `zeta` does nothing *)
  (* `delta` works, though *)
  cbv zeta. (* goal is: local_defn *)
  cbv delta [local_defn]. (* goal is: True *)

Abort.
