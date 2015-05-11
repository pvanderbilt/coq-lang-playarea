(** * Common Definitions *)
(** Data structures used by other modules. *)

Add LoadPath "/Users/pv/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

Module P3Common.

(** ** Association lists (alists) *)

Definition alist (T : Type) : Type := list (id * T).

Fixpoint lookup {X: Type} (x: id) (a: alist X) : option X :=
  match a with
    | nil => None
    | cons (y, v) a' => if eq_id_dec x y then (Some v) else (lookup x a')
    end.

Lemma lookup_cons_eq : 
  forall T x (v : T) (a : alist T),
    lookup x (cons (x, v) a) = Some v.
Proof.
  intros. simpl. apply eq_id.
Qed.

Lemma lookup_cons_neq :
  forall T x y (v : T) (a : alist T),
    x <> y ->
    lookup x (cons (y, v) a) = lookup x a.
Proof.
  intros. simpl. apply neq_id. apply H.
Qed.

End P3Common.
