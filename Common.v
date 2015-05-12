(** * Common Definitions *)
(** Data structures used by other modules. *)

Add LoadPath "/Users/pv/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

Module P3Common.

(** ** Association lists (alists) *)

Definition alist (T : Type) : Type := list (id * T).

Definition aextend {T: Type} (x: id) (v : T) (a: alist T) := (x, v) :: a.

Fixpoint alookup {T: Type} (x: id) (a: alist T) : option T :=
  match a with
    | nil => None
    | cons (y, v) a' => if eq_id_dec y x then (Some v) else (alookup x a')
    end.

Lemma alookup_cons_eq : 
  forall T x (v : T) (a : alist T),
    alookup x (cons (x, v) a) = Some v.
Proof.
  intros. simpl. apply eq_id.
Qed.

Lemma alookup_cons_neq :
  forall T x y (v : T) (a : alist T),
    y <> x ->
    alookup x (cons (y, v) a) = alookup x a.
Proof.
  intros. simpl. apply neq_id. apply H.
Qed.

Lemma alookup_aextend_eq : 
  forall T x (v : T) (a : alist T),
    alookup x (aextend x v a) = Some v.
Proof.
  intros. simpl. apply eq_id.
Qed.

Lemma alookup_aextend_neq :
  forall T x y (v : T) (a : alist T),
    y <> x ->
    alookup x (aextend y v a) = alookup x a.
Proof.
  intros. simpl. apply neq_id. apply H.
Qed.

Hint Unfold aextend.

End P3Common.
