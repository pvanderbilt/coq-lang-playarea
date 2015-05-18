(** * TestsR: Tests of RecordsExt.v *)

(**  *)

Add LoadPath "/Users/pv/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

(* Require Export Stlc. *)
Require Export Common RecordsExt.
Import P3Common Records.

Module RETests.

(** Some variables, for examples... *)

Notation a := (Id 0).
Notation f := (Id 1).
Notation g := (Id 2).
Notation l := (Id 3).
Notation A := (TBase (Id 4)).
Notation B := (TBase (Id 5)).
Notation k := (Id 6).
Notation i1 := (Id 7).
Notation i2 := (Id 8).

(* Playing around with notations *)
(*
Example base1 : alookup a (aextend a (ttrue) nil) = Some ttrue.
Proof. reflexivity. Qed.

Notation "G ';;' 'val' x '\in' T" := (aextend x T G) (at level 40).

Example base1c : alookup a (nil ;; val a \in TBool) = Some TBool.
Proof. reflexivity. Qed.

Notation "G 'has' 'val' x '\in' T" := (alookup x G = Some T) (at level 40).

Example base1d : (nil ;; val a \in TBool) has val a \in TBool.
Proof. reflexivity. Qed.
*)
(** [{ i1:A }] *)

Example er1 : exists (t:ty), t = TRcd [(Lv i1 A)].
Proof. eauto. Qed.

(** [{ i1:A->B, i2:A }] *)
Example er2 : exists (t:ty), t = 
  TRcd [(Lv i1 (TArrow A B)); (Lv i2 A)].
Proof. eauto. Qed.

Definition substf_ok (sfunc:  id -> tm -> tm -> tm) :=
  sfunc a (tvar f) (tvar a) = tvar f
    /\ sfunc a (tvar f) (tvar g) = tvar g
    /\ sfunc g (tvar f) (tvar a) = tvar a
    /\ sfunc a (tvar g) (tproj (tvar a) a) = tproj (tvar g) a
    /\ sfunc a (tvar g) (tapp (tvar f) (tvar a)) = tapp (tvar f) (tvar g)
    /\ sfunc a  (tapp (tvar f) (tvar a)) (tproj (tvar a) a)
        =  tproj  (tapp (tvar f) (tvar a)) a.

Example subst_ok :substf_ok subst.
Proof. unfold substf_ok. repeat split. Qed.

Notation "Ls ';;;' x '\in' T" := (add_vdecl x T Ls) (at level 40).
Notation "Fs ';;;' x = t"     := (add_vdef x t Fs) (at level 40).

Example er2a : exists (t:ty), t = 
  TRcd (nil ;;; i1 \in (TArrow A B) ;;; i2 \in A).
Proof. eauto. Qed.

Hint Constructors has_type rcd_has_type.

Lemma typing_example_2 : 
  empty |- 
    (tapp (tabs a (TRcd [(Lv i1 (TArrow A A)); (Lv i2 (TArrow B B))])
              (tproj (tvar a) i2))
            (trcd [(Fv i1 (tabs a A (tvar a))); (Fv i2 (tabs a B (tvar a)))]) )
    \in (TArrow B B).
Proof. 
  (* info_eauto 20 using has_type, rcd_has_type, eq_id. *)
  eauto 20 using extend_eq. 
  (* TBD: Figure out why eauto isn't taking the hints (above and before) *)
  eapply T_App.
    eapply T_Abs. eapply T_Proj.
      eapply T_Var.  eapply extend_eq.
      reflexivity. 
    eapply T_Rcd.
      eapply TR_Cons. eapply T_Abs. eapply T_Var. eapply extend_eq.
      eapply TR_Cons. eapply T_Abs. eapply T_Var. eapply extend_eq.
      eapply TR_Nil.
Qed.

(** Before starting to prove this fact (or the one above!), make sure
    you understand what it is saying. *)

Example typing_nonexample : 
  ~ exists T,
      (extend empty a (TRcd (cons (Lv i2 (TArrow A A)) nil)))  |-
               (trcd (cons (Fv i1 (tabs a B (tvar a))) nil)) \in
               T.
  (* no T | a : { i2 : A->A } |- { i1 = λ a:B . a } : T *)
Proof.
  (* FILL IN HERE *) Admitted.

Example typing_nonexample_2 : forall y,
  ~ exists T,
    (extend empty y A) |-
           (tapp (tabs a (TRcd [(Lv i1 A)]) (tproj (tvar a) i1))
                 (trcd [(Fv i1 (tvar y)); (Fv i2 (tvar y))]) ) \in
           T.
  (* forall y, ~ exists T, y : A |- (λ a : { i1 : A} . a.i1) { i1 = y; i2 = y } : T *)
Proof.
  (* FILL IN HERE *) Admitted.

End RETests.
