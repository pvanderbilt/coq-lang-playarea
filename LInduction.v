(** * LInduction: An induction principal for LDef *)

(**  This file defines an induction principal based on induction over terms 
      with inversion on typing. It is used in LEProps1.v, but it doesn't really 
      make the proof any simpler.*)

Add LoadPath "~/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

Require Export LDef LEval.
Import LDEF.
Import LEVAL.

Theorem tm_ind_with_ty_inv:
  forall P : context -> tm -> ty -> Prop,
  (
    forall G x T,
    G x = Some T ->
      P G (tvar x) T
  ) -> (
    forall G T1 T2,
    forall t1 : tm, G |- t1 \in TArrow T1 T2 -> P G t1 (TArrow T1 T2) -> 
    forall t2 : tm, G |- t2 \in T1 -> P G t2 T1 -> 
      P G (tapp t1 t2) T2
  ) -> (
    forall G (T1 T2 : ty),
    forall (x : id) (tb : tm), 
    extend G x T1 |- tb \in T2 ->
    P (extend G x T1) tb T2 -> 
      P G (tabs x T1 tb) (TArrow T1 T2)
  ) -> (
    forall G, P G ttrue TBool 
  ) -> (
    forall G, P G tfalse TBool
  )  ->
  (
    forall G T,
    forall tb : tm, G |- tb \in TBool -> P G tb TBool -> 
    forall tt : tm, G |- tt \in T -> P G tt T -> 
    forall te : tm, G |- te \in T -> P G te T -> 
      P G (tif tb tt te) T
  ) ->
    forall (G : context) (t : tm) (T : ty), G |- t \in T -> P G t T.
Proof.
  intros P Hvar Happ Habs Htrue Hfalse Hif G t T Hin.
  generalize dependent G. generalize dependent T.
  induction t; intros T G Hin; inversion Hin; subst; clear Hin. 
    apply (Hvar _ _ _ H1).
    apply (Happ G T11 T t1 H2 (IHt1 _ _ H2) t2 H4 (IHt2 _ _ H4)).
    apply (Habs G t T12 i t0 H4 (IHt _ _ H4)).
    apply (Htrue G).
    apply (Hfalse G).
    apply (Hif G T t1 H3 (IHt1 _ _ H3) t2 H5 (IHt2 _ _ H5) t3 H6 (IHt3 _ _ H6)).
Qed.

(* This older version does not have the typing assertions. *)

Theorem tm_ind_with_ty_inv':
  forall P : context -> tm -> ty -> Prop,
	(
    forall G x T,
    G x = Some T ->
    	P G (tvar x) T
	) -> (
    forall G T1 T2,
    forall t1 : tm, P G t1 (TArrow T1 T2) -> 
    forall t2 : tm, P G t2 T1 -> 
    	P G (tapp t1 t2) T2
	) -> (
    forall G (T1 T2 : ty),
    forall (x : id) (tb : tm), 
    P (extend G x T1) tb T2 -> 
    	P G (tabs x T1 tb) (TArrow T1 T2)
	) -> (
    forall G, P G ttrue TBool 
  ) -> (
    forall G, P G tfalse TBool
  )  ->
	(
    forall G T,
    forall tb : tm, P G tb TBool -> 
    forall tt : tm, P G tt T -> 
    forall te : tm, P G te T -> 
    	P G (tif tb tt te) T
	) ->
    forall (G : context) (t : tm) (T : ty), G |- t \in T -> P G t T.
Proof.
  intros P Hvar Happ Habs Htrue Hfalse Hif G t T Hin.
  generalize dependent G. generalize dependent T.
  induction t; intros T G Hin; inversion Hin; subst; clear Hin. 
    apply (Hvar _ _ _ H1).
    apply (Happ G T11 T t1 (IHt1 _ _ H2) t2  (IHt2 _ _ H4)).
    apply (Habs G t T12 i t0 (IHt _ _ H4)).
    apply (Htrue G).
    apply (Hfalse G).
    apply (Hif G T t1 (IHt1 _ _ H3) t2  (IHt2 _ _ H5) t3 (IHt3 _ _ H6)).
Qed.

