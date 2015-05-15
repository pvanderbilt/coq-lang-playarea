(** * LProps: Properties of LDef *)

(** This file develops the type safety theorem for the small-step semantics of LDef.v.
    It is currently just Pierce's StlcProp.v. *)

Add LoadPath "~/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

Require Export LDef.

Module LDefProps.
Import LDEF.

(* ###################################################################### *)
(** ** Canonical Forms *)

Lemma canonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal. 
    (* manual version:
    inversion HVal; subst; clear HVal.
      inversion HT; subst; clear HT. exists x0. exists t0.  auto.
      inversion HT. 
      inversion HT. 
  my version:*)
  inversion HVal; subst; inversion HT; subst; clear HVal HT.
  (* inversion HVal; intros; subst; try inversion HT; subst; auto. -- original *)
  exists x t0.  auto.
Qed.
   

(* ###################################################################### *)
(** ** Progress *)

(** The _progress_ theorem tells us that closed, well-typed
    terms are not stuck: either a well-typed term is a value, or it
    can take an evaluation step.  
  The proof is by induction on the derivation of [|- t \in T]. *)

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

(** _Proof_: 

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we know immediately that [t] is a value.

    - If the last rule of the derivation was [T_App], then [t = t1
      t2], and we know that [t1] and [t2] are also well typed in the
      empty context; in particular, there exists a type [T2] such that
      [|- t1 \in T2 -> T] and [|- t2 \in T2].  By the induction
      hypothesis, either [t1] is a value or it can take an evaluation
      step.

        - If [t1] is a value, we now consider [t2], which by the other
          induction hypothesis must also either be a value or take an
          evaluation step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation was [T_If], then [t = if t1
      then t2 else t3], where [t1] has type [Bool].  By the IH, [t1]
      either is a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps
          to [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]).
*)

Proof with eauto.
  intros t T Ht.
  remember (empty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".
    (* contradictory: variables cannot be typed in an 
       empty context *)
    inversion H. 

  Case "T_App". 
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a 
       value or steps... *)
    right. destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is also a value".
        apply canonical_forms_fun in Ht1.
          destruct Ht1 as [x0 [t0 Heq]]. subst. eexists. 
            apply ST_AppAbs. assumption.
          assumption.
        (* original: 
        assert (exists x0 t0, t1 = tabs x0 T11 t0).
        eapply canonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...
      *)

      SSCase "t2 steps".
(* Why doesn't this work?
        eexists. apply ST_App2.
          assumption.  inversion H0 as [t2' Hstp]. subst.  eapply Hstp. 
*)
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...

    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...

  Case "T_If".
    right. destruct IHHt1...

    SCase "t1 is a value".
      destruct (canonical_forms_bool t1); subst; eauto.

    SCase "t1 also steps".
      inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...
Qed.

(** (Exercise: 3 ) A proof that progress can also be proved by induction on terms
    instead of induction on typing derivations. *)

Theorem progress' : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof.
  intros t.
  t_cases (induction t) Case; intros T Ht; auto.
  (* FILLED IN  *)
    Case "tvar". inversion Ht. inversion H1.
    Case "tapp". right. inversion Ht; subst; clear Ht. 
        destruct IHt1 with (T:=TArrow T11 T).  (* t1 : T11-->T *) apply H2.
      SCase "value t1". apply IHt2 in H4. clear IHt2. destruct H4.
        SSCase "value t2". apply canonical_forms_fun in H2. 
          destruct H2 as [x0 [t0 Heq]]. subst.
          eexists. apply ST_AppAbs. assumption. assumption.
        SSCase " t2 ==> t' ". destruct H0 as [t2' Ht2]. eexists. 
          apply ST_App2. assumption. eassumption.
      SCase "t1==>t1'". destruct H as [t1' Ht1]. eexists. 
        apply ST_App1. eassumption.
    Case "tif". right. inversion Ht; subst; clear Ht. 
          destruct IHt1 with (T:=TBool). apply H3.
      SCase "value t1". apply canonical_forms_bool in H3. destruct H3; subst.
        SSCase "t1 = ttrue". eexists. apply ST_IfTrue.
        SSCase "t1 = tfalse". eexists. apply ST_IfFalse.
        apply H.
      SCase "t1==>t1'". destruct H as [t1' Ht1]. eexists. 
        apply ST_If. eassumption.
Qed.
(** [] *)

(* ###################################################################### *)
(** ** Preservation *)


(* ###################################################################### *)
(** *** Free Occurrences *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif t1 t2 t3).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2" 
  | Case_aux c "afi_abs" 
  | Case_aux c "afi_if1" | Case_aux c "afi_if2" 
  | Case_aux c "afi_if3" ].

Hint Constructors appears_free_in.

(** A term in which no variables appear free is said to be _closed_. *)

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(* ###################################################################### *)
(** *** Substitution *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', lookup_vdecl x Gamma = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma. 
  generalize dependent T. 
  afi_cases (induction H) Case; 
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.

(** Next, we'll need the fact that any term [t] which is well typed in
    the empty context is closed -- that is, it has no free variables. *)

(** ** (Exercise: 2 stars, optional (typable_empty__closed))  *)
Corollary typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.
Proof.
  (* FILLED IN *) 
  intros t T Hin x Hfree.
  apply free_in_context with (T:=T) (Gamma:=empty) in Hfree. 
  destruct Hfree. inversion H. assumption.
Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> 
                lookup_vdecl x Gamma = lookup_vdecl x Gamma') ->
     Gamma' |- t \in T.

Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  has_type_cases (induction H) Case; intros; auto.
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to 
       instantiate is [extend Gamma x T11] *)
    unfold extend, lookup_vdecl. destruct (eq_id_dec x x1)... 
  Case "T_App".
    apply T_App with T11...  
Qed.


(** _Lemma_: If [Gamma,x:U |- t \in T] and [|- v \in U], then [Gamma |-
    [x:=v]t \in T]. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     extend Gamma x U |- t \in T ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in T.

(** One technical subtlety in the statement of the lemma is that we
    assign [v] the type [U] in the _empty_ context -- in other words,
    we assume [v] is closed.  This assumption considerably simplifies
    the [T_Abs] case of the proof (compared to assuming [Gamma |- v \in
    U], which would be the other reasonable assumption at this point)
    because the context invariance lemma then tells us that [v] has
    type [U] in any context at all -- we don't have to worry about
    free variables in [v] clashing with the variable being introduced
    into the context by [T_Abs]. *)

Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T. 
  t_cases (induction t) Case; intros T Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; clear H (* added *); simpl...
  Case "tvar".
    rename i into y. destruct (eq_id_dec x y).
    SCase "x=y".
      subst. 
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
      eapply context_invariance... intros x Hcontra.
      (* added Ht' & removed .. *)
      destruct (free_in_context _ _ T empty Hcontra Ht') as [T' HT']. 
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2... 
  Case "tabs".
    rename i into y. apply T_Abs.
    destruct (eq_id_dec x y).
    SCase "x=y".
      eapply context_invariance...
      subst.
      intros x Hafi. unfold extend, lookup_vdecl.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend, lookup_vdecl.
      destruct (eq_id_dec y z)...
      subst. rewrite neq_id... 
Qed.

(** The substitution lemma can be viewed as a kind of "commutation"
    property.  Intuitively, it says that substitution and typing can
    be done in either order: we can either assign types to the terms
    [t] and [v] separately (under suitable contexts) and then combine
    them using substitution, or we can substitute first and then
    assign a type to [ [x:=v] t ] -- the result is the same either
    way. *)

(* ###################################################################### *)
(** *** Main Theorem *)

(** Preservation: if a closed
    term [t] has type [T], and takes an evaluation step to [t'], then [t']
    is also a closed term with type [T].  In other words, the small-step
    evaluation relation preserves types.
    Proof by induction on the derivation of [|- t \in T].
*)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.

Proof with eauto.
  remember (empty) as Gamma.
  intros t t' T HT. generalize dependent t'.  
      (* playing around:
        has_type_cases (induction HT) Case. admit. admit. admit.  admit. admit. 
        intros t' HE. subst Gamma. subst. inversion HE. subst. assumption. subst. assumption. subst. apply T_If; try assumption.
        apply IHHT1. reflexivity . apply H3. *)
       has_type_cases (induction HT) Case;
       intros t' HE; subst Gamma; subst; 
       try solve [inversion HE; subst; auto].
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction, 
       and [eauto] takes care of them *)
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      inversion HT1...  
Qed.


(* ###################################################################### *)
(** ** Type Soundness *)

(** Progress and preservation together imply that a well-typed
    term can _never_ reach a stuck state.  *)

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti   (* FILLED IN  *)  as [ x | x y z ].
    Case "multi_refl: x==>x". 
      apply progress in Hhas_type. destruct Hhas_type; auto.
    Case "multi_step: x==>y, y==>*z". 
      apply IHHmulti; try assumption.
      eapply preservation.
        apply Hhas_type.
        assumption.
Qed.

(* ###################################################################### *)
(** ** Uniqueness of Types *)

(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type.  

    (Exercise) TBD: Formalize this statement and prove it. *)
(* FILL IN HERE *)

End LDefProps.