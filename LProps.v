(** * LProps: Properties of STLC Typing (for the language defined in LDef.v). *)

Load Init.
Require Export SfLib.
Require Import LibTactics.

Require Export Common LDef.
Import P3Common.

Module LProps.
Import LDEF.

(* ###################################################################### *)
(** **  *)


(* #################################### *)
(** *** Record Field Lookup *)

Lemma rcd_field_lookup : 
  forall rb Trb x Tx,
    empty |- rb *\in Trb ->
    lookup_vdecl x Trb = Some Tx ->
    exists vx, lookup_vdef x rb = Some vx /\ empty |- vx \in Tx.
Proof.
  intros rb Tr x Tx Ht Hl.
  induction Ht as [| G y vy Ty rb' Trb' Hty Ht]. 
  Case "nil". inversion Hl.
  Case "cons".
    destruct (eq_id_dec y x).
      SCase "x=y". subst. 
        rewrite (lookup_add_vdecl_eq x Ty Trb') in Hl. inverts Hl.
        exists vy. split.
          apply lookup_add_vdef_eq.
          apply Hty.
      SCase "y<>x".
        rewrite (lookup_add_vdecl_neq _ _ Ty Trb' n) in Hl. 
        destruct (IHHt Hl) as [vx [Hlx HTx]]; clear IHHt.
        exists vx. split.
          rewrite (lookup_add_vdef_neq _ _ _ _ n). apply Hlx.
          apply HTx.
Qed.

(* ###################################################################### *)
(** *** Progress *)

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'. 
Proof with eauto.
  (* Theorem: Suppose empty |- t : T.  Then either
       1. t is a value, or
       2. t ==> t' for some t'.
     Proof: By induction on the given typing derivation. *)
  intros t T Ht.
  remember (empty) as Gamma.
  generalize dependent HeqGamma.
  Ltac p_ind_tactic Ht := induction Ht using has_type_ind_both
    with (P0 := fun G tr Tr => 
       G = empty -> 
       value_rcd tr \/ (exists tr', tr *==> tr')).
  has_type_both_cases (p_ind_tactic Ht) Case; intros HeqGamma; subst; 
    try (left; auto; fail).
     (* the [try  (left; auto; fail)] tactic handles the value cases 
      (T_Abs, T_True, T_False, TR_Nil) *)

  Case "T_Var".
    (* The final rule in the given typing derivation cannot be [T_Var],
       since it can never be the case that [empty |- x : T] (since the
       context is empty). *)
    inversion H.

  Case "T_App".
    (* If the last rule applied was T_App, then [t = t1 t2], and we know 
       from the form of the rule that
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       By the induction hypothesis, each of t1 and t2 either is a value 
       or can take a step. *)
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
      (* If both [t1] and [t2] are values, then we know that 
         [t1 = tabs x T11 t12], since abstractions are the only values
         that can have an arrow type.  But 
         [(tabs x T11 t12) t2 ==> [x:=t2]t12] by [ST_AppAbs]. *)
        inversion H; subst; try (solve by inversion).
        exists ([x:=t2]t12)...
      SSCase "t2 steps".
        (* If [t1] is a value and [t2 ==> t2'], then [t1 t2 ==> t1 t2'] 
           by [ST_App2]. *)
        destruct H0 as [t2' Hstp]. exists (tapp t1 t2')...
    SCase "t1 steps".
      (* Finally, If [t1 ==> t1'], then [t1 t2 ==> t1' t2] by [ST_App1]. *)
      destruct H as [t1' Hstp]. exists (tapp t1' t2)...

  Case "T_Rcd".
    (* If the last rule in the given derivation is [T_Rcd], then 
       [t = (trcd tr)], [T=(Trcd Tr)] and [empty |- tr *: Tr]. 
      The combined induction rule requires that P0->P 
      which is what we establish here. *)
    destruct (IHHt eq_refl) as [Hv | [tr' Hst]]; clear IHHt.
      SCase "value_rcd tr". left. apply (v_rcd _ Hv).
      SCase "tr *==> tr". right. exists (trcd tr'). apply (ST_Rcd _ _ Hst).

  Case "T_Proj".
    (* If the last rule in the given derivation is [T_Proj], then 
       [t = tproj t x] and [empty |- t : (TRcd Tr)]
       By the IH, [t] either is a value or takes a step. *)
    right. destruct IHHt...
    SCase "t is value".
      (* If [t] is a value and [t : TRcd Tr], we can invert the
          latter to get that [t = (trcd tr)] with [tr *: Tr] *)
      inverts Ht; try solve by inversion...
      (* Lemma [rcd_field_lookup] shows that [lookup_vdef x tr = Some vx] for
         some [vx].*)
      destruct (rcd_field_lookup _ _ _ Tx H4 H) as [vx [Hlxr Htx]].
      (* So [tproj x t ==> vx] by [ST_ProjRcd] with the inversion of H0
         to get that [vx] is a value.  *)
      exists vx. inverts H0 as H0. apply (ST_ProjRcd _ _ _ H0 Hlxr).
    SCase "t steps".
      (* On the other hand, if [t ==> t'], then [tproj t x ==> tproj t' x]
         by [ST_Proj1]. *)
      destruct H0 as [t' Hstp]. exists (tproj t' x)...

  Case "T_If".
    right. destruct IHHt1...

    SCase "t1 is a value".
      inverts H; try inversion Ht1; eauto.
      (* destruct (canonical_forms_bool t1); subst; eauto.*)

    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...

  Case "TR_Cons".
    (* If the last rule was [T_Rcd] established by [TR_Cons], then 
          [tr = cons (x, t) tr],
          [Tr = cons (x, T) Tr],
          [ empty |- t : Tx] and
          [empty |- tr *: Tr].
        By the P IH, either t is a value or it steps and
        by the P0 IH, either tr is a value or it steps. *)
    destruct (IHHt eq_refl) as [Hvt | [t' Hstt']]; clear IHHt.
      SSCase "value t". 
          destruct (IHHt0 eq_refl) as [Hvtr | [tr' Hsttr']]; clear IHHt0.
        SSSCase "value_rcd tr". 
          left. apply (vr_cons _ _ _ Hvt Hvtr).
        SSSCase "tr *==> tr'". 
          right. eexists. apply (STR_Tail _ _ _ _ Hvt Hsttr').
      SSCase "t ==> t'". right. eexists. apply (STR_Head _ _ _ _ Hstt').
Qed.

(* ###################################################################### *)
(** *** Context Invariance *)

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
  | afi_proj : forall x t i,
     appears_free_in x t ->
     appears_free_in x (tproj t i)
  | afi_rcd : forall x r,
     appears_free_in_rcd x r -> 
     appears_free_in x (trcd r)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif t1 t2 t3)

with appears_free_in_rcd : id -> (list def) -> Prop :=
  | afi_rhead : forall x i ti r',
      appears_free_in x ti ->
      appears_free_in_rcd x (add_vdef i ti r')
  | afi_rtail : forall x i ti r',
      appears_free_in_rcd x r' ->
      appears_free_in_rcd x (add_vdef i ti r').

Hint Constructors appears_free_in appears_free_in_rcd.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> 
                lookup_vdecl x Gamma = lookup_vdecl x Gamma') ->
     Gamma' |- t \in S.
Proof with eauto 15.
  intros. generalize dependent Gamma'.
  Ltac ci_ind_tactic H := induction H using has_type_ind_both with 
    (P0 := fun Gamma r RS => 
      forall Gamma' : context,
      (forall x : id, appears_free_in_rcd x r -> 
                      lookup_vdecl x Gamma = lookup_vdecl x Gamma') ->
      Gamma' |- r *\in RS).
  has_type_both_cases (ci_ind_tactic H) Case; intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold extend, lookup_vdecl. destruct (eq_id_dec x y)...
Qed.


Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T',  lookup_vdecl x Gamma = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  Ltac fic_ind_tactic H x := induction H using has_type_ind_both with 
    (P0 := fun Gamma r RS => 
      appears_free_in_rcd x r ->
      Gamma |- r *\in RS ->
      exists T', lookup_vdecl x Gamma = Some T').
  has_type_both_cases (fic_ind_tactic Htyp x) Case; 
    inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold extend, lookup_vdecl in Hctx. 
    rewrite neq_id in Hctx... 
Qed.


(* ###################################################################### *)
(** *** Substitution preserves typing *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (extend Gamma x U) |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- ([x:=v]t) \in S.
Proof with eauto 15.
  (* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then 
     Gamma |- ([x:=v]t) S. *)
  intros Gamma x U v t S Htypt Htypv. 
  generalize dependent Gamma. generalize dependent S.
  (* Proof: By extended induction on the term t.  Most cases follow directly
     from the IHs, with the exception of tvar and tabs, which
     aren't automatic because we must reason about how the
     variables interact. *)
  Ltac spt_induction t x v U := induction t using tm_nest_rect with 
    (Q := fun r =>
      forall (RT : list decl) (Gamma : context),
        (extend Gamma x U) |- r *\in RT -> 
        Gamma |- (subst_rcd x v r) *\in RT).
  t_both_cases (spt_induction t x v U) Case; 
    intros S Gamma Htypt; simpl; inverts Htypt...

  Case "tvar".
    simpl. rename x0 into y.
    (* If t = y, we know that
         [empty |- v : U] and
         [Gamma,x:U |- y : S]
       and, by inversion, [extend Gamma x U y = Some S].  We want to
       show that [Gamma |- [x:=v]y : S].

       There are two cases to consider: either [x=y] or [x<>y]. *)
    destruct (eq_id_dec x y). 
    SCase "x=y".
    (* If [x = y], then we know that [U = S], and that [[x:=v]y = v].
       So what we really must show is that if [empty |- v : U] then
       [Gamma |- v : U].  We have already proven a more general version
       of this theorem, called context invariance. *)
      subst.
      unfold extend, lookup_vdecl in H1. rewrite eq_id in H1. 
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
      apply T_Var... unfold extend, lookup_vdecl in H1. rewrite neq_id in H1...

  Case "tabs".
    rename x0 into y. rename T into T1.
    (* If [t = tabs y T1 t0], then we know that
         [Gamma,x:U |- tabs y T11 t0 : T1->T2]
         [Gamma,x:U,y:T1 |- t0 : T2]
         [empty |- v : U]
       As our IH, we know that forall S Gamma, 
         [Gamma,x:U |- t0 : S -> Gamma |- [x:=v]t0 S].
    
       We can calculate that 
         [x:=v]t = tabs y T11 (if beq_id x y then t0 else [x:=v]t0)
       And we must show that [Gamma |- [x:=v]t : T11->T12].  We know
       we will do so using [T_Abs], so it remains to be shown that:
         [Gamma,y:T11 |- if beq_id x y then t0 else [x:=v]t0 : T12]
       We consider two cases: [x = y] and [x <> y].
    *)
    apply T_Abs...
    destruct (eq_id_dec x y).
    SCase "x=y".
    (* If [x = y], then the substitution has no effect.  Context
       invariance shows that [Gamma,y:U,y:T11] and [Gamma,y:T11] are
       equivalent.  Since the former context shows that [t0 : T12], so
       does the latter. *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold extend, lookup_vdecl.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
    (* If [x <> y], then the IH and context invariance allow us to show that
         [Gamma,x:U,y:T1 |- t : T2]       =>
         [Gamma,y:T11,x:U |- t : T2]      =>
         [Gamma,y:T11 |- [x:=v]t : T2] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend, lookup_vdecl.
      destruct (eq_id_dec y z)... 
      subst. rewrite neq_id...

  Case "trcd". 
    (* Due to having to define subst_rec within subst, 
       the goal is in a form that doesn't match, so
       we use a special lemma to get it back into a form
       that eauto can handle. *)
    rewrite <- (subst_rcd_eqv x v rb)... 

  Case "trcons". (* TBD: Why doesn't this work automatically? *)
    apply TR_Cons...
Qed.

(** *** Preservation *)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  (* Theorem: If [empty |- t : T] and [t ==> t'], then [empty |- t' : T]. *)
  remember (empty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many cases are
     contradictory ([T_Var], [T_Abs]) or follow directly from the IH
     ([T_RCons]).  We show just the interesting ones. *)
  Ltac pres_ind_tactic HT := induction HT using has_type_ind_both
    with (P0 := fun Gamma tr Tr => forall tr' : list def,
       Gamma = empty -> 
       tr *==> tr' ->
       Gamma |- tr' *\in Tr).
  has_type_both_cases (pres_ind_tactic HT) Case;
    introv HeqGamma HE; subst; inverts HE... 

  Case "T_App".
    (* If the last rule used was [T_App], then [t = t1 t2], and three rules
       could have been used to show [t ==> t']: [ST_App1], [ST_App2], and 
       [ST_AppAbs]. In the first two cases, the result follows directly from 
       the IH. *)
    SCase "ST_AppAbs".
      (* For the third case, suppose 
           [t1 = tabs x T11 t12]
         and
           [t2 = v2].  We must show that [empty |- [x:=v2]t12 : T2]. 
         We know by assumption that
             [empty |- tabs x T11 t12 : T1->T2]
         and by inversion
             [x:T1 |- t12 : T2]
         We have already proven that substitution_preserves_typing and 
             [empty |- v2 : T1]
         by assumption, so we are done. *)
      apply substitution_preserves_typing with T1...
      inversion HT1...

  Case "T_Proj".
    (* If the last rule was [T_Proj], then [t = tproj t0 x] 
       where [t0 : (TRcd Tr)] and [lookup_vdecl x Tr = Some T]
       for some [t0], [x] and [Tr]. Two rules could have caused 
       [t ==> t']: [ST_Proj1] and [ST_ProjRcd].  The typing
       of [t'] follows from the IH in the former case.

       In the [ST_ProjRcd] case, [t0 = (trcd r)] for some [r]
       where [value_rcd r] and [lookup_vdef x r = Some t'].
       Inverting Ht gives [r *: Tr] and we can apply lemma
       [rcd_field_lookup] to find the record element this
       projection steps to. *)
    inverts HT.
    destruct (rcd_field_lookup _ _ _ _ H5 H) as [vx [ Hlxr Htx]].
    rewrite H4 in Hlxr. inversion Hlxr...

Qed.
(** [] *)

End LProps.
