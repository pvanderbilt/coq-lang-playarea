(** * LProps: Properties of STLC Typing (for the language defined in LDef.v). *)

Load Init.
Require Export SfLib.
Require Import LibTactics.

Require Export Common LDef.
Import Common LDef.


(* ###################################################################### *)
(** ** Progress *)

(** *** Canonical Forms *)
(**  These lemmas aren't currently used. *)

Lemma canonical_forms_bool : forall t,
  empty |-- t \in TBool ->
  is_value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |-- t \in (TArrow T1 T2) ->
  is_value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal. 
  inversion HVal; subst; inversion HT; subst; clear HVal HT.
  exists x t12.  auto.
Qed.
   

(* #################################### *)
(** *** Record Field Lookup *)
(** If [rb *: Trb] and [Trb] has [x:Tx],
    then [rb] has [x=vx] such that [vx:Tx]. *)

Lemma lookup_cons_vdecl_eq : 
  forall (x : id) (T : ty) (Ls : list decl),
    lookup_vdecl x ((Lv x T) :: Ls) = Some T.
Proof.
  intros. simpl. apply eq_id.
Qed.

Lemma lookup_cons_vdecl_neq :
  forall (x y : id) (T : ty) (Ls : list decl),
    y <> x ->
    lookup_vdecl x ((Lv y T) :: Ls) = lookup_vdecl x Ls.
Proof.
  intros. simpl. apply neq_id. apply H.
Qed.

Lemma rcd_field_lookup : 
  forall rb Trb x Tx,
    empty |-- rb *\in Trb ->
    lookup_vdecl x Trb = Some Tx ->
    exists vx, lookup_vdef x rb = Some vx /\ empty |-- vx \in Tx.
Proof.
  intros rb Tr x Tx Ht Hl.
  induction Ht as [| G F L Fs Ls HF HFs].
  Case "nil". inversion Hl.
  Case "cons".
    inversion HF as [? y vy Ty Hty]; subst; clear HF.
    destruct (eq_id_dec y x) as [ ? | Hneq].
      SCase "x=y". subst. 
        rewrite (lookup_cons_vdecl_eq x Ty Ls) in Hl. inverts Hl.
        exists vy. split.
          apply lookup_add_vdef_eq.
          apply Hty.
      SCase "y<>x".
        rewrite (lookup_cons_vdecl_neq _ _ Ty Ls Hneq) in Hl. 
        destruct (IHHFs Hl) as [vx [Hlx HTx]]; clear IHHFs.
        exists vx. split.
          rewrite <- Hlx. apply (lookup_add_vdef_neq _ _ _ _ Hneq). 
          apply HTx.
Qed.

(* ###################################################################### *)
(** *** Progress theorem *)

Theorem progress : forall t T, 
     empty |-- t \in T ->
     is_value t \/ exists t', t ==> t'. 
Proof with eauto.
  (* Theorem: Suppose empty |-- t : T.  Then either
       1. t is a value, or
       2. t ==> t' for some t'.
     Proof: By induction on the given typing derivation. *)
  intros t T Ht.
  remember (empty) as Gamma.
  generalize dependent HeqGamma.

  set (Q := fun G F (L : decl) => 
       G = empty -> 
       is_value_def F \/ (exists F', F >==> F')).
  set (QL := fun G tr (Tr : list decl) => 
       G = empty -> 
       is_value_defs tr \/ (exists tr', tr *>==> tr')).
  has_type_xind_tactic Ht Q QL Case; intros HeqGamma; subst; subst Q QL;
    try (left; auto; fail).
     (* the [try  (left; auto; fail)] tactic handles the value cases 
      (T_Abs, T_True, T_False, TR_Nil) *)

  Case "T_Var".
    (* The final rule in the given typing derivation cannot be [T_Var],
       since it can never be the case that [empty |-- x : T] (since the
       context is empty). *)
    inversion Hlk.

  Case "T_App".
    (* If the last rule applied was T_App, then [t = t1 t2], and we know 
       from the form of the rule that
         [empty |-- t1 : T1 -> T2]
         [empty |-- t2 : T1]
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
       [t = (trcd tr)], [T=(Trcd Tr)] and [empty |-- tr *: Tr]. 
      The combined induction rule requires that P0->P 
      which is what we establish here. *)
    destruct (IHHtr eq_refl) as [Hv | [tr' Hst]]; clear IHHtr.
      SCase "is_value_defs tr". left. apply (v_rcd _ Hv).
      SCase "tr *==> tr". right. exists (trcd tr'). apply (ST_Rcd _ _ Hst).

  Case "T_Proj".
    (* If the last rule in the given derivation is [T_Proj], then 
       [t = tproj t x] and [empty |-- t : (TRcd Tr)]
       By the IH, [t] either is a value or takes a step. *)
    right. destruct IHHt...
    SCase "t is value".
      (* If [t] is a value and [t : TRcd Tr], we can invert the
          latter to get that [t = (trcd tr)] with [tr *: Tr] *)
      inverts Ht; try solve by inversion...
      (* Lemma [rcd_field_lookup] shows that [lookup_vdef x tr = Some vx] for
         some [vx].*)
      destruct (rcd_field_lookup _ _ _ Tx H3 Hlk) as [vx [Hlxr Htx]].
      (* So [tproj x t ==> vx] by [ST_ProjRcd] with the inversion of H0
         to get that [vx] is a value.  *)
      exists vx. inverts H as Hvr. apply (ST_ProjRcd _ _ _ Hvr Hlxr).
    SCase "t steps".
      (* On the other hand, if [t ==> t'], then [tproj t x ==> tproj t' x]
         by [ST_Proj]. *)
      destruct H as [t' Hstp]. exists (tproj t' x)...

  Case "T_If".
    right. destruct IHHtb...

    SCase "tb is a value".
      inverts H; try inversion Htb; eauto.
      (* destruct (canonical_forms_bool tb); subst; eauto.*)

    SCase "tb steps".
      inversion H as [tb' Hstp]. exists (tif tb' tt te)...

  Case "T_Let".
    right. destruct IHHF...
    SCase "is_value_def F".
      destruct H as [x vx].
      exists ([x:=vx]t).
      apply (ST_LetDef x vx t H).

    SCase "exists F', F >==> F'".
      destruct H as [F' HF'].
      exists (tlet F' t).
      apply (ST_Let F F' t HF').

  Case "F_V".
    destruct IHHt...
    (* the value case is handled *)
    SCase "exists t', t ==> t'".
      right. destruct H as [t' Ht']. 
      exists (Fv x t'). apply (STD_V x t t' Ht').

  Case "TR_Cons".
    destruct IHHF...
    SCase "is_value_def F".
      destruct IHHFs...
      (* SSCase is_value_defs Fs is handled *)
      SSCase "exists tr', Fs *>==> tr'".
        destruct H0 as [Fs' HFs'].
        right. exists (F::Fs').
        apply (STR_Tail _ _ _ H HFs').

    SCase "exists F', F >==> F'".
      right. destruct H as [F' HF']. exists (F'::Fs).
      apply (STR_Head _ _ _ HF').
Qed.

(* ###################################################################### *)
(** ** Subsitution preserves typing *)
(** *** Definition of a variable being _free_ *)

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
     appears_free_in_pdefs x r -> 
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
  | afi_let1 : forall x F t,
      appears_free_in_def x F ->
      appears_free_in x (tlet F t)
  | afi_let2 : forall x y t1 t2,
      y <> x ->
      appears_free_in x t2 ->
      appears_free_in x (tlet (Fv y t1) t2)

with appears_free_in_def : id -> def -> Prop :=
  | afi_def_v : forall x y t,
      appears_free_in x t ->
      appears_free_in_def x (Fv y t)

with appears_free_in_pdefs : id -> (list def) -> Prop :=
  | afi_rhead : forall x F Fs,
      appears_free_in_def x F ->
      appears_free_in_pdefs x (F :: Fs)
  | afi_rtail : forall x F Fs,
      appears_free_in_pdefs x Fs ->
      appears_free_in_pdefs x (F :: Fs).

Hint Constructors appears_free_in appears_free_in_def appears_free_in_pdefs.

(** *** Definition of a _closed_ term *)

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(** *** Lemma [free_in_context]

If [x] is free in typable [t], it must be defined by the context. *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |-- t \in T ->
   exists T',  lookup_vdecl x Gamma = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_xind_tactic Htyp 
    (fun Gamma F (L : decl) => 
      appears_free_in_def x F ->
      exists T', lookup_vdecl x Gamma = Some T'
    ) 
    (fun Gamma r (RS : list decl) => 
      appears_free_in_pdefs x r ->
      exists T', lookup_vdecl x Gamma = Some T'
    ) 
    Case; inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtb as [T' Hctx]... exists T'.
    rewrite (lookup_add_vdecl_neq _ _ T1 Gamma H2) in Hctx...
  Case "T_Let".
    inverts HF.
    destruct IHHt as [T' Hctx]... exists T'.
    rewrite (lookup_cons_vdecl_neq _ _ _ Gamma H2) in Hctx...
Qed.

(**  If a term is typable in the empty context it must be closed. *)

Corollary typable_empty__closed : forall t T, 
    empty |-- t \in T  ->
    closed t.
Proof.
  intros t T Hin x Hfree.
  apply free_in_context with (T:=T) (Gamma:=empty) in Hfree. 
  destruct Hfree. inversion H. assumption.
Qed.

(** *** Context Invariance theorem *)
(** If [Gamma] and [Gamma]' agree on all free variables of a term [t],
    the type of [t] is the same for both contexts. *)

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |-- t \in S  ->
     (forall x, appears_free_in x t -> 
                lookup_vdecl x Gamma = lookup_vdecl x Gamma') ->
     Gamma' |-- t \in S.
Proof with eauto 15.
  intros. generalize dependent Gamma'.
  set (Q := fun Gamma F L => 
      forall Gamma' : context,
      (forall x : id, appears_free_in_def x F -> 
                      lookup_vdecl x Gamma = lookup_vdecl x Gamma') ->
      def_yields Gamma' F L).
  set (QL := fun Gamma r RS => 
      forall Gamma' : context,
      (forall x : id, appears_free_in_pdefs x r -> 
                      lookup_vdecl x Gamma = lookup_vdecl x Gamma') ->
      Gamma' |-- r *\in RS).
  has_type_xind_tactic H Q QL Case; intros Gamma' Heqv; subst Q QL...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHHtb. intros y Hafi.
    unfold add_vdecl, lookup_vdecl. destruct (eq_id_dec x y)...
  Case "T_Let".
    apply T_Let with (L:=L)... apply IHHt. intros x Hafi.
    inversion HF as [? z tz Tz Hz]; subst...
    simpl. destruct (eq_id_dec z x)...
Qed.



(* ###################################################################### *)
(** *** Substitution preserves typing lemma *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     add_vdecl x U Gamma |-- t \in S  ->
     empty |-- v \in U   ->
     Gamma |-- ([x:=v]t) \in S.
Proof with eauto 15.
  (* Theorem: If Gamma,x:U |-- t : S and empty |-- v : U, then 
     Gamma |-- ([x:=v]t) S. *)
  intros Gamma x U v t S Htypt Htypv. 
  generalize dependent Gamma. generalize dependent S.
  (* Proof: By extended induction on the term t.  Most cases follow directly
     from the IHs, with the exception of tvar and tabs, which
     aren't automatic because we must reason about how the
     variables interact. *)

  set (Q := fun F =>
      forall (L : decl) (Gamma : context),
        def_yields (add_vdecl x U Gamma) F L -> 
        def_yields Gamma ([x:<=v]F) L).
  set (QL := fun Fs =>
      forall (RT : list decl) (Gamma : context),
        add_vdecl x U Gamma |-- Fs *\in RT -> 
        Gamma |-- ([x:<=v]* Fs) *\in RT).
  tm_xind_tactic t Q QL Case; intros S Gamma Htypt;  
    subst Q QL; inverts Htypt; try (simpl; eauto 15; fail).

  Case "tvar".
    rename x0 into y.
    (* If t = y, we know that
         [empty |-- v : U] and
         [Gamma,x:U |-- y : S]
       and, by inversion, [extend Gamma x U y = Some S].  We want to
       show that [Gamma |-- [x:=v]y : S].

       There are two cases to consider: either [x=y] or [x<>y]. *)
    simpl. destruct (eq_id_dec x y). 
    SCase "x=y".
    (* If [x = y], then we know that [U = S], and that [[x:=v]y = v].
       So what we really must show is that if [empty |-- v : U] then
       [Gamma |-- v : U].  We have already proven a more general version
       of this theorem, called context invariance. *)
      subst.
      rewrite (lookup_add_vdecl_eq y U Gamma) in H1. inverts H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |-- y : S] by [T_Var]. *)
      apply T_Var... 
      rewrite (lookup_add_vdecl_neq y x U Gamma n) in H1...

  Case "tabs".
    rename x0 into y. rename Tx into T1.
    (* If [t = tabs y T1 t0], then we know that
         [Gamma,x:U |-- tabs y T11 t0 : T1->T2]
         [Gamma,x:U,y:T1 |-- t0 : T2]
         [empty |-- v : U]
       As our IH, we know that forall S Gamma, 
         [Gamma,x:U |-- t0 : S -> Gamma |-- [x:=v]t0 S].
    
       We can calculate that 
         [x:=v]t = tabs y T11 (if beq_id x y then t0 else [x:=v]t0)
       And we must show that [Gamma |-- [x:=v]t : T11->T12].  We know
       we will do so using [T_Abs], so it remains to be shown that:
         [Gamma,y:T11 |-- if beq_id x y then t0 else [x:=v]t0 : T12]
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
      intros x Hafi. apply lookup_add_vdecl_shadow.
    SCase "x<>y".
    (* If [x <> y], then the IH and context invariance allow us to show that
         [Gamma,x:U,y:T1 |-- t : T2]       =>
         [Gamma,y:T11,x:U |-- t : T2]      =>
         [Gamma,y:T11 |-- [x:=v]t : T2] *)
      apply IHtb. eapply context_invariance...
      intros z Hafi. simpl. destruct (eq_id_dec y z)... 
      subst. rewrite neq_id...

  Case "tlet".
    destruct F as [z Tz].
    simpl. eapply T_Let.
      SCase "G |-- F yields L". apply (IHF _ _ H2). 
      SCase "G,L |-- t : T". inverts H2.
        destruct (eq_id_dec x z) as [Heq|Hne].
          SSCase "x=z". subst. 
            eapply context_invariance... intros x Hafi.
            simpl. destruct (eq_id_dec z x)...
          SSCase "x<>z".
            apply IHt.
            eapply context_invariance... intros y Hafi.
            simpl. 
            destruct (eq_id_dec z y); destruct (eq_id_dec x y); subst...
              destruct Hne; reflexivity.
Qed.

(** *** The Preservation Theorem *)
(** Preservation: if a closed
    term [t] has type [T], and takes an evaluation step to [t'], then [t']
    is also a closed term with type [T].  In other words, the small-step
    evaluation relation preserves types.
    Proof by induction on the derivation of [|-- t \in T].
*)
Theorem preservation : forall t t' T,
     empty |-- t \in T  ->
     t ==> t'  ->
     empty |-- t' \in T.
Proof with eauto.
  intros t t' T HT.
  (* Theorem: If [empty |-- t : T] and [t ==> t'], then [empty |-- t' : T]. *)
  remember (empty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many cases are
     contradictory ([T_Var], [T_Abs]) or follow directly from the IH
     ([T_RCons]).  We show just the interesting ones. *)
  set (Q := fun Gamma F L => forall F' : def,
       Gamma = empty -> 
       F >==> F' ->
       def_yields Gamma F' L).
  set (QL := fun Gamma Fs Ls => forall Fs' : list def,
       Gamma = empty -> 
       Fs *>==> Fs' ->
       Gamma |-- Fs' *\in Ls).
  has_type_xind_tactic HT Q QL Case;
    introv HeqGamma HE; subst; inverts HE; subst Q QL... 

  Case "T_App".
    (* If the last rule used was [T_App], then [t = t1 t2], and three rules
       could have been used to show [t ==> t']: [ST_App1], [ST_App2], and 
       [ST_AppAbs]. In the first two cases, the result follows directly from 
       the IH. *)
    SCase "ST_AppAbs".
      (* For the third case, suppose 
           [t1 = tabs x T11 t12]
         and
           [t2 = v2].  We must show that [empty |-- [x:=v2]t12 : T2]. 
         We know by assumption that
             [empty |-- tabs x T11 t12 : T1->T2]
         and by inversion
             [x:T1 |-- t12 : T2]
         We have already proven that substitution_preserves_typing and 
             [empty |-- v2 : T1]
         by assumption, so we are done. *)
      apply substitution_preserves_typing with T1...
      inversion Ht1...

  Case "T_Proj".
    (* If the last rule was [T_Proj], then [t = tproj t0 x] 
       where [t0 : (TRcd Tr)] and [lookup_vdecl x Tr = Some T]
       for some [t0], [x] and [Tr]. Two rules could have caused 
       [t ==> t']: [ST_Proj] and [ST_ProjRcd].  The typing
       of [t'] follows from the IH in the former case.

       In the [ST_ProjRcd] case, [t0 = (trcd r)] for some [r]
       where [is_value_rcd r] and [lookup_vdef x r = LetSome t'].
       Inverting Ht gives [r *: Tr] and we can apply lemma
       [rcd_field_lookup] to find the record element this
       projection steps to. *)
    inverts Ht.
    destruct (rcd_field_lookup _ _ _ _ H4 Hlk) as [vx [ Hlxr Htx]].
    rewrite H3 in Hlxr. inversion Hlxr...

  Case "T_Let".
    (* If the last rule was [T_Let], then [t = tlet F t'] 
       where [F yields L] and [L |-- t : T].
       Two rules could have caused [t ==> t']: [ST_Let] and [ST_LetDef].  
       The first case is handled automatically since it follows from the IH.

       In the [ST_LetDef] case, [t = tlet (Fv x vx) t2] (where vx is a value).
       This steps to [[x:=vx]t2] which has type [T] since [vx:T0] (H4) and
       [x:T0 |-- t:T] (Ht). *)
    inverts HF.
    apply substitution_preserves_typing with T0...
Qed.

(* ###################################################################### *)
(** ** Type Soundness *)

(** Progress and preservation together imply that a well-typed
    term can _never_ reach a stuck state.  *)

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ is_value t.

Corollary soundness : forall t t' T,
  empty |-- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti as [ x | x y z Hxy].
    Case "multi_refl: x==>x". 
      (* The progress theorem says that this can't happen *)
      destruct (progress _ _ Hhas_type); auto.
    Case "multi_step: x==>y, y==>*z". 
      apply IHHmulti; try assumption.
      apply (preservation _ _ _ Hhas_type Hxy).
Qed.
