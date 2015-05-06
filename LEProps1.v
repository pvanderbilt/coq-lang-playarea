(** * LEProps1: Properties of LEval (a big-step semantics for LDef) *)

(**  V1: An attempt at soundness of eval using a [value_has_type]
      relation with several variations (commented out).  However, this version uses the
      eval relation and doesn't take non-termination into account.  The theorem goes through only
      because of a [fun_vals] lemma that is admitted (faked). *)

Add LoadPath "~/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

Require Export LDef LEval LEProps.
Import LDEF.
Import LEVAL.

Module ValueHasType1 <: HAS_TYPE_DEF.

(* ###################################################################### *)

(**  ** value_has_type *)

Reserved Notation "v ':' T" (at level 40).
Reserved Notation "g ':*' G" (at level 40).
Reserved Notation "t '/' g '|:' T" (at level 40, g at level 39).

Inductive value_has_type' : evalue -> ty -> Prop :=
  | TV_Abs : forall xf tb gf T1 T2,
(* 
         ( forall (va : evalue),  va : T1 -> tb / (acons xf va gf) |: T2) -> 
          vabs xf tb gf : TArrow T1 T2  *)
(* 
        ( forall ta G g va, G |- ta \in T1 -> (* g :* G -> *) ta / g || va -> tb (acons xf va gf) |: T2 ) -> 
          vabs xf tb gf : TArrow T1 T2 *)
        (* (exists (Gf : context), gf :* Gf /\ extend Gf xf T1 |- tb \in T2) ->  *)
(*         forall Gf, gf :* Gf ->
          (extend Gf xf T1 |- tb \in T2) ->
          (forall g, g :* (extend Gf xf T1) -> tb / g |: T2) -> *)
(*           ( forall va,  va : T1 -> tb / (acons xf va gf) |: T2 ) -> *)
              vabs xf tb gf : TArrow T1 T2
  | TV_True : vtrue : TBool
  | TV_False : vfalse : TBool

with rtcontext_has_type': rctx -> context -> Prop :=
  | TC_nil : anil :* empty
  | TC_cons : forall G g x v T, g :* G -> v : T -> acons x v g :* extend G x T

with evaluates_to' : tm -> rctx -> ty -> Prop := 
   | TVE : forall t g T, (exists v, t / g || v /\ v : T) -> t / g |: T
   (* TVE : forall t g T v, t / g || v -> v : T -> t / g |: T *)

where "v ':' T" := (value_has_type' v T)
 and "g ':*' G" := (rtcontext_has_type' g G)
 and "t '/' g '|:' T" := (evaluates_to' t g T) .

Tactic Notation "value_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TV_Abs" | Case_aux c "TV_True" | Case_aux c "TV_False" ].

Tactic Notation "rtcontext_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TC_nil" | Case_aux c "TC_cons"  ].

Hint Constructors value_has_type' rtcontext_has_type' evaluates_to'.

Definition value_has_type := value_has_type'.
Definition rtcontext_has_type := rtcontext_has_type'.
Definition evaluates_to := evaluates_to'.
Definition rtcontext_has_type_ind := rtcontext_has_type'_ind.

Hint Resolve TVE. 

End ValueHasType1.

Module LECoreP := LECoreProps ValueHasType1.

Module LEProps1.

Import ValueHasType1.
Import LECoreP.
(**  ** key lemmas *)

Lemma bool_vals : forall v, v ::: TBool -> (v=vtrue \/ v=vfalse).
Proof. intros v Hv. inversion Hv; auto. Qed.

Lemma bool_vals' : forall v, (v=vtrue \/ v=vfalse) -> v : TBool.
Proof. intros v Hv. inversion Hv; subst; auto. Qed.

Lemma fun_vals: forall v T1 T2, v : TArrow T1 T2 ->
  exists xf tb gf, v = vabs xf tb gf (* added *) /\
    forall va,  va : T1 -> tb / (acons xf va gf) |: T2
      (* exists vr, tb / (acons xf va gf) || vr /\  vr : T2 *)
    (***** HERE ***). 
Proof.
  (* introv H. inverts H. exists xf tb gf. (* was: reflexivity. *) split. reflexivity.
    intros va Hva. *)
    admit.    (*  !!! *)
Qed.

Lemma fun_vals': forall v T1 T2,  
  ( exists xf tb gf, v = vabs xf tb gf (* added *) /\
    forall va,  va : T1 -> tb / (acons xf va gf) |: T2 ) -> v : TArrow T1 T2.
Proof.
    admit.    (*  !!! *)
Qed.

Lemma fun_vals'': forall T1 T2 xf tb gc,
    ( forall va,  va : T1 -> tb / (acons xf va gc) |: T2 ) -> (vabs xf tb gc) : TArrow T1 T2.
Proof.
  introv H. apply fun_vals'. exists xf tb gc. auto.
Qed.


(** * tests *)
Example e_not_T: f_not / rctx0 |: (TArrow TBool TBool).
Proof. eauto 15 using TVE.
  apply TVE. eauto 15.
(*eexists. split.
      eapply E_Abs.
      eapply TV_Abs. intros va. eexists. split.
        skip. 
        eapply E_If. 
          eapply E_Var. eauto. 
          skip.
Abort All.
 *)
Qed.

Hint Resolve TVE.
Example e_f_pair_T: f_pair / rctx0 |: TArrow TBool (TArrow TBool (TArrow TBool TBool)).
Proof. apply TVE. info_eauto 15.
    (* apply TV_Abs. eexists. split; eauto. eauto 8 using has_type. *)
Qed.

(* ###################################################################### *)
(**  ** ctxts_gx_then_alookup *)


(* 
Lemma ctxts_gx_then_alookup : 
  forall (x : id) (G : context) (g : rctx) (T : ty),
    g :* G -> 
    G x = Some T ->
      exists v, alookup x g = Some v /\ v : T.
Proof.
  introv Hctxts HGxT. rtcontext_has_type_cases (induction Hctxts) Case.
    Case "TC_nil". inversion HGxT.
    Case "TC_cons". unfold extend in HGxT. destruct (eq_id_dec x0 x).
      SCase "x=x0". inversion HGxT; subst; clear HGxT. exists v. split.
        simpl. apply eq_id.
        assumption.
      SCase "x0<>x". apply IHHctxts in HGxT. clear IHHctxts.
        inversion HGxT as [v' [Ha' Hb']]. exists v'. split.
          rewrite <- Ha'. simpl. apply (neq_id _ _ _ _ _ n).
          assumption.
Qed.

Lemma lemma1 : forall G x T,
  G |- (tvar x) \in T -> G x = Some T.
Proof. introv H. inversion H. auto. Qed.

Lemma lemma2 : forall G x T g,
  G |- (tvar x) \in T -> g :* G -> 
    exists v, alookup x g = Some v /\ v : T.
Proof. introv HG Hg. apply (ctxts_gx_then_alookup x G g T Hg). apply lemma1. assumption. Qed.

Lemma lemma3 : forall G x T g,
  G |- (tvar x) \in T -> g :* G -> 
    exists v, eval (tvar x) g v /\ v : T.
Proof. introv HG Hg. destruct (lemma2 G x T g HG Hg) as [v [Hl Hv]]. exists v. auto. Qed.
 *)
Hint Constructors value_has_type' rtcontext_has_type' evaluates_to'.
Hint Resolve TVE. 
Theorem bigstep_soundness :
  forall (G : context) (t : tm) (T : ty),
    G |- t \in T -> 
      forall (g : rctx), g :* G -> t / g |: T.
Proof.
  intros G t T. generalize dependent T. generalize dependent G.
  t_cases (induction t as [ x | t1 ? t2 ? | x Tx tb | | | ti ? tt ? te ? ]) Case; intros G T Hty g Hg;
        inversion Hty; subst; apply TVE; eauto.
    Case "tvar". (* eauto using eval_var_T. *)
      destruct (eval_var_T G x T g Hty Hg) as [v [Hl Hv]]. exists v. auto.
    Case "tapp".
      (* first get the values computed by t1 and t2 using the induction hypotheses  *)
      apply IHt1 with (g:=g) in H2; try apply Hg. inverts H2 as [v1 [He1 Hv1]]; clear IHt1.
      apply IHt2 with (g:=g) in H4; try apply Hg. inverts H4 as [v2 [He2 Hv2]]; clear IHt2.
      (* At this point, there are values v1 and v2 and hypotheses about their runtime 
          types & eval.  The goal is
                tapp t1 t2 / g |: T
          which reduces to 
                exists vr, tapp t1 t2 / g || vr /\ vr : T .
          We can try eapply and eexists tactics, but end up with "Impossible to unify",
          so it seems better to figure out what is the result, v. This comes down to
          deriving 
                exists vr, (apply v1 v2 vr) /\ vr : T
          from "v1 : TArrow T11 T" and "v2 : T11".
          In the following, the bogus [fun_vals] lemma above is used.  Somehow 
          TV_Abs needs to be strenghtened to give the [fun_vals] lemma (or be it).
      *)
      destruct (fun_vals _ _ _ Hv1) as [xf [tb [gf [? Hfun]]]]; subst; clear Hv1. 
      (*
          Hfun comes from the [fun_vals] lemma applied to "v1 : TArrow T11 T".
          It is now applied to "v2 : T11":
      *)
      apply Hfun in Hv2. inversion Hv2 as [? ? ? [vr [Her Hvr]]]; subst; clear Hv2 Hfun. 
      (* alt that used to work: destruct (Hfun v2 Hv2) as [ vr [Her Hvr] ]; clear Hfun Hv2. *)
      exists vr. exact (conj (E_App t1 t2 _ v2 _ g He1 He2 (EA xf tb gf _ _ Her)) Hvr).
    (* With the current definition of value_has_type, the "tabs" case is so trivial it doesn't show up. 
    Case "tabs". (* clear IHt.  The IH is NOT BEING USED*) 
      apply TVE. eexists. split. eapply E_Abs. apply TV_Abs.
      (* apply (fun_vals'' _ _ _ _ _ (fun va Hva => (IHtb _ _ H4 _ (TC_cons _ _ _ _ _ Hg Hva)))).*)
      (* old: apply TVE. eexists. split. eapply E_Abs. apply TV_Abs. exists G. auto. *)  *)
    Case "tif".
      apply IHt1 with (g:=g) in H3; try apply Hg. inverts H3 as [vb [? Hvb]]; clear IHt1.
      apply IHt2 with (g:=g) in H5; try apply Hg. inverts H5 as [vt [? Hvt]]; clear IHt2.
      apply IHt3 with (g:=g) in H6; try apply Hg. inverts H6 as [ve [? Hve]]; clear IHt3.
      destruct (bool_vals vb Hvb); subst; eauto 10.
Qed.

(* This one using induction on the typing derivation: *)

Theorem bigstep_soundness' :
  forall (G : context) (t : tm) (T : ty),
    G |- t \in T -> 
      forall (g : rctx), g :* G -> t / g |: T.
Proof.
  intros G t T Hty. has_type_cases (induction Hty) Case; intros g Hg;  apply TVE; eauto.
    Case "T_Var". eauto using eval_var_T.
(*     Case "T_Abs". intros  g Hg.  apply TVE. eexists. split. eapply E_Abs. apply TV_Abs. 
 *)      (* exists Gamma. split. apply Hg. apply Hty. (* didn't use IH *) *)
    Case "T_App". 
      set (Htmp := (IHHty1 g Hg)). inverts Htmp as [v1 [Htv1 HT1]]. clear IHHty1.
      set (Htmp := (IHHty2 g Hg)). inverts Htmp as [v2 [Htv2 HT2]]. clear IHHty2.
      (* was: assert (He1 : t1 / g |: TArrow T11 T12). apply IHHty1. assumption. inverts He1 as [ v1 [Htv1 HT1]].
                  assert (He2 : t2 / g |: T11). apply IHHty2. assumption. inverts He2 as [ v2 [Htv2 HT2]]. *)
      destruct (fun_vals v1 _ _ HT1) as [xf [ tb [ gf [? Hfun]]]]; subst.  (* BOGUS *)
      apply Hfun in HT2. inverts HT2 as [vr [Her Hvr]]. clear Hfun.
      exists vr. apply (conj (E_App _ _ _ v2 _ _ Htv1 Htv2 (EA _ _ _ _ _ Her)) Hvr). 
    Case "T_If".
      set (Htmp := (IHHty1 g Hg)). inverts Htmp as [vi [? Hvi]].
      set (Htmp := (IHHty2 g Hg)). inverts Htmp as [vt [? Hvt]].
      set (Htmp := (IHHty3 g Hg)). inverts Htmp as [ve [? Hve]].
      clear IHHty1 IHHty2 IHHty3.
      destruct (bool_vals vi Hvi); subst; eauto 10.
Qed.

(* This one using my custom induction principal *)
Require Export LInduction.

Import LInduction.

Theorem bigstep_soundness'' :
  forall (G : context) (t : tm) (T : ty),
    G |- t \in T -> 
      forall (g : rctx), g :* G -> t / g |: T.
Proof.
  intros G t T Hty.
  t_cases (induction Hty using  tm_ind_with_ty_inv) Case; intros g Hg;  apply TVE; eauto.
  (* t_cases (refine (tm_ind_with_ty_inv (fun G t T => forall g : rctx, g :* G -> t / g |: T) 
            _ _ _ _ _ _ G t T Hty)) Case; clear G t T Hty.*)
    Case "tvar". eauto using eval_var_T.
    Case "tapp". 
      set (Htmp := (IHHty1 g Hg)). inverts Htmp as [v1 [Htv1 HT1]]. clear IHHty1.
      set (Htmp := (IHHty2 g Hg)). inverts Htmp as [v2 [Htv2 HT2]]. clear IHHty2.
      destruct (fun_vals v1 _ _ HT1) as [xf [ tb [ gf [? Hfun]]]]; subst.  (* BOGUS *)
      apply Hfun in HT2. inverts HT2 as [vr [Her Hvr]]. clear Hfun.
      exists vr. apply (conj (E_App _ _ _ v2 _ _ Htv1 Htv2 (EA _ _ _ _ _ Her)) Hvr).
    (* Case "tabs". 
      introv He IHe Hg.  apply TVE. eexists. split. eapply E_Abs. apply TV_Abs.
      (* didn't use IH *) *)
    Case "tif".
      set (Htmp := (IHHty1 g Hg)). inverts Htmp as [vi [? Hvi]].
      set (Htmp := (IHHty2 g Hg)). inverts Htmp as [vt [? Hvt]].
      set (Htmp := (IHHty3 g Hg)). inverts Htmp as [ve [? Hve]].
      clear IHHty1 IHHty2 IHHty3.
      destruct (bool_vals vi Hvi); subst; eauto 10.
Qed.

(* ALMOST OK:
Theorem bigstep_soundness :
  forall (G : context) (t : tm) (T : ty),
    G |- t \in T -> 
      forall (g : rctx), g :* G -> 
        exists (v : evalue), 
          eval t g v
          /\ v : T
with  fun_vals': forall v T1 T2, value_has_type v (TArrow T1 T2) ->
  exists xf tb gf, v = vabs xf tb gf /\   
    ( forall (va : evalue),  value_has_type va T1 -> 
            exists (vr : evalue), eval tb (acons xf va gf) vr /\ value_has_type vr T2 ).
Proof.
  Case "bigstep_soundness". 
  intros G t T. generalize dependent T. generalize dependent G.
  t_cases (induction t) SCase; intros G T Hty g Hg; inversion Hty; subst; clear Hty; eauto. 
(*
    SCase "tvar". destruct (lemma3 G i T g Hty Hg) as [v [Hl Hv]]. exists v. auto. 
    SCase "tapp". inversion Hty; subst; clear Hty.
      apply IHt1 with (g:=g) in H2; clear IHt1. destruct H2 as [v1 [He1 Hv1]].
      destruct (fun_vals' v1 T11 T Hv1) as [xf [ tb  [gf [Hv1eq Htb]]]]. subst.
      apply IHt2 with (g:=g) in H4. clear IHt2; destruct H4 as [v2 [He2 Hv2]].
      destruct (Htb v2 Hv2) as [vr [Hvr Hetb]]. clear Htb.
      exists vr. split. eapply E_App. apply He1. apply He2. apply Hetb. 
      assumption. assumption. assumption.
   SCase "tabs". inversion Hty; subst; clear Hty.
      eexists. split. eapply E_Abs. apply TV_Abs. exists G. auto.
  SCase "ttrue". eexists. split. econstructor. inversion Hty; subst; clear Hty.  econstructor.
  SCase "tfalse". inversion Hty; subst; clear Hty. eauto. 
  SCase "tif". inversion Hty; subst; clear Hty. eauto. 
*)
  Case "fun_vals".
    introv Hv. inversion Hv; subst; clear Hv. exists xf tb gf. split. auto.
      intros va HTva. destruct H1 as [Gf [HTGf HTtb]].
      apply bigstep_soundness with (G:=(extend Gf xf T1)). auto. auto.
Qed.
*)
(*
destruct (ctxts_gx_then_alookup _ _ _ _ Hg H).
apply ctxts_gx_then_alookup. eexists. split. constructor. eauto.

has_type_cases (induction Hty) SCase; intros  g Hg.
    SCase "T_Var". (* x *) destruct (ctxts_gx_then_alookup _ _ _ _ Hg H) as [v [He Hv]].
      exists (v). auto.
    SCase "T_Abs". (* x T11 T12 *) destruct (IHHty 

eexists. split.
      eapply E_Abs.
      apply TV_Abs. exists Gamma. auto.
    SCase "T_App". 
      destruct (IHHty1 g Hg) as [v1 [He1 Ht1]]; clear IHHty1.
      destruct (IHHty2 g Hg) as [v2 [He2 Ht2]]; clear IHHty2. 
      inversion Ht1; subst; clear Ht1. eexists. split. 
        eapply E_App.
          eapply He1.
          eapply He2.
          destruct H1 as [G [HGg HGT]]. clear He1 He2.


Abort All.
  Case "fun_vals'". 
  intros v T1 T2 Hv.  inverts Hv. exists xf tb gf. split; auto.
    intros va Hva.
*)


End LEProps1.