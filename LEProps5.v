(** * Another version of LEProps.  Seems like the value_has_type definition is incomplete.*)

Add LoadPath "~/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

Require Export LDef LEval.
Import LDEF.
Import LEVAL.

Module LEProps.

(* ###################################################################### *)
(**  *value_has_type *)
(* Reserved Notation "v '\in' T" (at level 40). *)

(*
Inductive value_has_type_new : evalue -> ty -> Prop :=
  | VHT : forall t T v, \empty |- t \in T -> eval t anil v -> value_has_type_new v T.

Lemma vbool : forall v, value_has_type_new v TBool -> (v =vtrue \/ v = vfalse).
Proof. intros v Hv. inverts Hv.   
   remember \empty as G. generalize dependent G. induction H; subst; try (solve by inversion). inverts H1.
*)

Inductive value_has_type : evalue -> ty -> Prop :=
  | TV_Abs : forall va vf T1 T2,
        value_has_type va T1 -> vapp vf  va T2 -> value_has_type vf (TArrow T1 T2)
  | TV_True : 
        value_has_type vtrue TBool
  | TV_False : 
        value_has_type vfalse TBool
with rtcontext_has_type: rctx -> context -> Prop :=
  | TC_nil : rtcontext_has_type anil empty
  | TC_cons : forall G g x v T, 
    rtcontext_has_type g G -> 
      value_has_type v T ->
      rtcontext_has_type (acons x v g) (extend G x T)
with vapp : evalue -> evalue -> ty -> Prop :=
  | TVApp : forall va T2 tf xf gf vr,
      
      eval tf (acons xf va gf) vr ->
      value_has_type vr T2 -> 
         vapp (vabs xf tf gf) va T2.


Inductive value_has_form : evalue -> ty -> Prop :=
  | TV_Abs' : forall xf tf gf T1 T2,
          value_has_form (vabs xf tf gf) (TArrow T1 T2) 
  | TV_True' : 
        value_has_form vtrue TBool
  | TV_False' : 
        value_has_form vfalse TBool.


(***** HERE ***)

(* where "v '\in' T" := (value_has_type v T). *)

Tactic Notation "value_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TV_Abs" | Case_aux c "TV_True" | Case_aux c "TV_False" ].

Tactic Notation "rtcontext_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TC_nil" | Case_aux c "TC_cons"  ].

Hint Constructors value_has_type rtcontext_has_type.

Lemma bool_vals : forall v, value_has_type v TBool -> (v=vtrue \/ v=vfalse).
Proof. intros v Hv. inversion Hv; auto. Qed.

Lemma fun_vals: forall v T1 T2, value_has_type v (TArrow T1 T2) ->
  exists xf tf gf, v = vabs xf tf gf (***** HERE ***).
Proof.
  introv H. inversion H. subst. inversion H4. exists xf tf gf. reflexivity.
Qed.


(** * tests *)
Example e_not_T: exists v, eval f_not rctx0 v /\ value_has_type v (TArrow TBool TBool).
Proof.
  eexists.  unfold f_not. eauto 10. (*Hint Resolve fun_vals. eauto 10.*)

     split.
      eapply E_Abs.
      eapply TV_Abs. eapply (TVApp4 _ TBool TBool (tif (tvar id_b) tfalse ttrue) id_b rctx0 _). intros va. eexists. split.
        skip. 
        eapply E_If. 
          eapply E_Var. eauto. 
          skip.
Abort All.
 *)
Qed.


Example e_f_pair_T: exists v, 
  eval f_pair rctx0 v /\ 
    value_has_type v (TArrow TBool (TArrow TBool (TArrow TBool TBool))).
Proof.
  eexists. split.
    unfold f_pair. eauto. eauto 10.
    (* apply TV_Abs. eexists. split; eauto. eauto 8 using has_type. *)
Qed. Hint 

(* ###################################################################### *)
(**  *ctxts_gx_then_alookup *)


Lemma ctxts_gx_then_alookup : 
  forall (x : id) (G : context) (g : rctx) (T : ty),
    rtcontext_has_type g G -> 
    G x = Some T ->
      exists v, alookup x g = Some v /\ value_has_type v T.
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
  G |- (tvar x) \in T -> rtcontext_has_type g G -> 
    exists v, alookup x g = Some v /\ value_has_type v T.
Proof. introv HG Hg. apply (ctxts_gx_then_alookup x G g T Hg). apply lemma1. assumption. Qed.

Lemma lemma3 : forall G x T g,
  G |- (tvar x) \in T -> rtcontext_has_type g G -> 
    exists v, eval (tvar x) g v /\ value_has_type v T.
Proof. introv HG Hg. destruct (lemma2 G x T g HG Hg) as [v [Hl Hv]]. exists v. auto. Qed.

Theorem bigstep_soundness :
  forall (G : context) (t : tm) (T : ty),
    G |- t \in T -> 
      forall (g : rctx), rtcontext_has_type g G -> 
        exists (v : evalue), 
          eval t g v
          /\ value_has_type v T.
Proof.
  intros G t T. generalize dependent T. generalize dependent G.
  t_cases (induction t) Case; intros G T Hty g Hg. 
    Case "tvar". destruct (lemma3 G i T g Hty Hg) as [v [Hl Hv]]. exists v. auto. 
    Case "tapp". inversion Hty; subst; clear Hty.
      apply IHt1 with (g:=g) in H2; clear IHt1. destruct H2 as [v1 [He1 Hv1]].
      apply IHt2 with (g:=g) in H4; clear IHt2. destruct H4 as [v2 [He2 Hv2]].
      eexists. split.
        inversion Hv1; subst; clear Hv1. destruct H1 as [Gf [HTGf HTtf]].
        eapply (E_App t1 t2 tf xf v2 _ g gf).
            eapply He1. apply He2.

     
      assert (HHH: exists (vr : evalue), eval tf (acons xf v2 gf) vr /\ value_has_type vr T).
 
        apply bigstep_soundness with (G:=(extend Gf xf T11)).

      destruct (Htf v2 Hv2) as [vr [Hvr Hetf]]. clear Htf.
      exists vr. split. eapply E_App. apply He1. apply He2. apply Hetf. 
      assumption. assumption. assumption.

      Hv1eq  ::=  intros va HTva. destruct H1 as [Gf [HTGf HTtf]].
      Htf  ::=  apply bigstep_soundness with (G:=(extend Gf xf T11)). auto. auto.


    destruct (fun_vals' v1 T11 T Hv1) as [xf [ tf  [gf [Hv1eq Htf]]]]. subst.



inversion Hty; subst; clear Hty; eauto


(* with  fun_vals': forall v T1 T2, value_has_type v (TArrow T1 T2) ->
  exists xf tf gf, v = vabs xf tf gf /\   
    ( forall (va : evalue),  value_has_type va T1 -> 
            exists (vr : evalue), eval tf (acons xf va gf) vr /\ value_has_type vr T2 ).
  Case "fun_vals".
    introv Hv. inversion Hv1; subst; clear Hv1.. exists xf tf gf. split. auto.
      intros va HTva. destruct H1 as [Gf [HTGf HTtf]].
      apply bigstep_soundness with (G:=(extend Gf xf T1)). auto. auto.
*)
(*
    SCase "tvar". destruct (lemma3 G i T g Hty Hg) as [v [Hl Hv]]. exists v. auto. 
    SCase "tapp". inversion Hty; subst; clear Hty.
      apply IHt1 with (g:=g) in H2; clear IHt1. destruct H2 as [v1 [He1 Hv1]].
      destruct (fun_vals' v1 T11 T Hv1) as [xf [ tf  [gf [Hv1eq Htf]]]]. subst.
      apply IHt2 with (g:=g) in H4. clear IHt2; destruct H4 as [v2 [He2 Hv2]].
      destruct (Htf v2 Hv2) as [vr [Hvr Hetf]]. clear Htf.
      exists vr. split. eapply E_App. apply He1. apply He2. apply Hetf. 
      assumption. assumption. assumption.
   SCase "tabs". inversion Hty; subst; clear Hty.
      eexists. split. eapply E_Abs. apply TV_Abs. exists G. auto.
  SCase "ttrue". eexists. split. econstructor. inversion Hty; subst; clear Hty.  econstructor.
  SCase "tfalse". inversion Hty; subst; clear Hty. eauto. 
  SCase "tif". inversion Hty; subst; clear Hty. eauto. 
*)
Qed.


(* ALMOST OK:
Theorem bigstep_soundness :
  forall (G : context) (t : tm) (T : ty),
    G |- t \in T -> 
      forall (g : rctx), rtcontext_has_type g G -> 
        exists (v : evalue), 
          eval t g v
          /\ value_has_type v T
with  fun_vals': forall v T1 T2, value_has_type v (TArrow T1 T2) ->
  exists xf tf gf, v = vabs xf tf gf /\   
    ( forall (va : evalue),  value_has_type va T1 -> 
            exists (vr : evalue), eval tf (acons xf va gf) vr /\ value_has_type vr T2 ).
Proof.
  Case "bigstep_soundness". 
  intros G t T. generalize dependent T. generalize dependent G.
  t_cases (induction t) SCase; intros G T Hty g Hg; inversion Hty; subst; clear Hty; eauto. 
(*
    SCase "tvar". destruct (lemma3 G i T g Hty Hg) as [v [Hl Hv]]. exists v. auto. 
    SCase "tapp". inversion Hty; subst; clear Hty.
      apply IHt1 with (g:=g) in H2; clear IHt1. destruct H2 as [v1 [He1 Hv1]].
      destruct (fun_vals' v1 T11 T Hv1) as [xf [ tf  [gf [Hv1eq Htf]]]]. subst.
      apply IHt2 with (g:=g) in H4. clear IHt2; destruct H4 as [v2 [He2 Hv2]].
      destruct (Htf v2 Hv2) as [vr [Hvr Hetf]]. clear Htf.
      exists vr. split. eapply E_App. apply He1. apply He2. apply Hetf. 
      assumption. assumption. assumption.
   SCase "tabs". inversion Hty; subst; clear Hty.
      eexists. split. eapply E_Abs. apply TV_Abs. exists G. auto.
  SCase "ttrue". eexists. split. econstructor. inversion Hty; subst; clear Hty.  econstructor.
  SCase "tfalse". inversion Hty; subst; clear Hty. eauto. 
  SCase "tif". inversion Hty; subst; clear Hty. eauto. 
*)
  Case "fun_vals".
    introv Hv. inversion Hv; subst; clear Hv. exists xf tf gf. split. auto.
      intros va HTva. destruct H1 as [Gf [HTGf HTtf]].
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
  intros v T1 T2 Hv.  inverts Hv. exists xf tf gf. split; auto.
    intros va Hva.
*)


End BigStepSubst.