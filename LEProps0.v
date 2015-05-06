(** * Lemmas for soundness proofs*)

(**  This file has lemmas for use in other experiments, LEPropsN.v.
      It attempts to use Coq module types to abstract out the particular 
      definitions of [value_has_type] and friends. However, the use of 
      modules creates awkwardness in proving, so this file is only 
      used by LEProps1.v.
*)

Add LoadPath "~/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

Require Export LDef LEval.
Import LDEF.
Import LEVAL.

Module Type HAS_TYPE_DEF.

Parameter value_has_type : evalue -> ty -> Prop.
Parameter rtcontext_has_type: rctx -> context -> Prop.
Parameter evaluates_to : tm -> rctx ->  ty -> Prop.

Parameter rtcontext_has_type_ind :
  forall P : rctx -> context -> Prop,
  P anil \empty ->
  (forall (G : context) (g : rctx) (x : id) (v : evalue) (T : ty),
    rtcontext_has_type g G -> P g G -> value_has_type v T -> 
      P (acons x v g) (extend G x T)) ->
  forall (r : rctx) (c : context), rtcontext_has_type r c -> P r c.

End HAS_TYPE_DEF.


Module LECoreProps (HTD : HAS_TYPE_DEF).

(* ###################################################################### *)

(**  ** key lemmas *)
(**  *** ctxts_gx_then_alookup *)

Notation "v ':::' T" := (HTD.value_has_type v T) (at level 40) .
Notation "g ':::*' G" := (HTD.rtcontext_has_type g G) (at level 40).
Notation "t '/' g '|:' T"  := (HTD.evaluates_to t g T) (at level 40, g at level 39). 

Lemma ctxts_gx_then_alookup : 
  forall (x : id) (G : context) (g : rctx) (T : ty),
    g  :::* G -> 
    G x = Some T ->
      exists v, alookup x g = Some v /\ v ::: T.
Proof.
  introv Hctxts HGxT. induction Hctxts using HTD.rtcontext_has_type_ind.
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

Lemma ctx_tvar_then_some : forall G x T,
  G |- (tvar x) \in T -> G x = Some T.
Proof. introv H. inversion H. auto. Qed.

Lemma ctx_tvar_then_alookup : forall G x T g,
  G |- (tvar x) \in T -> g :::* G -> 
    exists v, alookup x g = Some v /\ v ::: T.
Proof. 
  introv HG Hg. apply (ctxts_gx_then_alookup x G g T Hg). 
  apply ctx_tvar_then_some. assumption. 
Qed.

Lemma eval_var_T : forall G x T g,
  G |- (tvar x) \in T -> g :::* G -> 
    exists v, eval (tvar x) g v /\ v ::: T.
Proof. introv HG Hg. destruct (ctx_tvar_then_alookup G x T g HG Hg) as [v [Hl Hv]]. exists v. auto. Qed.


End LECoreProps.