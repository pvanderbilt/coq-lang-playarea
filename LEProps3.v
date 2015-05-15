(** * An attempt at soundness of [evalF]  
    This file contains an attempt at proving the soundness of [evalF] 
    (the big-step evaluation function defined in [Leval.v]).
    However, a key definition is not allowed due to Coq's positivity restriction.

    To get around this, lemmas are defined to fake the desired definition
    and a proof goes through.*)

Add LoadPath "~/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

Require Export Common LDef LEval.
Import P3Common LDEF LEVAL.

Module LEProps3.

(* ###################################################################### *)

Reserved Notation "v ':::' T" (at level 40).
Reserved Notation "g ':::*' G" (at level 40).
Reserved Notation "t '/' g '=>:' T" (at level 40, g at level 39).


(** The definitions below define relations that relate [evalF], values and types.
    However, they don't work.  In the [TV_Abs] case of [value_has_type], I want 

[[
  forall xf tb gf T1 T2,
    ( forall va,  va ::: T1 -> tb / (acons xf va gf) =>: T2 ) ->
      vabs xf tb gf ::: TArrow T1 T2
]]

    However, this isn't accepted because of a "Non strictly positive occurrence" error
    due to [va ::: T1 ] being to the left of an implication.
    Below I provide lemmas that fake this behavior, and it seems that the soundness proof goes through.

    Some alternative that I've tried:

     -  [(exists Gf , gf :::* Gf /\ extend Gf xf T1 |- tb \in T2) ->]#<br/>#
        [    vabs xf tb gf ::: TArrow T1 T2]

        This is accepted but gets to a state in the [tapp] case where the context has:
            - [Hv2t : v2 ::: T11]
            - [Hevf : evalF tb (acons xf v2 gf) n' = erf]
            - [HGgf : gf :::* Gf]
            - [Htbt : extend Gf xf T11 |- tb \in T]
        It seems that this needs the inductive hypothesis from the [tabs] case.

     -  [(exists Gf, gf :::* Gf /\ Gf |- (tabs xf T1 tb) \in TArrow T1 T2 ) -> ...]

        This is accepted but is similar to the one above.

     -  [( forall ta G g va n, G |- ta \in T1 ->  g :::* G -> ]#<br/>#
          [    evalF ta g n = efr_normal va -> ]#<br/>#
          [    tb / (acons xf va gf) =>: T2 ) -> ...]

        This is not accepted because of the [gf :::* Gf ]clause. 
        This makes sense as the first line is another way to say [va ::: T1] (given soundness).
*)

Inductive value_has_type : evalue -> ty -> Prop :=
  | TV_Abs : forall xf tb gf T1 T2,
     (* As discussed above, I want the following premise, but it's rejected as a "Non strictly positive occurrence".
         ( forall va,  va ::: T1 -> tb / (acons xf va gf) =>: T2 ) ->
      *)
               vabs xf tb gf ::: TArrow T1 T2
  | TV_True : vtrue ::: TBool
  | TV_False : vfalse ::: TBool

with rtcontext_has_type: rctx -> context -> Prop :=
  | TC_nil : nil :::* empty
  | TC_cons : forall G g x v T, 
                g :::* G -> v ::: T -> (aextend x v g) :::* extend G x T

with evaluates_to_a : tm -> rctx ->  ty -> Prop := 
   | TVE : forall t g T,  
             (forall n, result_ok (evalF t g n) T) -> (t / g =>: T)

with result_ok : ef_return -> ty -> Prop :=
  | TR_NG : forall (T : ty), result_ok efr_nogas T
  | TR_Norm : forall (vr : evalue) (T : ty),  
                vr ::: T ->  result_ok (efr_normal vr) T

where "v ':::' T" := (value_has_type v T)
 and "g ':::*' G" := (rtcontext_has_type g G)
 and "t '/' g '=>:' T" := (evaluates_to_a t g T) .

Hint Constructors value_has_type rtcontext_has_type evaluates_to_a result_ok.

(** ** Lemmas for faking the desired behavior of TV_Abs. *)

Lemma fake_vht_arrow_inversion:
  forall T1 T2 v, v ::: TArrow T1 T2 ->
    exists xf tb gf, v = (vabs xf tb gf) /\ 
                  (forall va, va ::: T1 -> tb / (aextend xf va gf) =>: T2).
Proof. admit. Qed.

Lemma fake_TV_Abs:  
      forall (xf : id) (tb : tm) (gf : alist evalue) (T1 T2 : ty), 
          (forall va, va ::: T1 -> tb / (aextend xf va gf) =>: T2) ->
          vabs xf tb gf ::: TArrow T1 T2.
Proof. admit. Qed.


(* Copies of lemmas from LEProps. *)

Lemma ctxts_agree_on_lookup : 
  forall (x : id) (G : context) (g : rctx) (T : ty),
    g  :::* G -> 
    lookup_vdecl x G = Some T ->
      exists v, alookup x g = Some v /\ v ::: T.
Proof.
  introv Hctxts HGxT. induction Hctxts.
    Case "TC_nil". inversion HGxT.
    Case "TC_cons". unfold lookup_vdecl, extend in HGxT. 
    destruct (eq_id_dec x0 x).
      SCase "x0=x". subst. inverts HGxT. exists v. split.
        simpl. apply eq_id.
        assumption.
      SCase "x0<>x". apply IHHctxts in HGxT. clear IHHctxts.
        inversion HGxT as [v' [Ha' Hb']]. exists v'. split.
          rewrite <- Ha'. simpl. apply (neq_id _ _ _ _ _ n).
          assumption.
Qed.


Lemma ctx_tvar_then_some : forall G x T,
  G |- (tvar x) \in T -> lookup_vdecl x G = Some T.
Proof. introv H. inversion H. auto. Qed.

Lemma ctx_tvar_then_alookup : forall G x T g,
  G |- (tvar x) \in T -> g :::* G -> 
    exists v, alookup x g = Some v /\ v ::: T.
Proof. 
  introv HG Hg. apply (ctxts_agree_on_lookup x G g T Hg). 
  apply ctx_tvar_then_some. assumption. 
Qed.

(* END OF COPY *)

(** ** Lemma for reasoning about  (tvar x) / g =>: T. *)

Lemma ctx_tvar_then_evalsto : forall G x T g,
  G |- (tvar x) \in T -> g :::* G -> (tvar x) / g =>: T.
Proof. 
  introv HG Hg. destruct (ctx_tvar_then_alookup G x T g HG Hg) as [v [Hl Hv]]. 
  apply TVE. intro n. destruct n as [ | n' ].
    simpl. apply TR_NG.
    simpl. rewrite Hl.
    eapply TR_Norm. apply Hv.
Qed.



(** ** Lemma for more easily proving something of the form t / g =>: T *)

Lemma evalF_parts :
  forall (t : tm) (T : ty) (g : rctx),
    (forall n' er, evalF t g (S n') = er -> result_ok er T) ->
        t / g  =>: T.
Proof.
	introv H. apply TVE.
	destruct n  as [ | n' ]; [ simpl (evalF _ _ _); apply TR_NG | idtac ].
	apply (H n' _ eq_refl).
Qed.


(** ** Lemma for  reasoning about LETRT forms. *)

Lemma let_val : 
  forall t1 g n' (f : evalue -> ef_return) erf T1 T2,
    (LETRT x <== evalF t1 g n' IN f x) = erf ->
    t1 / g =>: T1 -> 
    (forall v1 er1, efr_normal v1 = er1 -> v1 ::: T1 -> forall er2, (f v1) = er2 -> result_ok er2 T2) 
          -> result_ok erf T2.
Proof. 
    introv HLet Heval Hin. inverts Heval as Hok1. specialize (Hok1 n').
    remember (evalF t1 g n') as er1. 
    inversion Hok1 as [T1' Her1eq HT1eq | v1 T1' Hv1 Her1eq HT1eq]. 
      rewrite <- Her1eq in HLet. subst erf. apply TR_NG .
      rewrite <- Her1eq in HLet. clear Heqer1. subst erf. apply (Hin v1 er1 Her1eq Hv1 (f v1) eq_refl).
Qed.



(**  ** evalF_soundness *)

Theorem evalF_soundness : 
  forall (t : tm) (G : context) (T : ty) (g : rctx),
    G |- t \in T ->  g :::* G -> t / g  =>: T.
Proof.
  (* introv Hty HGg. generalize dependent G. generalize dependent g. generalize dependent T. *)
  t_cases (induction t as [ x | t1 ? t2 ? | x Tx tb | | | ti ? tt ? te ? ]) Case; introv Hty HGg.

  Case "tvar". apply (ctx_tvar_then_evalsto G x T g Hty HGg).

  Case "tapp".
    inverts Hty.
    apply evalF_parts. intros n' er Hev. simpl in Hev.
    (* use the IHs to get [Ht1 : t1 / g =>: TArrow T11 T] and [Ht2 : t2 / g =>: T11].  *)
    assert (Ht1 := IHt1 _ _ _ H2 HGg); clear IHt1 H2.
    assert (Ht2 := IHt2 _ _ _ H4 HGg); clear IHt2 H4.
    (* use the [let_val] lemmas with Ht1 and Ht2 to decompose the two LETRT forms *)
    apply (let_val t1 g n' _ _ (TArrow T11 T) T Hev Ht1). clear Hev Ht1. 
    intros v1 er1 Hv1 Hv1t erL2 HevL2.
    apply (let_val t2 g n' _ _ _ _ HevL2 Ht2). clear HevL2 Ht2.
    intros v2 er2 Hv2 Hv2t erf Hevf.
    (* Here:   [Hv1t : v1 ::: TArrow T11 T] & [Hv2t : v2 ::: T11] & [erf = match v1 with ... end]. *)
    (* Invert Hv1t to get at the structure of v1 which gives [erf = evalF tb (aextend xf v2 gf) n'].  
        However, with the TV_Abs definition above, there is no information about tb, so we can't proceed.
        Instead, use the fake inversion lemma to see that it goes through. *)
    assert (Hex := (fake_vht_arrow_inversion _ _ _ Hv1t)); clear Hv1t;  (* BOGUS *)
    inversion Hex as [xf [ tb [ gf [ Hv1eq Hva]]]]; subst v1; clear Hex.
    specialize (Hva v2 Hv2t). clear Hv2t.
    inverts Hva as Hok2. specialize (Hok2 n'). rewrite Hevf in Hok2. apply Hok2.

  Case "tabs". 
    inverts Hty.
    apply evalF_parts. intros n' er Hev. simpl in Hev. rewrite <- Hev. clear Hev. apply TR_Norm.
    (* At this point, the goal is [vabs x tb g ::: TArrow Tx T12].
        Given the current TV_Abs, [apply TV_Abs] works.  However, it doesn't use the IH.
        We use the fake_TV_Abs lemma to show that the desired TV_Abs definition would work. *)
    apply fake_TV_Abs.   (* BOGUS *)
    intros va Hva.
    (* use the IH on H4 and TC_Cons with Hva. *)
    apply (IHtb _ _ _ H4). apply (TC_cons _ _ _ va _ HGg Hva).
    (* apply (fun va Hva => IHtb _ _ _ H4 (TC_cons _ _ _ va _ HGg Hva)). *)

  Case "ttrue".
    inverts Hty.
    apply evalF_parts. intros n' er Hev. simpl in Hev. rewrite <- Hev. apply TR_Norm. apply TV_True.

  Case "tfalse".
    inverts Hty.
    apply evalF_parts. intros n' er Hev. simpl in Hev. rewrite <- Hev. auto.

  Case "tif".
    inverts Hty.
    assert (Hti := IHt1 _ _ _ H3 HGg); clear IHt1 H3.
    assert (Htt := IHt2 _ _ _ H5 HGg); clear IHt2 H5.
    assert (Hte := IHt3 _ _ _ H6 HGg); clear IHt3 H6.

    apply evalF_parts. intros n' er Hev. simpl in Hev.
    inverts Hti as Hoki. specialize (Hoki n'). 
    inversion Hoki as [TBool' Hei HeqTB | vb TBool' Hvbt Hei HeqTB]; clear Hoki.
      SCase "nogas". rewrite <- Hei in Hev. rewrite <- Hev. apply TR_NG.
      SCase "efr_normal vb". subst TBool'. rewrite <- Hei in Hev; clear Hei. inverts Hvbt.
        SSCase "vtrue". inverts Htt as Hokt.  specialize (Hokt n'). rewrite Hev in Hokt. apply Hokt.
        SSCase "vfalse". inverts Hte as Hoke.  specialize (Hoke n'). rewrite Hev in Hoke. apply Hoke.
Qed.

End LEProps3.
