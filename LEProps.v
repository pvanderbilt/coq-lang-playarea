(** * Soundness of EvalF (a big-step semantics for LDef) *)

(**  This file develops a proof of soundness of [evalF], using a recursive definition of 
      [value_has_type] rather than an inductive relation (as was done in earlier attempts).  
      It seems to be working!  *)

Load Init.
Require Export SfLib.
Require Import LibTactics.

Require Export Common LDef LEval.
Import P3Common LDEF LEVAL.

Module LEProps.

(* ###################################################################### *)
(** ** Relations between values, types and evalF. *)

(**  We define several relations concurrently:
        - [v ::: T] (aka [value has type v T]): value v is the result of evaluating some term of type T.
        - [t / g =>: T] (aka [evaluates_to_a t g T]): term t, when evaluated in runtime-context g, 
          will either yield a value v ::: T or not terminate (but it won't get stuck).
        - [result_ok er T]: er (an instance of ef_return) is either efr_normal v and v ::: T or is efr_nogas;
          it is not efr_stuck.
        - [ g :::* G] (aka [bindings_match_decls g G]): 
          the runtime context, g, has exactly the elements specified by the typing context G (Gamma).

    If defined as mutually recursive functions, Coq complains about the lack of a non-decreasing argument.
    While it really is decreasing, Coq can't figure it out.  
    In the meantime, [value_has_type] is defined with the next two inside and then they are defined again
    outside the [value_has_type] definition.
    It would be nice if there was a way to get around this.
*)

Reserved Notation "v ':::' T" (at level 40).
Reserved Notation "g ':::*' G" (at level 40).
Reserved Notation "t '/' g '=>:' T" (at level 40, g at level 39).

Fixpoint value_has_type (v : evalue) (T : ty) {struct T} : Prop :=
  let result_ok (er : ef_return) (T : ty) : Prop :=
    match er with
      | efr_normal vr => vr ::: T
      | efr_nogas     => True
      | efr_stuck     => False
    end
  in let evaluates_to_a (t : tm) (g : rctx) (T : ty) : Prop := 
    forall n, result_ok (evalF t g n) T
  in let fix bindings_match_decls 
           (bs : alist evalue) (Ls : list decl) {struct Ls} : Prop :=
    match Ls with
      | nil => True
      | (Lv x T) :: Ls' => (exists v, alookup x bs = Some v /\ v ::: T)
                           /\ bindings_match_decls bs Ls'
    end
(*
  in let bindings_match_decls 
           (bs : alist evalue) (Ls : list decl) : Prop :=
   forall x T, lookup_vdecl x Ls = Some T ->
      exists v, alookup x bs = Some v /\ v ::: T
*)
(*
  in let fix bindings_match_decls 
           (bs : alist evalue) (Ls : list decl) {struct Ls} : Prop :=
    match (Ls, bs) with
      | (nil, nil) => True
      | ((Lv x T) :: Ls', ((y, v) :: bs')) =>
          x=y /\ v ::: T /\ bindings_match_decls bs' Ls'
      | (_, _) => False
    end
*)
  in match (T, v) with
    | (TBool, vtrue) => True
    | (TBool, vfalse) => True
    | ((TArrow T1 T2), (vabs xf tb gf)) => 
        forall va, va ::: T1 -> evaluates_to_a tb (aextend xf va gf) T2
    | ((TRcd Tr), (vrcd vr)) => bindings_match_decls vr Tr 
         (* this forces order which might be wrong *)
    | (_, _) => False
  end
where "v ':::' T" := (value_has_type v T).

Definition result_ok (er : ef_return) (T : ty) : Prop :=
    match er with
      | efr_normal vr => vr ::: T
      | efr_nogas => True
      | efr_stuck => False
    end.

Definition evaluates_to_a (t : tm) (g : rctx) (T : ty) : Prop := 
    forall n, result_ok (evalF t g n) T.
Notation "t '/' g '=>:' T" := (evaluates_to_a t g T) 
    (at level 40, g at level 39).

Fixpoint bindings_match_decls 
           (bs : alist evalue) (Ls : list decl) {struct Ls} : Prop :=
    match Ls with
      | nil => True
      | (Lv x T) :: Ls' => (exists v, alookup x bs = Some v /\ v ::: T)
                           /\ bindings_match_decls bs Ls'
    end.

Notation "g ':::*' G" := (bindings_match_decls g G).
Hint Unfold bindings_match_decls.

Lemma TC_nil :
  nil :::* nil.
Proof. simpl. constructor. Qed.

Lemma TC_cons : 
  forall G g x v T,
    g :::* G ->
    v ::: T ->
    (aextend x v g) :::* (add_vdecl x T G).
Proof.
  introv HgG HvT. simpl. split. 
    exists v. split. 
      apply eq_id.
      apply HvT.
    admit. (* Fix this! *)
Qed.

Lemma decl_implies_value:
  forall x T Ls bs, 
    In (Lv x T) Ls -> 
    bs :::* Ls ->
    exists v, alookup x bs = Some v /\ v ::: T.
Proof.
  introv Hin Hbmd.
  induction Ls as [ | L Ls'].
    simpl in Hin. contradiction.
    destruct L. destruct Hbmd as [Hex Hrest]. destruct Hin.
      SCase "=". inverts H. apply Hex.
      SCase "In tail". apply (IHLs' H Hrest).
Qed.

(*
Definition bindings_match_decls (bs : alist evalue) (Ls : list decl) : Prop :=
  let decl_implies_lookup bs L := match L with (Lv x T) => exists v, alookup x bs = Some v /\ v ::: T end
  in Forall (decl_implies_lookup bs) Ls.
*)
(*  Forall (fun L => match L with (Lv x T) => exists v, alookup x bs = Some v /\ v ::: T end) Ls. *)

(*
Fixpoint bindings_match_decls 
           (bs : alist evalue) (Ls : list decl) {struct Ls} : Prop :=
    match (Ls, bs) with
      | (nil, nil) => True
      | ((Lv x T) :: Ls', ((y, v) :: bs')) =>
          x=y /\ v ::: T /\ bindings_match_decls bs' Ls'
      | (_, _) => False
    end.
*)


(*
Inductive bindings_match_decls: rctx -> context -> Prop :=
  | TC_nil : nil :::* empty
  | TC_cons : forall G g x v T, 
                g :::* G -> v ::: T -> (aextend x v g) :::* (add_vdecl x T G)
where "g ':::*' G" := (bindings_match_decls g G).
Hint Constructors  bindings_match_decls.
*)
Hint Unfold value_has_type result_ok evaluates_to_a. 

(* ###################################################################### *)
(** ** Lemmas  *)
(** *** Lemmas for "inverting" the [value_has_type] function. *)

Lemma bool_vals: forall v, v ::: TBool -> (v = vtrue \/ v = vfalse).
Proof.
  intros v Hvt. destruct v; try (simpl in Hvt; contradiction); auto.
Qed.

Lemma fun_vals:
  forall T1 T2 v, v ::: TArrow T1 T2 ->
    exists xf tb gf, 
      v = (vabs xf tb gf) 
      /\ (forall va, va ::: T1 -> tb / (aextend xf va gf) =>: T2).
Proof. 
  intros T1 T2 v Hvt.  destruct v; simpl in Hvt; try contradiction.
    exists i t a. split. 
      reflexivity.
      intros va Hvat n. 
        specialize (Hvt va Hvat n). 
        destruct (evalF t (aextend i va a) n); unfold result_ok; auto.
Qed.

Lemma rcd_vals :
  forall v Ls, v ::: TRcd Ls ->
    exists bs, 
      v = (vrcd bs) /\ bs :::* Ls.
Proof. 
  intros v Ls Hvt. destruct v as [ | | | bs]; simpl in Hvt; try contradiction.
    exists bs. split. 
      reflexivity.
      red. induction Ls.
        simpl. apply Hvt.
        destruct a as [x T]. simpl.
        destruct Hvt as [Hex Hfix].
        split. 
          apply Hex.
          apply (IHLs Hfix).
Qed.
Print rcd_vals.

Fixpoint value_has_type' (v : evalue) (T : ty) {struct T} : Prop :=
  match (T, v) with
    | (TBool, vtrue) => True
    | (TBool, vfalse) => True
    | ((TArrow T1 T2), (vabs xf tb gf)) => 
        forall va, va ::: T1 -> tb / (aextend xf va gf) =>: T2
    | ((TRcd Tr), (vrcd vr)) => vr :::* Tr 
    | (_, _) => False
  end.

Lemma vht_defs_eq:
  forall v T, value_has_type v T <-> value_has_type' v T.
Proof.
  intros. split; intro H. 
    Case "->". induction T; destruct v; simpl in H; auto.
    Case "<-". induction T; destruct v; simpl in H; auto.
Qed.


(** *** Lemmas for reasoning about contexts (runtime and typing). *)
Require Import Utils. Import PVUTILS.
Lemma lookup_implies_in:
  forall x G T,
    lookup_vdecl x G = Some T -> In (Lv x T) G.
Proof.
  introv Hlookup. induction G as [ | L G'].
  Case "G=[]". inversion Hlookup.
  Case "G=L::G'". 
    destruct L as [y Ty].
    destruct (eq_id_dec y x).
    SCase "y=x". subst. 
      simplify_term_in (lookup_vdecl x (Lv x Ty :: G')) Hlookup. 
        apply lookup_add_vdecl_eq. 
        inverts Hlookup. simpl. left. reflexivity.
    SCase "y<>x". 
      simplify_term_in (lookup_vdecl x (Lv y Ty :: G')) Hlookup.
        apply lookup_add_vdecl_neq. apply n.
        simpl. right. apply (IHG' Hlookup).
Qed.


Lemma ctxts_agree_on_lookup : 
  forall (x : id) (G : context) (g : rctx) (T : ty),
    g  :::* G -> 
    lookup_vdecl x G = Some T ->
      exists v, alookup x g = Some v /\ v ::: T.
Proof.
  introv HgG HGxT. 
  apply lookup_implies_in in HGxT. 
  apply (decl_implies_value _ _ _ _ HGxT HgG).
(*
  induction G as [ | [? Ty] G']; introv Hctxts HGxT. 
    Case "G=[]". inversion HGxT.
    Case "G=(Lv y Ty)::G'". 
      destruct g as [ | [y vy] g']. simpl in Hctxts.
      SCase "g=[]". contradiction.
      SCase "g=(y;vy)::g'".
        inversion Hctxts as [? [Het HgG]]; subst; clear Hctxts.
        destruct (eq_id_dec y x) as [ Heq | Hneq ].
          SSCase "y=x". subst. exists vy. split.
            apply alookup_cons_eq.
            assert (Hxxx := (lookup_add_vdecl_eq x Ty G')). unfold add_vdecl in Hxxx.
              rewrite Hxxx in HGxT. inverts HGxT. apply Het.
          SSCase "y<>x". 
            assert (Hxxx := (lookup_add_vdecl_neq x y Ty G' Hneq)). unfold add_vdecl in Hxxx.
            rewrite Hxxx in HGxT. destruct (IHG' g' T HgG HGxT) as [v [Hlv HvT]].
            exists v. split.
              rewrite (alookup_cons_neq _ _ _ _ _ Hneq). apply Hlv. 
              apply HvT.*)
Qed.

(*
Lemma ctxts_agree_on_lookup_old : 
  forall (x : id) (G : context) (g : rctx) (T : ty),
    g  :::* G -> 
    lookup_vdecl x G = Some T ->
      exists v, alookup x g = Some v /\ v ::: T.
Proof.
  introv Hctxts HGxT. induction Hctxts.
    Case "TC_nil". inversion HGxT.
    Case "TC_cons". unfold lookup_vdecl, add_vdecl in HGxT. 
    destruct (eq_id_dec x0 x).
      SCase "x0=x". subst. inverts HGxT. exists v. split.
        simpl. apply eq_id.
        assumption.
      SCase "x0<>x". apply IHHctxts in HGxT. clear IHHctxts.
        inversion HGxT as [v' [Ha' Hb']]. exists v'. split.
          rewrite <- Ha'. simpl. apply (neq_id _ _ _ _ _ n).
          assumption.
Qed.
*)

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

(** *** Lemma for reasoning about  (tvar x) / g =>: T. *)

Lemma ctx_tvar_then_evalsto : forall G x T g,
  G |- (tvar x) \in T -> g :::* G -> (tvar x) / g =>: T.
Proof. 
  introv HG Hg. destruct (ctx_tvar_then_alookup G x T g HG Hg) as [v [Hl Hv]].
  unfold evaluates_to_a. intro n. destruct n as [ | n' ]; simpl; auto.
    rewrite Hl. auto.
Qed.

(** *** Lemma for more easily proving something of the form t / g =>: T *)

Lemma evalF_parts :
  forall (t : tm) (T : ty) (g : rctx),
    (forall n' er, evalF t g (S n') = er -> result_ok er T) ->
        t / g  =>: T.
Proof.
	introv H. unfold evaluates_to_a. 
	destruct n  as [ | n' ].
     simpl (evalF _ _ _). unfold result_ok. exact I.
	   apply (H n' _ eq_refl).
Qed.


(** *** Lemma for  reasoning about LETRT forms. *)

Lemma let_val : 
  forall t1 g n' (f : evalue -> ef_return) erf T1 T2,
    (LETRT x <== evalF t1 g n' IN f x) = erf ->
    t1 / g =>: T1 -> 
    (forall v1 er1, efr_normal v1 = er1 -> v1 ::: T1 -> forall er2, (f v1) = er2 -> result_ok er2 T2) 
          -> result_ok erf T2.
Proof. 
    introv HLet Heval Hin. assert(Hok1 := Heval  n'); clear Heval.
    remember (evalF t1 g n') as er1.
    destruct er1 as [v1 | | ].
      unfold result_ok in Hok1. apply (Hin  v1 (evalF t1 g n') Heqer1 Hok1 erf HLet).
      subst erf; auto.
      subst erf; auto.
Qed.

(* ###################################################################### *)
(**  ** Proof of soundness of evalF *)
(**  *** Proof of [evalF_is_sound_yielding_T] *)

Theorem evalF_is_sound_yielding_T : 
  forall (t : tm) (G : context) (T : ty) (g : rctx),
    G |- t \in T ->  g :::* G -> t / g  =>: T.
Proof.
  (* introv Hty HGg. generalize dependent G. generalize dependent g. generalize dependent T. *)
  t_cases (induction t as [ | | x | t1 IHt1 t2 IHt2 | x Tx tb IHtb | Fs | tr IHtr x | ti ? tt ? te ? ]) 
      Case; introv Hty HGg.

  Case "ttrue".
    inverts Hty. apply evalF_parts; intros n' er Hev; simpl in Hev.
    rewrite <- Hev. auto.

  Case "tfalse".
    inverts Hty. apply evalF_parts; intros n' er Hev; simpl in Hev.
    rewrite <- Hev. auto.

  Case "tvar". apply (ctx_tvar_then_evalsto G x T g Hty HGg).

  Case "tapp".
    inverts Hty. apply evalF_parts. intros n' er Hev. simpl in Hev.
    (* use the IHs to get [Ht1 : t1 / g =>: TArrow T11 T] and [Ht2 : t2 / g =>: T11].  *)
    assert (Ht1 := IHt1 _ _ _ H2 HGg); clear IHt1 H2.
    assert (Ht2 := IHt2 _ _ _ H4 HGg); clear IHt2 H4.
    (* use the [let_val] lemmas with Ht1 and Ht2 to decompose the two LETRT forms *)
    apply (let_val t1 g n' _ _ (TArrow T1 T) T Hev Ht1); clear Hev Ht1;
    intros v1 er1 Hv1 Hv1t erL2 HevL2.
    apply (let_val t2 g n' _ _ _ _ HevL2 Ht2); clear HevL2 Ht2;
    intros v2 er2 Hv2 Hv2t erf Hevf.
    assert (Hex := fun_vals _ _ _ Hv1t); clear Hv1t.
    inversion Hex as [xf [ tb [ gf [ Hv1eq Hva]]]]; subst v1; clear Hex.
    specialize (Hva v2 Hv2t). clear Hv2t.
    assert (Hok2 := Hva n'). rewrite Hevf in Hok2. apply Hok2.

  Case "tabs". 
    inverts Hty. apply evalF_parts; intros n' er Hev; simpl in Hev.
    rewrite <- Hev. clear Hev. unfold result_ok.  unfold value_has_type. intros va Hvat n. 
    apply (IHtb _ _ (aextend x va g) H4 (TC_cons _ _ _ _ _ HGg Hvat)).

  Case "trcd". 
    inverts Hty. apply evalF_parts; intros n' er Hev. simpl in Hev.
    admit.

  Case "tproj". 
    inverts Hty. apply evalF_parts; intros n' er Hev. simpl in Hev. 
    assert (Htr := IHtr _ _ _ H2 HGg); clear IHtr H2.
    apply (let_val tr g n' _ _ _ _ Hev Htr). clear Hev Htr; intros vr err Hvr Hvrt erp Hevp.
    destruct (rcd_vals _ _ Hvrt) as [ bs [? HbsT ]]; subst.
    assert (Hxxx := ctxts_agree_on_lookup _ _ _ _ HbsT H4). destruct Hxxx as [v [Hlk HvT]].
    rewrite Hlk. apply HvT.

  Case "tif".
    inverts Hty. apply evalF_parts; intros n' er Hev; simpl in Hev.
    assert (Hti := IHt1 _ _ _ H3 HGg); clear IHt1 H3.
    assert (Htt := IHt2 _ _ _ H5 HGg); clear IHt2 H5.
    assert (Hte := IHt3 _ _ _ H6 HGg); clear IHt3 H6.

    specialize (Hti n'). destruct (evalF ti g n').
       SCase "efr_normal vb". destruct e; simpl in Hti; subst er.
          SSCase "e = (vabs ...)". contradiction.
          SSCase "e = vtrue".  apply (Htt n').
          SSCase "e = vfalse".  apply (Hte n').
          SSCase "e = (vrcd ...)".  contradiction.
      SCase "nogas". subst er. apply Hti.
      SCase "stuck". unfold result_ok in Hti. contradiction.
Qed.

(**  *** Proof of [evalF_is_sound] *)

Corollary evalF_is_sound: 
  forall (t : tm) (G : context) (T : ty) (g : rctx) (n : nat),
    G |- t \in T ->  g :::* G -> evalF t g n  <> efr_stuck.
Proof.
  introv Hty HGg.
  assert (Hr := evalF_is_sound_yielding_T _ _ _ _ Hty HGg n).
  destruct (evalF t g n); [ discriminate | discriminate |
     unfold result_ok in Hr; contradiction] .
Qed.

End LEProps.
