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
        - [v ::: T] (aka [value has type v T]): 
          value v is the result of evaluating some term of type T.
        - [t / g =>: T] (aka [evaluates_to_a t g T]): 
          term t, when evaluated in runtime-context g, 
          will either yield a value v ::: T or not terminate 
          (but it won't get stuck).
        - [result_ok er T]: er (an instance of ef_return) is either 
          efr_normal v and v ::: T 
          or is efr_nogas; it is not efr_stuck.
        - [ g :::* G] (aka [bindings_match_decls g G]): 
          the runtime context, g, has exactly the elements specified by 
          the typing context G (Gamma) (in the same order).

    If defined as mutually recursive functions, Coq complains about 
    the lack of a non-decreasing argument.
    While it really is decreasing, Coq can't figure it out.  
    In the meantime, [value_has_type] is defined with the next three 
    nested within and then they are defined again
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
(*
  in let fix bindings_match_decls 
           (bs : alist evalue) (Ls : list decl) {struct Ls} : Prop :=
    match Ls with
      | nil => True
      | (Lv x T) :: Ls' => (exists v, alookup x bs = Some v /\ v ::: T)
                           /\ bindings_match_decls bs Ls'
    end
*)
(*
  in let bindings_match_decls 
           (bs : alist evalue) (Ls : list decl) : Prop :=
   forall x T, lookup_vdecl x Ls = Some T ->
      exists v, alookup x bs = Some v /\ v ::: T
*)
  in let fix bindings_match_decls 
           (bs : alist evalue) (Ls : list decl) {struct Ls} : Prop :=
    match (Ls, bs) with
      | (nil, nil) => True
      | ((Lv x T) :: Ls', ((y, v) :: bs')) =>
          x=y /\ v ::: T /\ bindings_match_decls bs' Ls'
      | (_, _) => False
    end
  in match (T, v) with
    | (TBool, vtrue) => True
    | (TBool, vfalse) => True
    | ((TArrow T1 T2), (vabs xf tb gf)) => 
        forall va, va ::: T1 -> evaluates_to_a tb (aextend xf va gf) T2
    | ((TRcd Tr), (vrcd vr)) => bindings_match_decls vr Tr 
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
    match (Ls, bs) with
      | (nil, nil) => True
      | ((Lv x T) :: Ls', ((y, v) :: bs')) =>
          x=y /\ v ::: T /\ bindings_match_decls bs' Ls'
      | (_, _) => False
    end.
Notation "g ':::*' G" := (bindings_match_decls g G).

Definition result_list_ok (er : xf_return) (Ls : list decl) : Prop :=
    match er with
      | efr_normal bs => bs :::* Ls
      | efr_nogas => True
      | efr_stuck => False
    end.


Definition execs_to_decls (Fs : list def) (g : rctx) (Ls : list decl) : Prop := 
    forall n', result_list_ok (execF_list Fs g n') Ls.
Notation "Fs '/' g '=>:*' Ls" := (execs_to_decls Fs g Ls) 
    (at level 40, g at level 39).

Hint Unfold value_has_type result_ok evaluates_to_a bindings_match_decls.



(** A handy lemma for doing a form of induction over :::*.
    Use it with the [refine] tactic.
*)

Lemma bmd_ind: 
  forall (P : list decl -> alist evalue -> Type)
    (fnil : P nil nil)
    (fcons: forall x v T Ls' bs', 
      v ::: T -> (P Ls' bs') -> P ((Lv x T)  :: Ls') ((x, v) :: bs')),
    forall (Ls : list decl) (bs : alist evalue), (bs :::* Ls) -> P Ls bs.
Proof.
  intros P fnil fcons Ls.
  induction Ls as [ | [x T] Ls']; intros bs Hbmd;
      destruct bs as [ |[y v] bs']; simpl in Hbmd; try contradiction.
    Case "Ls = []". 
      apply fnil.
    Case "Ls = L :: Ls'".
      destruct Hbmd as (Heq & Hvyt & Hbmd'). subst y. 
      apply (fcons _ _ _ _ _ Hvyt (IHLs' _ Hbmd')).
Qed.


(*
Fixpoint bindings_match_decls 
           (bs : alist evalue) (Ls : list decl) {struct Ls} : Prop :=
    match Ls with
      | nil => True
      | (Lv x T) :: Ls' => (exists v, alookup x bs = Some v /\ v ::: T)
                           /\ bindings_match_decls bs Ls'
    end.
*)
(*
Definition bindings_match_decls (bs : alist evalue) (Ls : list decl) : Prop :=
  let decl_implies_lookup bs L := match L with (Lv x T) => exists v, alookup x bs = Some v /\ v ::: T end
  in Forall (decl_implies_lookup bs) Ls.
*)
(*  Forall (fun L => match L with (Lv x T) => exists v, alookup x bs = Some v /\ v ::: T end) Ls. *)

(*
Inductive bindings_match_decls: rctx -> context -> Prop :=
  | TC_nil : nil :::* empty
  | TC_cons : forall G g x v T, 
                g :::* G -> v ::: T -> (aextend x v g) :::* (add_vdecl x T G)
where "g ':::*' G" := (bindings_match_decls g G).
Hint Constructors  bindings_match_decls.
*)

(** **** Constructor lemmas *)
(** Lemmas that mimic the inductive constructors that would have 
    been defined if Coq allowed us to define our relations that way. *)

Lemma TV_True :
  vtrue ::: TBool.
Proof. reflexivity. Qed.

Lemma TV_False :
  vfalse ::: TBool.
Proof. reflexivity. Qed.

Lemma TV_Abs :
  forall xf tb gf T1 T2,
    (forall va,  va ::: T1 -> tb / (aextend xf va gf) =>: T2) ->
    vabs xf tb gf ::: TArrow T1 T2.
Proof. introv H. simpl. exact H. Qed.

Lemma TV_Rcd : 
  forall Fs Ls,
    Fs :::* Ls ->
    vrcd Fs ::: TRcd Ls.
Proof. introv H. simpl. exact H. Qed.

Lemma TC_nil :
  nil :::* nil.
Proof. simpl. constructor. Qed.

Lemma TC_cons : 
  forall G g x v T,
    g :::* G ->
    v ::: T ->
    (aextend x v g) :::* (add_vdecl x T G).
Proof. auto.
  introv HgG HvT. simpl. auto. 
Qed.

Lemma TVE:
  forall t g T,
    (forall n er, evalF t g n = er -> result_ok er T) -> 
    (t / g =>: T).
Proof.
  introv H. red. apply (fun n => H n (evalF t g n) eq_refl).
Qed.

Lemma TVE_inv:
  forall t g T,
    (t / g =>: T) -> 
    (forall n er, evalF t g n = er -> result_ok er T).
Proof.
  intros t g T Hevto n er ?; subst er. apply Hevto.
Qed.

Lemma TR_Norm : 
  forall v T er,
    efr_normal v = er ->
    v ::: T ->
    result_ok er T.
Proof.
  introv Heq Ht. subst. simpl. exact Ht.
Qed.

Lemma TRL_Norm : 
  forall Fs Ls xr,
    efr_normal Fs = xr ->
    Fs :::* Ls ->
    result_list_ok xr Ls.
Proof.
  introv Heq Ht. subst. simpl. exact Ht.
Qed.

(* Not used: a version using [bmd_ind] but not [lookup_case]. *)
Lemma ctxts_agree_on_lookup_old1 : 
  forall (Ls : context) (bs : rctx),
    bs :::* Ls -> 
    forall (x : id) (T : ty),
      lookup_vdecl x Ls = Some T ->
        exists v, alookup x bs = Some v /\ v ::: T.
Proof.
  refine (bmd_ind
    (fun Ls bs => forall (x : id) (T : ty),
      lookup_vdecl x Ls = Some T ->
        exists v, alookup x bs = Some v /\ v ::: T)
    _
    _).
     Case "nil". introv Hlk. inverts Hlk.
     Case "cons". introv Hvt IH Hlk.
      unfold lookup_vdecl in Hlk.
      destruct (eq_id_dec x x0).
        SCase "x=x0". inversion Hlk; subst; clear Hlk.
          exists v. split.
            simpl. apply eq_id.
            apply Hvt.
        SCase "x<>x0". fold lookup_vdecl in Hlk.
          destruct (IH _ _ Hlk) as [v0 [Hlk0 Hvt0]].
          exists v0. split.
            rewrite (alookup_cons_neq _ _ _ _ _ n). apply Hlk0.
            apply Hvt0.
Qed.

(** An attempt at an induction-like rule for casing on the outcome of
    lookup over add. The rule can be proved, but it's hard to use, as
    the binding for r is wrong. *)

Lemma lookup_cons_case_old :
  forall (P : id -> id -> ty -> list decl -> option ty -> Prop)
    (Heq : forall x T Ls' r, r = Some T -> P x x T Ls' r)
    (Hneq : forall x y T Ls' r, r = (lookup_vdecl x Ls') -> y<>x -> P x y T Ls' r),
    forall x y T Ls' r, lookup_vdecl x (Lv y T :: Ls') = r ->
      P x y T Ls' r.
Proof.
  intros P Heq Hneq x y T Ls' r Hlk.
  unfold lookup_vdecl in Hlk.
  destruct (eq_id_dec y x) as [ He | Hne].
    SCase "y=x". subst. apply Heq. reflexivity.
    SCase "y<>x". fold lookup_vdecl in Hlk.
      subst r. apply (Hneq _ _ _ _ _ eq_refl Hne).
Qed.

(** Lemma [lookup_cons_case] allows one to more easily handle the
    two possible cases of [lookup_vdecl] after [add_vdecl] (except as a cons).
    Move to generic code. *)

Lemma lookup_cons_case :
  forall x y T Ls' r, 
    lookup_vdecl x (Lv y T :: Ls') = r ->
    (y=x /\ Some T = r) \/ (y<>x /\ lookup_vdecl x Ls' = r).
Proof.
  introv Hlk.
  unfold lookup_vdecl in Hlk.
  destruct (eq_id_dec y x) as [ He | Hne].
    SCase "y=x". left. auto.
    SCase "y<>x". fold lookup_vdecl in Hlk. right. auto. 
Qed.

(** Revision using above lemma:*)

Lemma ctxts_agree_on_lookup_old2 : 
  forall (Ls : context) (bs : rctx),
    bs :::* Ls -> 
    forall (x : id) (T : ty),
      lookup_vdecl x Ls = Some T ->
        exists v, alookup x bs = Some v /\ v ::: T.
Proof.
  refine (bmd_ind
    (fun Ls bs => forall (x : id) (T : ty),
      lookup_vdecl x Ls = Some T ->
        exists v, alookup x bs = Some v /\ v ::: T)
    _
    _).
     Case "nil". introv Hlk. inverts Hlk.
     Case "cons". introv Hvt IH Hlk.
       apply lookup_cons_case in Hlk. destruct Hlk as [[Hxe HTe] | [Hxn Hle]].
         SCase "x=x0". inversion HTe; subst; clear HTe. exists v. split.
           simpl. apply eq_id.
           apply Hvt. 
         SCase "x<>x0". 
           destruct (IH _ _ Hle) as [v0 [Hlk0 Hvt0]].
           exists v0. split.
             rewrite (alookup_cons_neq _ _ _ _ _ Hxn). apply Hlk0.
             apply Hvt0.
Qed.

(** Using refine with all underscores (use this one): *)

Lemma ctxts_agree_on_lookup : 
  forall (Ls : context) (bs : rctx),
    bs :::* Ls -> 
    forall (x : id) (T : ty),
      lookup_vdecl x Ls = Some T ->
        exists v, alookup x bs = Some v /\ v ::: T.
Proof.
  refine (bmd_ind _ _ _).
    Case "nil". introv Hlk. inverts Hlk.
    Case "cons". introv Hvt IH Hlk.
      apply lookup_cons_case in Hlk. 
      destruct Hlk as [[Hxe HTe] | [Hxn Hle]].
        SCase "x=x0". 
          inversion HTe; subst; clear HTe. 
          exists v. split.
            apply alookup_cons_eq.
            apply Hvt. 
        SCase "x<>x0". 
          destruct (IH _ _ Hle) as [v0 [Hlk0 Hvt0]]. 
          exists v0. split.
            rewrite (alookup_cons_neq _ _ _ _ _ Hxn). apply Hlk0.
            apply Hvt0.
Qed.

(* Not working:
Lemma decl_implies_value:
  forall x T Ls bs, 
    In (Lv x T) Ls -> 
    bs :::* Ls ->
    exists v, alookup x bs = Some v /\ v ::: T.
Proof.
  pose (P:= fun Ls bs => forall x T, 
         In (Lv x T) Ls -> 
         exists v, alookup x bs = Some v /\ v ::: T).
  assert (forall Ls bs, bs :::* Ls -> P Ls bs).
    apply bmd_ind.
      Case "nil". unfold P. intros x T Hin.  simpl in Hin. contradiction.
      Case "cons". introv Hvt IH Hin. destruct Hin as [Heq | HLs'].
         SCase "=". inversion Heq; subst x0 T0; clear Heq.
           exists v. split. 
             simpl. apply eq_id. 
             apply Hvt.
        SCase "In tail". 
          destruct bs as [ |[y vy] bs']; 
            destruct L; simpl in Hbmd; try contradiction.
        apply (IHLs' HLs' Hrest).

          apply (IH _ _ HLs').
  induction Ls as [ | L Ls'].
    Case "Ls = []". simpl in Hin. contradiction.
    Case "Ls = L :: Ls'".  simpl in Hin.
      destruct Hin as [Heq | HLs'].
      SCase "=". subst L.  
         destruct bs as [ |[y vy] bs']; simpl in Hbmd; try contradiction.
         destruct Hbmd as (Heq & Hvyt & Hbmd').
         subst y.  exists vy. split.
           simpl. apply eq_id. 
           apply Hvyt.
      SCase "In tail". 
        destruct bs as [ |[y vy] bs']; 
          destruct L; simpl in Hbmd; try contradiction.
        apply (IHLs' HLs' Hrest).
simpl in Hin.
       destruct L as [y Ty]. destruct bs; simpl in Hbmd; try contradiction.

 
destruct Hbmd as [Hex Hrest]. 
Qed.
*)


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
      assumption.
Qed.

(** *** value_has_type redefined and its equivalence *)

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
(*Require Import Utils. Import PVUTILS.
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
*)
Lemma lookup_implies_in:
  forall x G T,
    lookup_vdecl x G = Some T -> In (Lv x T) G.
Proof.
  introv Hlookup. induction G as [ | [y Ty] G'].
  Case "G=[]". inversion Hlookup.
  Case "G=(Lv y Ty)::G'". 
    apply lookup_cons_case in Hlookup.
    destruct Hlookup as [[Hxe HTe] | [Hxn Hle]].
    SCase "y=x". inverts HTe. subst. left. reflexivity.
    SCase "y<>x". right. apply (IHG' Hle).
Qed.


(* Doesn't work as [decl_implies_value] is commented out 
Lemma ctxts_agree_on_lookup_old3 : 
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
*)
(* Version for when :::* was defined inductively:
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
  introv HG Hg. 
  apply (ctxts_agree_on_lookup G g Hg x T (ctx_tvar_then_some _ _ _ HG)). 
Qed.


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

Lemma execF_list_parts :
  forall (Fs : list def) (Ls : list decl) (g : rctx),
    (forall n' er, execF_list Fs g n' = er -> result_list_ok er Ls) ->
        Fs / g  =>:* Ls.
Proof.
  introv H. unfold execs_to_decls. apply (fun n' => H n' _ eq_refl).
Qed.


(** *** Lemmas for reasoning about LETRT forms. *)

Lemma let_val : 
  forall t1 g n' (f : evalue -> ef_return) erf T1 T2,
    (LETRT x <== evalF t1 g n' IN f x) = erf ->
    t1 / g =>: T1 -> 
    (forall v1, 
       v1 ::: T1 -> 
       forall er2, 
         (f v1) = er2 -> 
         result_ok er2 T2) -> 
    result_ok erf T2.
Proof. 
    introv HLet Heval Hin. 
    specialize (Heval n'). 
    destruct (evalF t1 g n') as [v1 | | ]; try (subst erf; auto; fail).
      Case "result_ok v1". 
        unfold result_ok in Heval. 
        apply (Hin v1 Heval erf HLet).
Qed.

Lemma let_vlist : 
  forall Fs g n' (f : alist evalue -> ef_return) erf Ls T2,
    (LETRT bs <== execF_list Fs g n' IN f bs) = erf ->
    Fs / g =>:* Ls -> 
    (forall bs1,
       bs1 :::* Ls -> 
       forall er2, 
         (f bs1) = er2 -> 
         result_ok er2 T2) -> 
    result_ok erf T2.
Proof. 
    introv HLet Heval Hin. 
    specialize (Heval n'). 
    destruct (execF_list Fs g n') as [bs1 | | ]; try (subst erf; auto; fail).
      Case "result_ok bs1". 
        unfold result_list_ok in Heval. 
        apply (Hin bs1 Heval erf HLet).
Qed.

Lemma list_let_val : 
  forall t1 g n' (f : evalue -> xf_return) xrf T1 T2,
    (LETRT x <== evalF t1 g n' IN f x) = xrf ->
    t1 / g =>: T1 -> 
    (forall v1,
       v1 ::: T1 -> 
       forall er2, 
         (f v1) = er2 -> 
         result_list_ok er2 T2) -> 
    result_list_ok xrf T2.
Proof. 
    introv HLet Heval Hin. 
    specialize (Heval n'). 
    destruct (evalF t1 g n') as [v1 | | ]; try (subst xrf; auto; fail).
      Case "result_ok v1". 
        unfold result_ok in Heval. 
        apply (Hin v1 Heval xrf HLet).
Qed.

Lemma list_let_vlist : 
  forall Fs1 g n' (f : alist evalue -> xf_return) erf Ls1 Ls2,
    (LETRT bs1 <== execF_list Fs1 g n' IN f bs1) = erf ->
    Fs1 / g =>:* Ls1 -> 
    (forall bs1,
       bs1 :::* Ls1 -> 
       forall er2, 
         (f bs1) = er2 -> 
         result_list_ok er2 Ls2) -> 
    result_list_ok erf Ls2.
Proof. 
    introv HLet Heval Hin. 
    specialize (Heval n'). 
    destruct (execF_list Fs1 g n') as [bs1 | | ]; try (subst erf; auto; fail).
      Case "result_ok bs1". 
        unfold result_list_ok in Heval. 
        apply (Hin bs1 Heval erf HLet).
Qed.


(* ###################################################################### *)
(**  ** Proof of soundness of evalF *)
(**  *** Proof of [evalF_is_sound_yielding_T] *)

  
Theorem evalF_is_sound_yielding_T : 
  forall (t : tm) (G : context) (T : ty) (g : rctx),
    G |- t \in T ->  g :::* G -> t / g  =>: T.
Proof.
  set (Q:=fun Fs : list def =>
          forall (G : context) (Ls : list decl) (g : rctx),
            G |- Fs *\in Ls ->  g :::* G -> Fs / g  =>:* Ls).
  tm_xind_tactic t Q Case; 
    introv Hty HGg; inverts Hty; 
    (apply evalF_parts || apply execF_list_parts);
    intros n' er Hev; simpl in Hev; subst Q.

  Case "ttrue". 
    exact (TR_Norm _ _ _ Hev TV_True).

  Case "tfalse".
    exact (TR_Norm _ _ _ Hev TV_False).

  Case "tvar". 
    destruct (ctxts_agree_on_lookup _ _ HGg _ _ H1) as [v [Hlk Hvt]].
    rewrite Hlk in Hev. exact (TR_Norm _ _ _ Hev Hvt).
    (* pre "inverts" : apply (ctx_tvar_then_evalsto G x T g Hty HGg).*)

  Case "tapp".
    (* use IHs to get [Ht1 : t1 / g =>: TArrow T11 T] & [Ht2 : t2 / g =>: T11].  *)
    assert (Ht1 := IHt1 _ _ _ H2 HGg); clear IHt1 H2.
    assert (Ht2 := IHt2 _ _ _ H4 HGg); clear IHt2 H4.
    (* use the [let_val] lemma with Ht1 and Ht2 to decompose the two LETRT forms *)
    apply (let_val t1 g n' _ _ (TArrow T1 T) T Hev Ht1); clear Hev Ht1;
    intros v1 Hv1t erL2 HevL2.
    apply (let_val t2 g n' _ _ _ _ HevL2 Ht2); clear HevL2 Ht2;
    intros v2 Hv2t erf Hevf.
    assert (Hex := fun_vals _ _ _ Hv1t); clear Hv1t;
    destruct Hex as (xf & tb & gf & Hv1eq & Hva); subst v1. 
    apply (TVE_inv _ _ _ (Hva v2 Hv2t) n' _ Hevf).

  Case "tabs". 
    apply (TR_Norm _ _ _ Hev); clear Hev.
    apply TV_Abs; intros va Hvat.
    apply (IHtb _ _ (aextend x va g) H4). clear IHtb.
    apply (TC_cons _ _ _ _ _ HGg Hvat).

  Case "trcd". 
    rewrite <- (execF_list_eq Fs g n') in Hev.
    assert (HFs := IHFs _ _ _ H1 HGg); clear IHFs H1.
    apply (let_vlist _ g n' _ _ _ _ Hev HFs); clear Hev HFs;
    intros bs Hbst er2 Hev2. 
    apply (TR_Norm _ _ _ Hev2 (TV_Rcd _ _ Hbst)).

  Case "trnil".
    apply (TRL_Norm _ _ _ Hev TC_nil). 

  Case "trcons".
    assert (Ht := IHt _ _ _ H4 HGg); clear IHt H4.
    assert (HFs := IHFs _ _ _ H5 HGg); clear IHFs H5.
    apply (list_let_val tx g n' _ _ T _ Hev Ht); clear Hev Ht;
    intros v1 Hv1t erL2 HevL2.
    apply (list_let_vlist _ g n' _ _ Tr _ HevL2 HFs); clear HevL2 HFs;
    intros bs2 Hbs2t erf Hevf. 
    apply (TRL_Norm _ _ _ Hevf).
    apply (TC_cons _ _ _ _ _ Hbs2t Hv1t).

  Case "tproj". 
    assert (Htr := IHtr _ _ _ H2 HGg); clear IHtr H2.
    apply (let_val tr g n' _ _ _ _ Hev Htr); clear Hev Htr; 
    intros vr Hvrt erp Hevp.
    destruct (rcd_vals _ _ Hvrt) as [bs [? HbsT ]]. subst vr.
    destruct (ctxts_agree_on_lookup _ _ HbsT _ _ H4) as [v [Hlk HvT]].
    rewrite Hlk in Hevp. 
    apply (TR_Norm _ _ _ Hevp HvT).

  Case "tif".
    assert (Hti := IHti _ _ _ H3 HGg); clear IHti H3.
    apply (let_val ti g n' _ _ _ _ Hev Hti); clear Hev Hti;
    intros vi Hvit erc Hevc.
    destruct (bool_vals vi Hvit); subst.
      SSCase "v = vtrue". apply (IHtt _ _ _ H5 HGg n').
      SSCase "v = vfalse". apply (IHte _ _ _ H6 HGg n').

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
