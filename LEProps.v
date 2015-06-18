(** * Soundness of EvalF (a big-step semantics for LDef) *)

(**  This file develops a proof of soundness of [evalF], 
     using a recursive definition of 
     [value_has_type] rather than an inductive relation 
     (as was done in earlier attempts).  
     It has been updated to handle records and seems to be working!  *)

Load Init.
Require Export SfLib.
Require Import LibTactics.

Require Export Common LDef LEval.
Import Common LDef LEval.

(* ###################################################################### *)
(** ** Relations between values, types and evalF. *)

(**  We define several relations concurrently:
        - [v ::: T] (aka [value has type v T]): 
          value v is the result of evaluating some term of type T.
        - [bs :::* Ls] (aka [bindings_match_decls g G]): 
          [bs] is a list of [(xi,vi)] pairs and [Ls] is a list of declarations,
          [(Lv xi Ti)] and [vi:::Ti] for all [i]; thus [bs]
          has exactly the elements specified by 
          the typing context Ls (in the same order).
        - [t / g =>: T] (aka [may_eval_to t g T]): 
          term t, when evaluated in runtime-context g, 
          will either yield a value [v] such that [v:::T] or not terminate 
          (but it won't get stuck).
        - [Fs / g =>:* Ls] (aka [may_exec_list_to Fs g Ls]): 
          [Fs] is a list of definitions, each [(Fv xi ti)], 
          [Ls] is a list of declarations, each [(Lv xi Ti)], 
          and for each [i], [ti / g =>: Ti]; thus executing [Fs] will 
          either yield a value list [bs], such that [bs :::* Ls] 
          or it won't terminate (but it won't get stuck).
        - [result_ok er T]: [er] (an instance of [ef_return]) is either 
          [efr_normal v] and [v ::: T]
          or [er] is [efr_nogas]; [er] is not [efr_stuck].
        - [result_list_ok xr Ls]: [xr] (an instance of [xf_return]) is either 
          [efr_normal bs] and [bs :::* Ls]
          or [xr] is [efr_nogas]; [xr] is not [efr_stuck].

    If defined as mutually recursive functions, Coq complains about 
    the lack of a non-decreasing argument 
    (which really is decreasing but Coq can't tell).
    It would be nice if there was a way to get around this.
    In the meantime, [value_has_type] is defined with certain others 
    nested within and then the others are defined again
    outside the [value_has_type] definition.
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
  in let may_eval_to (t : tm) (g : rctx) (T : ty) : Prop := 
    forall n, result_ok (evalF t g n) T
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
        forall va, va ::: T1 -> may_eval_to tb (aextend xf va gf) T2
    | ((TRcd Tr), (vrcd vr)) => bindings_match_decls vr Tr 
    | (_, _) => False
  end
where "v ':::' T" := (value_has_type v T).

Fixpoint bindings_match_decls 
           (bs : alist evalue) (Ls : list decl) {struct Ls} : Prop :=
    match (Ls, bs) with
      | (nil, nil) => True
      | ((Lv x T) :: Ls', ((y, v) :: bs')) =>
          x=y /\ v ::: T /\ bindings_match_decls bs' Ls'
      | (_, _) => False
    end.
Notation "g ':::*' G" := (bindings_match_decls g G).

Definition result_ok (er : ef_return) (T : ty) : Prop :=
    match er with
      | efr_normal vr => vr ::: T
      | efr_nogas => True
      | efr_stuck => False
    end.

Definition result_list_ok (er : xf_return) (Ls : list decl) : Prop :=
    match er with
      | efr_normal bs => bs :::* Ls
      | efr_nogas => True
      | efr_stuck => False
    end.

Definition may_eval_to (t : tm) (g : rctx) (T : ty) : Prop := 
    forall n, result_ok (evalF t g n) T.
Notation "t '/' g '=>:' T" := (may_eval_to t g T) 
    (at level 40, g at level 39).

Definition may_exec_list_to (Fs : list def) (g : rctx) (Ls : list decl) : Prop := 
    forall n', result_list_ok (execF_list Fs g n') Ls.
Notation "Fs '/' g '=>:*' Ls" := (may_exec_list_to Fs g Ls) 
    (at level 40, g at level 39).

Hint Unfold value_has_type bindings_match_decls result_ok result_list_ok 
     may_eval_to may_exec_list_to.


(** The following are some alternate definition bodies of [bs:::*Ls] that I've 
    considered: 
<<
    match Ls with
      | nil => True
      | (Lv x T) :: Ls' => (exists v, alookup x bs = Some v /\ v ::: T)
                           /\ bindings_match_decls bs Ls'
    end

   forall x T, lookup_vdecl x Ls = Some T ->
      exists v, alookup x bs = Some v /\ v ::: T

  let decl_implies_lookup bs L := 
    match L with (Lv x T) => exists v, alookup x bs = Some v /\ v ::: T end
  in Forall (decl_implies_lookup bs) Ls.

>>
The following is the original inductive definition:
<<
  Inductive bindings_match_decls: rctx -> context -> Prop :=
    | TC_nil : nil :::* empty
    | TC_cons : forall G g x v T, 
                g :::* G -> v ::: T -> (aextend x v g) :::* (add_vdecl x T G)
  where "g ':::*' G" := (bindings_match_decls g G).
>>
*)

(** Here I redefine [value_has_type] using the above functions 
    and show that it is equivalent.  My thinking was that this
    would avoid the nested definitions, but they don't seem
    to come up, so this isn't used.*)

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


(* ###################################################################### *)
(** ** Lemmas  *)
(** *** A Lemma for induction on [:::*] *)
(** Lemma [bmd_ind] is a handy lemma for doing a form of induction over :::*.
    Use it with the [refine] tactic. *)

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



(** *** Constructor lemmas *)
(** Lemmas that mimic the inductive constructors that would have 
    been defined if Coq allowed us to define our relations that way. *)

Lemma VHT_True :
  vtrue ::: TBool.
Proof. reflexivity. Qed.

Lemma VHT_False :
  vfalse ::: TBool.
Proof. reflexivity. Qed.

Lemma VHT_Abs :
  forall xf tb gf T1 T2,
    (forall va,  va ::: T1 -> tb / (aextend xf va gf) =>: T2) ->
    vabs xf tb gf ::: TArrow T1 T2.
Proof. introv H. simpl. exact H. Qed.

Lemma VHT_Rcd : 
  forall Fs Ls,
    Fs :::* Ls ->
    vrcd Fs ::: TRcd Ls.
Proof. introv H. simpl. exact H. Qed.

Lemma BMDs_nil :
  nil :::* nil.
Proof. simpl. constructor. Qed.

Lemma BMDs_cons : 
  forall G g x v T,
    g :::* G ->
    v ::: T ->
    (aextend x v g) :::* (add_vdecl x T G).
Proof. auto.
  introv HgG HvT. simpl. auto. 
Qed.

Lemma MET:
  forall t g T,
    (forall n er, evalF t g n = er -> result_ok er T) -> 
    (t / g =>: T).
Proof.
  introv H. red. apply (fun n => H n (evalF t g n) eq_refl).
Qed.

Lemma ROk_Norm : 
  forall v T er,
    efr_normal v = er ->
    v ::: T ->
    result_ok er T.
Proof.
  introv Heq Ht. subst. simpl. exact Ht.
Qed.

Lemma RLOk_norm : 
  forall Fs Ls xr,
    efr_normal Fs = xr ->
    Fs :::* Ls ->
    result_list_ok xr Ls.
Proof.
  introv Heq Ht. subst. simpl. exact Ht.
Qed.

(** *** "Inversion" lemmas *)
(**  Lemmas for "inverting" the [value_has_type] function. 
     IN SF, [vht_inv_bool] is called [bool_vals] 
     and [vht_inv_arrow] is called [fun_vals]).*)

Lemma vht_inv_bool: forall v, v ::: TBool -> (v = vtrue \/ v = vfalse).
Proof.
  intros v Hvt. destruct v; try (simpl in Hvt; contradiction); auto.
Qed.

Lemma vht_inv_arrow:
  forall v T1 T2, v ::: TArrow T1 T2 ->
    exists xf tb gf, 
      v = (vabs xf tb gf) 
      /\ (forall va, va ::: T1 -> tb / (aextend xf va gf) =>: T2).
Proof. 
  intros v T1 T2 Hvt.  destruct v; simpl in Hvt; try contradiction.
    exists i t a. split. 
      reflexivity.
      intros va Hvat n. 
        specialize (Hvt va Hvat n). 
        destruct (evalF t (aextend i va a) n); simpl; auto.
Qed.

Lemma vht_inv_rcd :
  forall v Ls, v ::: TRcd Ls ->
    exists bs, v = (vrcd bs) /\ bs :::* Ls.
Proof. 
  intros v Ls Hvt. destruct v as [ | | | bs]; simpl in Hvt; try contradiction.
    exists bs. split. 
      reflexivity.
      assumption.
Qed.

(** The following isn't accepted by Coq (and isn't really needed):
<<
  Lemma vht_inversion :
    forall v T (Hvt : v ::: T), 
      (T=TBool /\ (vht_inv_bool v Hvt))
      \/ (exists T1 T2, T=TArrow T1 T2 /\ vht_inv_arrow v T1 T2 Hvt)
      \/ (exists Ls, T=TRcd Ls /\ vht_inv_rcd v Ls Hvt).
>>
*)

(** The following two lemmas were experiments that didn't work out. 
    They were intended to make it easier to use a hypothesis of the
    form [result_ok ... T] 
    but the inversion one had trouble coming up with [P]
    and the case one required a complicated [destruct]. *)

Lemma ROk_inversion:
  forall (P : ef_return -> ty -> Prop),
    forall er T, 
      result_ok er T ->
      (forall vr, vr ::: T -> P (efr_normal vr) T) ->
      P efr_nogas T ->
      P er T.
Proof.
  intros P er T Hok Hnorm Hng. destruct er; simpl in Hok.
    apply (Hnorm _ Hok).
    apply Hng.
    contradiction.
Qed.

Lemma ROk_case:
  forall er T, 
    result_ok er T -> (
      (exists vr, er = efr_normal vr /\ vr ::: T) \/
      er = efr_nogas ).
Proof.
  intros er T Hok. destruct er as [vr| | ]; simpl in Hok.
    left. exists vr. split. reflexivity. apply Hok.
    right. reflexivity.
    contradiction.
Qed.

(** *** Lemma [ctxts_agree_on_lookup] *)
(** Lemma [ctxts_agree_on_lookup] says that if [bs:::*Ls] and
    a lookup on [Ls] returns [Some T], then the related lookup on [bs]
    returns [Some v] where [v:::T]. *)

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
      apply lookup_add_vdecl_case in Hlk. 
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

(* Version for when :::* was defined inductively:
Lemma ctxts_agree_on_lookup_old : 
  forall (x : id) (G : context) (g : rctx) (T : ty),
    g  :::* G -> 
    lookup_vdecl x G = Some T ->
      exists v, alookup x g = Some v /\ v ::: T.
Proof.
  introv Hctxts HGxT. induction Hctxts.
    Case "BMDs_nil". inversion HGxT.
    Case "BMDs_cons". unfold lookup_vdecl, add_vdecl in HGxT. 
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


(** *** Lemmas for reasoning about contexts (runtime and typing). *)
(** No longer used.    *)

Lemma lookup_implies_in:
  forall x G T,
    lookup_vdecl x G = Some T -> In (Lv x T) G.
Proof.
  introv Hlookup. induction G as [ | [y Ty] G'].
  Case "G=[]". inversion Hlookup.
  Case "G=(Lv y Ty)::G'". 
    apply lookup_add_vdecl_case in Hlookup.
    destruct Hlookup as [[Hxe HTe] | [Hxn Hle]].
    SCase "y=x". inverts HTe. subst. left. reflexivity.
    SCase "y<>x". right. apply (IHG' Hle).
Qed.

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

Lemma ctx_tvar_then_evalsto : forall G x T g,
  G |- (tvar x) \in T -> g :::* G -> (tvar x) / g =>: T.
Proof. 
  introv HG Hg. destruct (ctx_tvar_then_alookup G x T g HG Hg) as [v [Hl Hv]].
  unfold may_eval_to. intro n. destruct n as [ | n' ]; simpl; auto.
    rewrite Hl. auto.
Qed.

(** *** Lemmas for more easily proving [t / g =>: T] and [Fs / g  =>:* Ls] *)
(** These lemmas rearrange things so that the calls to [evalF] and 
    [execF_list] are in hypotheses such that [let_val] and associates 
    can be applied to them.*)

Lemma evalF_parts :
  forall (t : tm) (T : ty) (g : rctx),
    (forall n' er, evalF t g (S n') = er -> result_ok er T) ->
        t / g  =>: T.
Proof.
  introv H. unfold may_eval_to. 
  destruct n  as [ | n' ].
    simpl (evalF _ _ 0). reflexivity. 
    apply (H n' _ eq_refl).
Qed.

Lemma execF_list_parts :
  forall (Fs : list def) (Ls : list decl) (g : rctx),
    (forall n' er, execF_list Fs g n' = er -> result_list_ok er Ls) ->
        Fs / g  =>:* Ls.
Proof.
  exact (fun _ _ _ H n' => H n' _ eq_refl).
Qed.


(** *** Lemmas for reasoning about LETRT forms. *)
(** These lemmas are for reasoning about [LETRT] forms.
    Given a hypothesis, [Hev], of the form [LETRT x <== evalF ... IN ...],
    applying [let_val] with [Hev] as the appropriate parameter will yield 
    subgoals that reason about the let- and in- clauses.

    Because [LETRT] is a notation, it is essentially generic in that it can 
    be used with both [evalF] and [execF_list].  Also the IN clause can be 
    either a singelton or a list.  However, lemmas are not notations,
    so there are four lemmas to handle the different cases. *)

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
      Case "result_list_ok bs1". 
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
      Case "result_list_ok bs1". 
        unfold result_list_ok in Heval. 
        apply (Hin bs1 Heval erf HLet).
Qed.


(* ###################################################################### *)
(**  ** Proof of soundness of evalF *)
(**  *** Proof of [evalF_is_sound_yielding_T] *)
(** This theorem says that if term [t] has type [T],
    then evaluating [t] will either yield a value of type [T]
    or not terminate; in particular, it won't get "stuck".

   The proof is by induction on [t] using the custom induction principle
   so that records are handled correctly.  For each case, the typing relation
   is inverted to yield type assertions about the components of [t] and
   [evalF_parts] (or [execF_list_parts]) and [simpl] are applied ending
   up with the appropriate clause of [evalF] in [Hev].
*) 

  
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
    exact (ROk_Norm _ _ _ Hev VHT_True).

  Case "tfalse".
    exact (ROk_Norm _ _ _ Hev VHT_False).

  Case "tvar". 
    destruct (ctxts_agree_on_lookup _ _ HGg _ _ H1) as [v [Hlk Hvt]].
    rewrite Hlk in Hev. exact (ROk_Norm _ _ _ Hev Hvt).

  Case "tapp".
    (* use IHs to get [Ht1 : t1 / g =>: TArrow T11 T] & [Ht2 : t2 / g =>: T11].  *)
    assert (Ht1 := IHt1 _ _ _ H2 HGg); clear IHt1 H2.
    assert (Ht2 := IHt2 _ _ _ H4 HGg); clear IHt2 H4.
    (* use the [let_val] lemma with Ht1 and Ht2 to decompose the two LETRT forms *)
    apply (let_val t1 g n' _ _ _ T Hev Ht1); clear Hev Ht1;
    intros v1 Hv1t erL2 HevL2.
    apply (let_val t2 g n' _ _ _ _ HevL2 Ht2); clear HevL2 Ht2;
    intros v2 Hv2t erf Hevf.
    assert (Hex := vht_inv_arrow _ _ _ Hv1t); clear Hv1t;
    destruct Hex as (xf & tb & gf & Hv1eq & Hva); subst v1 erf.
    apply (Hva v2 Hv2t n').

  Case "tabs". 
    apply (ROk_Norm _ _ _ Hev); clear Hev.
    apply VHT_Abs; intros va Hvat.
    apply (IHtb _ _ (aextend x va g) H4). clear IHtb.
    apply (BMDs_cons _ _ _ _ _ HGg Hvat).

  Case "trcd". 
    rewrite <- (execF_list_eq Fs g n') in Hev.
    assert (HFs := IHFs _ _ _ H1 HGg); clear IHFs H1.
    apply (let_vlist _ g n' _ _ _ _ Hev HFs); clear Hev HFs;
    intros bs Hbst er2 Hev2. 
    apply (ROk_Norm _ _ _ Hev2 (VHT_Rcd _ _ Hbst)).

  Case "trnil".
    apply (RLOk_norm _ _ _ Hev BMDs_nil). 

  Case "trcons".
    assert (Ht := IHt _ _ _ H4 HGg); clear IHt H4.
    assert (HFs := IHFs _ _ _ H5 HGg); clear IHFs H5.
    apply (list_let_val tx g n' _ _ T _ Hev Ht); clear Hev Ht;
    intros v1 Hv1t erL2 HevL2.
    apply (list_let_vlist _ g n' _ _ Tr _ HevL2 HFs); clear HevL2 HFs;
    intros bs2 Hbs2t erf Hevf. 
    apply (RLOk_norm _ _ _ Hevf).
    apply (BMDs_cons _ _ _ _ _ Hbs2t Hv1t).

  Case "tproj". 
    assert (Htr := IHtr _ _ _ H2 HGg); clear IHtr H2.
    apply (let_val tr g n' _ _ _ _ Hev Htr); clear Hev Htr; 
    intros vr Hvrt erp Hevp.
    destruct (vht_inv_rcd _ _ Hvrt) as [bs [? HbsT ]]. subst vr.
    destruct (ctxts_agree_on_lookup _ _ HbsT _ _ H4) as [v [Hlk HvT]].
    rewrite Hlk in Hevp. 
    apply (ROk_Norm _ _ _ Hevp HvT).

  Case "tif".
    assert (Hti := IHti _ _ _ H3 HGg); clear IHti H3.
    apply (let_val ti g n' _ _ _ _ Hev Hti); clear Hev Hti;
    intros vi Hvit erc Hevc.
    destruct (vht_inv_bool vi Hvit); subst.
      SSCase "v = vtrue". apply (IHtt _ _ _ H5 HGg n').
      SSCase "v = vfalse". apply (IHte _ _ _ H6 HGg n').

Qed.

(**  *** Proof of [evalF_is_sound] *)
(** This says that if [t] is well-typed, its evaluation will not get stuck. *)

Corollary evalF_is_sound: 
  forall (t : tm) (G : context) (T : ty) (g : rctx) (n : nat),
    G |- t \in T ->  g :::* G -> evalF t g n  <> efr_stuck.
Proof.
  introv Hty HGg.
  assert (Hr := evalF_is_sound_yielding_T _ _ _ _ Hty HGg n).
  destruct (evalF t g n); try discriminate.
     simpl in Hr; contradiction.
Qed.
