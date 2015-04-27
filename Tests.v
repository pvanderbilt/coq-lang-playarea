(** * Tests: tests related to LDEF. Currently just Pierce's examples. *)

(** ** Tests: Pierce's examples: tests related to small step semantics. *)

Add LoadPath  "~/Polya/coq/pv".
Add LoadPath  "~/Polya/coq/pierce_software_foundations_3.2".

Require Export LDef.
Import LDEF.

(** *** Definitions *)

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(** [idB = \x:Bool. x] *)

Notation idB := 
  (tabs x TBool (tvar x)).

(** [idBB = \x:Bool->Bool. x] *)

Notation idBB := 
  (tabs x (TArrow TBool TBool) (tvar x)).

(** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)

Notation idBBBB :=
  (tabs x (TArrow (TArrow TBool TBool) 
                      (TArrow TBool TBool)) 
    (tvar x)).

(** [k = \x:Bool. \y:Bool. x] *)

Notation k := (tabs x TBool (tabs y TBool (tvar x))).

(** [notB = \x:Bool. if x then false else true] *)

Notation notB := (tabs x TBool (tif (tvar x) tfalse ttrue)).


(** (We write these as [Notation]s rather than [Definition]s to make
    things easier for [auto].) *)
(* ##################################### *)
(** *** Examples *)

(** Example:
    ((\x:Bool->Bool. x) (\x:Bool. x)) ==>* (\x:Bool. x)
i.e.
    (idBB idB) ==>* idB
*)

Lemma step_example1 :
  (tapp idBB idB) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.  Qed.  

(** Example:
((\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x))) 
      ==>* (\x:Bool. x)
i.e.
  (idBB (idBB idB)) ==>* idB.
*)

Lemma step_example2 :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.  Qed. 

(** Example:
((\x:Bool->Bool. x) (\x:Bool. if x then false
                              else true)) true)
      ==>* false
i.e.
  ((idBB notB) ttrue) ==>* tfalse.
*)

Lemma step_example3 :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. 
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_IfTrue. apply multi_refl.  Qed. 

(** Example:
((\x:Bool -> Bool. x) ((\x:Bool. if x then false
                               else true) true))
      ==>* false
i.e.
  (idBB (notB ttrue)) ==>* tfalse.
*)

Lemma step_example4 :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. 
  eapply multi_step.
    apply ST_App2. auto. 
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto. 
    apply ST_IfTrue. 
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl.  Qed. 


(** A more automatic proof *)

Lemma step_example1' :
  (tapp idBB idB) ==>* idB.
Proof. normalize.  Qed.  

(** Again, we can use the [normalize] tactic from above to simplify
    the proof. *)

Lemma step_example2' :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  normalize.
Qed. 

Lemma step_example3' :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. normalize.  Qed.  

Lemma step_example4' :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. normalize.  Qed.  

(** **** Exercise: 2 stars (step_example3)  *)  
(** Try to do this one both with and without [normalize]. *)

Lemma step_example5 :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof. (* FILLED IN  *)
(*
  eapply multi_step; eauto; try instantiate; simpl.
  eapply multi_step; eauto; try instantiate; simpl.
  apply multi_refl. *)
  repeat (eapply multi_step; eauto; try instantiate; simpl; try apply multi_refl).
  (* In this file, coq infinitie-looped without the final try. *)
Qed.
(** [] *)

(* ################################### *)
(** *** Examples *)

Example typing_example_1 :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

(** Note that since we added the [has_type] constructors to the hints
    database, auto can actually solve this one immediately. *)

Example typing_example_1' :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof. auto.  Qed.

(** Another example:
     empty |- \x:A. \y:A->A. y (y x)) 
           \in A -> (A->A) -> A.
*)

Example typing_example_2 :
  empty |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof with auto using extend_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

(** **** Exercise: 2 stars, optional (typing_example_2_full)  *)
(** Prove the same result without using [auto], [eauto], or
    [eapply]. *)

Example typing_example_2_full :
  empty |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof.
  (* FILLED IN *)
  apply T_Abs.
  apply T_Abs.
  apply T_App with (T11:=TBool). apply T_Var. apply extend_eq.
  apply T_App with TBool. apply T_Var. apply extend_eq.
  apply T_Var. apply extend_neq. unfold not. intro HP. inversion HP. 
Qed.
(* Why is not "apply extend_eq" needed in the last line? *)
(* As discovered below, "reflexivity" can be used after "apply T_Var".  
    I leave this as a way to deal with contexts that are not gound. *)
(** [] *)

Lemma extend_neq' : forall A (ctxt: partial_map A) x1 T2 x2 R,
  x2 <> x1 ->
  ctxt x1 = R ->
  (extend ctxt x2 T2) x1 = R.
Proof.
  intros. unfold extend. rewrite neq_id; auto.
Qed.

Example typing_example_2_full' :
  forall (ctxt : context),
  ctxt |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof.
  (* DONE OVER *)
  intro.
  apply T_Abs.
  apply T_Abs.
  apply T_App with (T11:=TBool). apply T_Var. apply extend_eq.
  apply T_App with TBool. apply T_Var. reflexivity. (* it DOES work. *)
  apply T_Var. apply extend_neq'. discriminate. apply extend_eq.
Qed.


(** **** Exercise: 2 stars (typing_example_3)  *)
(** Formally prove the following typing derivation holds: *)
(** 
   empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool.
               y (x z) 
         \in T.
*)

Example typing_example_3 :
  exists T, 
    empty |-
      (tabs x (TArrow TBool TBool)
         (tabs y (TArrow TBool TBool)
            (tabs z TBool
               (tapp (tvar y) (tapp (tvar x) (tvar z)))))) \in
      T.
Proof with auto.
  (* FILLED IN *)
  eexists. 
  eapply T_Abs.
  eapply T_Abs.
  eapply T_Abs.
  eapply T_App. apply T_Var. reflexivity.
  eapply T_App. apply T_Var. reflexivity.
  apply T_Var. reflexivity.
Qed.
(** [] *)

(** We can also show that terms are _not_ typable.  For example, let's
    formally check that there is no typing derivation assigning a type
    to the term [\x:Bool. \y:Bool, x y] -- i.e.,
    ~ exists T,
        empty |- \x:Bool. \y:Bool, x y : T.
*)

Example typing_nonexample_1 :
  ~ exists T,
      empty |- 
        (tabs x TBool
            (tabs y TBool
               (tapp (tvar x) (tvar y)))) \in
        T.
Proof.
  intros Hc. inversion Hc as [T].
  clear Hc. (* Added this and "as" above *)
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  (* rewrite extend_neq in H1. rewrite extend_eq in H1. *)
  inversion H1.  Qed.

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs x S
             (tapp (tvar x) (tvar x))) \in
          T).
Proof.
  (* FILLED IN *) 
  intros Hc. inversion Hc as [S [T H1]]. clear Hc.
  inversion H1; subst; clear H1.
  inversion H5; subst; clear H5.
  inversion H2; subst; clear H2.
  inversion H4; subst; clear H4.
  rewrite H1 in H2. inversion H2. clear H1 H2.
  induction T11. 
    inversion H0. 
    inversion H0. apply IHT11_1. rewrite H2. apply H1.
Qed.
(** [] *)


