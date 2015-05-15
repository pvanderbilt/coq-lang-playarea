(** * LDef: Definition of an STLC-based language.  *)

(** This is SF's Stlc with Gamma change to be a list of declarations.
*)

Add LoadPath "~/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

Module LDEF.

(* ###################################################################### *)
(** ** Syntax *)


(* ################################### *)
(** *** Types *)

Inductive ty : Type := 
  | TBool  : ty 
  | TArrow : ty -> ty -> ty.

(* ################################### *)
(** *** Terms *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "ttrue" 
  | Case_aux c "tfalse" | Case_aux c "tif" ].



(* ###################################################################### *)
(** ** Operational Semantics *)

(* ################################### *)
(** *** Values *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse.

Hint Constructors value.

(* ###################################################################### *)
(** *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue => 
      ttrue
  | tfalse => 
      tfalse
  | tif t1 t2 t3 => 
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(** _Technical note_: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables.
    Since we are only interested here in defining the [step] relation
    on closed terms (i.e., terms like [\x:Bool. x], that do not mention
    variables are not bound by some enclosing lambda), we can skip
    this extra complexity here, but it must be dealt with when
    formalizing richer languages. *)


(* ################################### *)
(** *** Reduction *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue" 
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" := 
   repeat (print_goal; eapply multi_step ; 
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.

(* ###################################################################### *)
(** ** Typing *)

(* ################################### *)
(** *** Contexts *)

Inductive decl :=
  | Lv : id -> ty -> decl.

Definition context := list decl.
Definition empty := nil (A:=decl).
Definition extend (Gamma : context) (x : id) (T : ty) := (Lv x T) :: Gamma.
Fixpoint lookup_vdecl (x : id) (Gamma : context) := 
  match Gamma with 
    | nil => None 
    | (Lv y T) :: Ls' => if eq_id_dec y x then Some T else lookup_vdecl x Ls'
  end.

Lemma extend_eq : forall (ctxt: context) x T,
  lookup_vdecl x (extend ctxt x T) = Some T.
Proof.
  intros. unfold extend, lookup_vdecl. rewrite eq_id; auto. 
Qed.

Lemma extend_neq : forall (ctxt: context) x1 x2 T,
  x2 <> x1 ->
  lookup_vdecl x1 (extend ctxt x2 T) = lookup_vdecl x1 ctxt.
Proof.
  intros. unfold extend, lookup_vdecl. rewrite neq_id; auto. 
Qed.

Lemma extend_shadow : forall (ctxt: context) t1 t2 x1 x2,
  lookup_vdecl x1 (extend (extend ctxt x2 t1) x2 t2)  
    = lookup_vdecl x1 (extend ctxt x2 t2).
Proof with auto.
  intros. unfold extend, lookup_vdecl. destruct (eq_id_dec x2 x1)...
Qed.

(* ################################### *)
(** *** Typing Relation *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      lookup_vdecl x Gamma = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_True" 
  | Case_aux c "T_False" | Case_aux c "T_If" ].

Hint Constructors has_type.

End LDEF.

(** $Date: $ *)

