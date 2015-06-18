(** * LDef: STLC with records (as lists). *)

(** This file started out as SF's Records.v but has been modified to 
    have records as lists of declarations (in contrast to SF's approach). *)

Load Init.
Require Export SfLib.
Require Import LibTactics.

Require Export Common.
Import Common.


(* ###################################################################### *)

(**  ** SYNTAX:
<<
       t ::=                          Terms:
           | true, false                 boolean values
           | x                           variable
           | t1 t2                       application
           | \x:T1.t2                    abstraction
           | {F1; ...; Fn}               record 
           | t.i                         projection
           | if tb then te else tf       conditional
       T ::=                          Types:
           | X                           base type (not used)
           | Bool                        boolean type
           | T1 -> T2                    function type
           | {L1; ...; Ln}               record type
       F ::=                          Definitions:
           | val x = t                   bind value to id
       L ::=                          Declarations:
           | val x : T                   id has type
>> 
*)

(**  *** Types [ty] *)

Inductive ty : Type :=
  | TBase     : id -> ty
  | TBool     : ty
  | TArrow    : ty -> ty -> ty
  | TRcd      : (list decl) -> ty
with decl : Type :=
  | Lv        : id -> ty -> decl.

(** *** Terms [tm] *)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar  : id -> tm
  | tapp  : tm -> tm -> tm
  | tabs  : id -> ty -> tm -> tm
  | trcd  : list def -> tm
  | tproj : tm -> id -> tm
  | tif : tm -> tm -> tm -> tm
with def : Type :=
  | Fv    : id -> tm -> def.

(** In SF there is an observation about how an embedded list doesn't 
    give a useful induction principle, so they have
    the following for types:
<<
      | TRNil : ty
      | TRCons : id -> ty -> ty -> ty
>>
    Since this allows TRCons to be applied to non-record components,
    they have a way to tell whether types are well-formed.  The same
    thing applies to terms.

    Instead, we use a list of declarations and fix the induction 
    principle.  Similarly, record terms are lists of definitions.
*)

(** *** "Case" tactic notations and [tm_ind_tactic]  *)

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TBase" | Case_aux c "TBool" 
  | Case_aux c "TArrow" | Case_aux c "TRcd" ].

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ttrue" | Case_aux c "tfalse" 
  | Case_aux c "tvar" | Case_aux c "tapp" | Case_aux c "tabs"
  | Case_aux c "trcd" | Case_aux c "tproj"| Case_aux c "tif" ].

Ltac tm_ind_tactic t C := 
  t_cases (induction t as 
    [ | | x | t1 IHt1 t2 IHt2 | x Tx tb IHtb | Fs | tr IHtr x 
    | ti IHti tt IHtt te IHte ] using tm_rect) C.
  


(** *** Functions and lemmas for dealing with definition and declaration lists *)

Definition add_vdef x t Fs := (Fv x t) :: Fs.
Definition add_vdecl x T Ls := (Lv x T) :: Ls.

Fixpoint lookup_vdef x Fs := 
  match Fs with 
    | nil => None 
    | (Fv y t) :: Fs' => 
        if eq_id_dec y x then Some t else lookup_vdef x Fs'
    (* | _ :: Fs' => lookup_vdef x Fs' *)
  end.

Fixpoint lookup_vdecl x Ls := 
  match Ls with 
    | nil => None 
    | (Lv y T) :: Ls' => 
        if eq_id_dec y x then Some T else lookup_vdecl x Ls'
  end.

Lemma lookup_add_vdef_eq : 
  forall (x : id) (t : tm) (Fs : list def),
    lookup_vdef x (add_vdef x t Fs) = Some t.
Proof.
  intros. simpl. apply eq_id.
Qed.

Lemma lookup_add_vdef_neq :
  forall (x y : id) (t : tm) (Fs : list def),
    y <> x ->
    lookup_vdef x (add_vdef y t Fs) = lookup_vdef x Fs.
Proof.
  intros. simpl. apply neq_id. apply H.
Qed.

Lemma lookup_add_vdecl_eq : 
  forall (x : id) (T : ty) (Ls : list decl),
    lookup_vdecl x (add_vdecl x T Ls) = Some T.
Proof.
  intros. simpl. apply eq_id.
Qed.

Lemma lookup_add_vdecl_neq :
  forall (x y : id) (T : ty) (Ls : list decl),
    y <> x ->
    lookup_vdecl x (add_vdecl y T Ls) = lookup_vdecl x Ls.
Proof.
  intros. simpl. apply neq_id. apply H.
Qed.

Lemma lookup_add_vdecl_shadow : forall (ctxt: list decl) t1 t2 x1 x2,
  lookup_vdecl x1 (add_vdecl x2 t2 (add_vdecl x2 t1 ctxt))  
    = lookup_vdecl x1 (add_vdecl x2 t2 ctxt).
Proof with auto.
  intros. unfold add_vdecl, lookup_vdecl. destruct (eq_id_dec x2 x1)...
Qed.

(** Lemma [lookup_add_vdecl_case] allows one to more easily handle the
    two possible cases of [lookup_vdecl] after [add_vdecl] (except as a cons).
    Move to generic code. *)

Lemma lookup_add_vdecl_case :
  forall x y T Ls' r, 
    lookup_vdecl x (add_vdecl y T Ls') = r ->
    (y=x /\ Some T = r) \/ (y<>x /\ lookup_vdecl x Ls' = r).
Proof.
  introv Hlk.
  unfold lookup_vdecl, add_vdecl in Hlk.
  destruct (eq_id_dec y x) as [ He | Hne].
    SCase "y=x". left. auto.
    SCase "y<>x". fold lookup_vdecl in Hlk. right. auto. 
Qed.

(** A previous attempt at an induction-like rule for casing on the outcome of
    lookup over add. The rule can be proved, but I can't figure out
    how to apply it to prove [ctxts_agree_on_lookup]. *)

Lemma lookup_add_vdecl_case_old :
  forall (P : id -> id -> ty -> list decl -> option ty -> Prop)
    (Heq : forall x T Ls' r, r = Some T -> P x x T Ls' r)
    (Hneq : forall x y T Ls' r, r = (lookup_vdecl x Ls') -> y<>x -> P x y T Ls' r),
    forall x y T Ls' r, lookup_vdecl x (add_vdecl y T Ls') = r ->
      P x y T Ls' r.
Proof.
  intros P Heq Hneq x y T Ls' r Hlk.
  unfold lookup_vdecl, add_vdecl in Hlk.
  destruct (eq_id_dec y x) as [ He | Hne].
    SCase "y=x". subst. apply Heq. reflexivity.
    SCase "y<>x". fold lookup_vdecl in Hlk.
      subst r. apply (Hneq _ _ _ _ _ eq_refl Hne).
Qed.



(* ###################################################################### *)
(** ** Custom recursion principles. *)

(** *** Extended recursion on types, [ty_xrect]

    The coq-generated recursion principle for types ([ty]) has the following type:
<< 
  ty_rect : 
    forall P : ty -> Type,
      (forall i : id, P (TBase i)) ->
      P TBool ->
      (forall t : ty, P t -> forall t0 : ty, P t0 -> P (TArrow t t0)) ->
      (forall r : list decl, P (TRcd r)) -> (* records *)
    forall t : ty, P t
>>

    Notice that the "step" function for records has type
    [forall r : list decl, P (TRcd r))], 
    which does not provide recursive applications for the [ty] values within the
    list of declarations.
    
    The following custom recursion principle replaces the records case 
    with four:
      - an additional proposition function [Q] over [list decl] (at the top),
      - a proof that for record body type, [Trb], [Q Trb] implies [P (TRcd Trb)],
      - a proof of [Q nil] and
      - a proof that [P T] and [Q Trb] implies [Q (cons x T Trb))]
*)

Definition ty_xrect
  (P: ty -> Type) 
  (Q: list decl -> Type)
    (fTBase : forall x : id, P (TBase x))
    (fTBool : P (TBool))
    (fTArrow : forall T1 : ty, P T1 -> forall T2 : ty, P T2 -> P (TArrow T1 T2))
    (fTRcd' : forall Trb : list decl, Q Trb -> P (TRcd Trb))
      (fTRcd_nil' : Q nil)
      (fTRcd_cons' : forall (x : id) (T : ty) (Trb : list decl), 
                       P T -> Q Trb -> Q ((Lv x T) :: Trb))
  : forall T : ty, P T
  := fix F (T : ty) : P T :=
     let fix G (Trb : list decl) : Q Trb :=
         match Trb with
           | nil => fTRcd_nil'
           | (Lv x T) :: Trb' => fTRcd_cons' x T Trb' (F T) (G Trb')
         end
     in match T with
       | TBase x => fTBase x
       | TBool => fTBool
       | TArrow T1 T2 => fTArrow T1 (F T1) T2 (F T2)
       | TRcd Trb => fTRcd' Trb (G Trb)
     end.



(** *** Extended recursion on terms, [tm_xrect]

    Here is the extended recursion principle for terms [tm].
    This version directly delegates to the recursion principles for
    lists and terms, [list_rect] and [tm_rect].
*)

Definition tm_xrect
  (P: tm -> Type) 
  (Q: list def -> Type)
    (ftrue : P ttrue)
    (ffalse : P tfalse)
    (fvar : forall x : id, P (tvar x))
    (fapp : forall t1 : tm, P t1 -> forall t2 : tm, P t2 -> P (tapp t1 t2))
    (fabs : forall (x : id) (T : ty) (t : tm), P t -> P (tabs x T t))
    (frcd' : forall rb : list def, Q rb -> P (trcd rb))
      (frcd_nil' : Q nil)
      (frcd_cons' : forall (x : id) (t : tm) (rb : list def),
                      P t -> Q rb -> Q ((Fv x t) :: rb))
    (fproj : forall t : tm, P t -> forall x : id, P (tproj t x)) 
    (fif : forall tb : tm, P tb -> 
           forall tt : tm, P tt -> 
           forall te : tm, P te -> P (tif tb tt te)) 
  : forall t : tm, P t
  := fix F (t : tm) : P t := 
    let frcd_cons bxt rb := match bxt with (Fv x t) => frcd_cons' x t rb (F t) end
    in let frcd rb := frcd' rb (list_rect Q frcd_nil' frcd_cons rb)
    in tm_rect P ftrue ffalse fvar fapp fabs frcd fproj fif t.

(** *** [tm_xind_tactic] extended induction tactic *)

Tactic Notation "t_xcases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ttrue" | Case_aux c "tfalse" 
  | Case_aux c "tvar" | Case_aux c "tapp" | Case_aux c "tabs"
  | Case_aux c "trcd" | Case_aux c "trnil" | Case_aux c "trcons"
  | Case_aux c "tproj" | Case_aux c "tif" ].

Ltac tm_xind_tactic t Qv C := 
  t_xcases (induction t 
    as [ | | ?x | ?t1 ?IHt1 ?t2 ?IHt2 | ?x ?Tx ?tb ?IHtb | ?Fs ?IHFs | 
         | ?x ?tx ?Fs ?IHt ?IHFs | ?tr ?IHtr ?x 
         | ?ti ?IHti ?tt ?IHtt ?te ?IHte ]
    using tm_xrect with (Q:=Qv)) C.


(* ###################################################################### *)
(** ** Reduction *)
(** *** Substitution *)

(**  Coq complains when [subst] is defined with [Fixpoint ... with] 
     as it cannot figure out that the term is not increasing in the 
     [with] clause.  While [subst] can be defined using the custom
     recursion defined above, in proofs it simplifies to a mess 
     that I can't fold back up.
     Instead, [subst] is defined with a nested fixpoint, as follows: 
*)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).
Reserved Notation "'[' x ':=' s ']*' r" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) {struct t} : tm :=
  let fix rsubst (a: list def) : list def := 
    match a with
      | nil => nil 
      | (Fv i t) :: r' => (Fv i ([x:=s] t)) :: (rsubst r')
    end
  in
  match t with
    | ttrue => ttrue
    | tfalse => tfalse
    | tvar y => if eq_id_dec x y then s else t
    | tabs y T t1 =>  tabs y T (if eq_id_dec x y then t1 else (subst x s t1))
    | tapp t1 t2 => tapp ([x:=s] t1) ([x:=s] t2)
    | trcd r => trcd (rsubst r)
    | tproj t1 i => tproj ([x:=s] t1) i
    | tif t1 t2 t3 => tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(**  This substitution assumes that [s] is closed,
     which is OK since the step relation is only defined on closed terms.
     This would need to change if [s] was allowed to have free variables.*)

(**  In order to make the nested fixpoint visible, it is defined again as
     [subst_rcd] and a lemma is given that supports rewriting the nested
     fixpoint to it. *)

Fixpoint subst_rcd (x:id) (s:tm) (a: list def) : list def := 
  match a with
    | nil => nil 
    | (Fv i t) :: rb' => (Fv i ([x:=s] t)) :: ([x:=s]* rb')
  end

where "'[' x ':=' s ']*' r" := (subst_rcd x s r).


Lemma subst_rcd_eqv :
  forall x s a,
    [x := s]* a =
    ((fix rsubst (a0 : list def) : list def :=
         match a0 with
         | nil => nil
         | (Fv i t) :: r' => (Fv i ([x := s]t)) :: (rsubst r')
         end) a).
Proof.
  intros. induction a.
    reflexivity.
    simpl. rewrite <- IHa. reflexivity.
Qed.




(* ###################################################################### *)


(** *** Values 
<<
       v ::=                          Values:
           | true | false                boolean values
           | \x:T.t                      abstractions
           | {i1=v1, ..., in=vn}         record values
>> 
Note that a record is a value if all of its fields are. *)


Inductive value : tm -> Prop :=
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse
  | v_abs : forall x T11 t12,
      value (tabs x T11 t12)
  | v_rcd : forall r, 
      value_rcd r -> 
      value (trcd r)

with value_rcd : (list def) -> Prop :=
  | vr_nil : 
      value_rcd nil
  | vr_cons : forall x v1 vr,
      value v1 ->
      value_rcd vr ->
      value_rcd (add_vdef x v1 vr).

Hint Constructors value value_rcd.


(** *** Reduction rules
<<
                               value v2
                     ----------------------------                   (ST_AppAbs)
                     (\x:T.t12) v2 ==> [x:=v2]t12

                              t1 ==> t1'
                           ----------------                           (ST_App1)
                           t1 t2 ==> t1' t2

                              value v1
                              t2 ==> t2'
                           ----------------                           (ST_App2)
                           v1 t2 ==> v1 t2'

                                 t1 ==> t1'
                               --------------                        (ST_Proj1)
                               t1.i ==> t1'.i

                          -------------------------                (ST_ProjRcd)
                          {..., i=vi, ...}.i ==> vi

                                 ti ==> ti'                            (ST_Rcd)
    --------------------------------------------------------------------  
    {i1=v1, ..., im=vm, in=tn, ...} ==> {i1=v1, ..., im=vm, in=tn', ...}

                    --------------------------------                (ST_IfTrue)
                    (if true then t1 else t2) ==> t1

                    ---------------------------------              (ST_IfFalse)
                    (if false then t1 else t2) ==> t2

                              t1 ==> t1'
         ----------------------------------------------------           (ST_If)
         (if t1 then t2 else t3) ==> (if t1' then t2 else t3)

>> 
*)

Reserved Notation "t1 '==>' t2" (at level 40).
Reserved Notation "rb1 '*==>' rb2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (tapp (tabs x T11 t12) v2) ==> ([x:=v2]t12)
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tapp t1 t2) ==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tapp v1 t2) ==> (tapp v1 t2')
  | ST_Proj1 : forall t1 t1' i,
        t1 ==> t1' ->
        (tproj t1 i) ==> (tproj t1' i)
  | ST_ProjRcd : forall r x vx,
        value_rcd r ->
        lookup_vdef x r = Some vx ->
        (tproj (trcd r) x) ==> vx
  | ST_Rcd : forall rb rb',
        rb *==> rb' ->
        (trcd rb) ==> (trcd rb')
  | ST_IfTrue : forall t1 t2,
        (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
        (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
        t1 ==> t1' ->
        (tif t1 t2 t3) ==> (tif t1' t2 t3)

with step_rcd : (list def) -> (list def) -> Prop := 
  | STR_Head : forall x t t' rb,
        t ==> t' ->
        (add_vdef x t rb) *==> (add_vdef x t' rb)
  | STR_Tail : forall x v rb rb',
        value v ->
        rb *==> rb' ->
        (add_vdef x v rb) *==> (add_vdef x v rb')

where "t1 '==>' t2" := (step t1 t2)
and "rb1 '*==>' rb2" := (step_rcd rb1 rb2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
  | Case_aux c "ST_Proj1" | Case_aux c "ST_ProjRcd" | Case_aux c "ST_Rcd" 
  | Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"].

Tactic Notation "step_rcd_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "STR_Head" | Case_aux c "STR_Tail" ].

Hint Constructors step step_rcd.

(** *** Multi-step *)

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(** **** Normalization tactics *)

Tactic Notation "normalize" := 
   repeat (eapply multi_step ; 
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.

(* Verbose version: *)

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize_v" := 
   repeat (print_goal; eapply multi_step ; 
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.

 

(* ###################################################################### *)
(** ** Typing *)

(** *** Contexts *)

Definition context := list decl.
Definition empty := nil (A:=decl).

(** *** Typing rules:
<<
                             Gamma x = T
                            --------------                              (T_Var)
                            Gamma |- x : T

                      Gamma , x:T11 |- t12 : T12
                     ----------------------------                       (T_Abs)
                     Gamma |- \x:T11.t12 : T11->T12

                        Gamma |- t1 : T11->T12
                          Gamma |- t2 : T11
                        ----------------------                          (T_App)
                         Gamma |- t1 t2 : T12

               Gamma |- [i1=t1, ..., in=tn] *: [1:T1, ..., in:Tn]
             --------------------------------------------------         (T_Rcd)
             Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn}

                       Gamma |- t : {..., i:Ti, ...}
                       -----------------------------                   (T_Proj)
                             Gamma |- t.i : Ti

                         --------------------                          (T_True)
                         Gamma |- true : Bool

                        ---------------------                         (T_False)
                        Gamma |- false : Bool

       Gamma |- t1 : Bool    Gamma |- t2 : T    Gamma |- t3 : T
       --------------------------------------------------------          (T_If)
                  Gamma |- if t1 then t2 else t3 \in : T  

                        -------------------                            (TR_Nil)
                        Gamma |- []  *:  []

                           Gamma |- t : T
                          Gamma |- tr *: Tr
                  ---------------------------------                   (TR_Cons)
                  Gamma |- i=t :: tr  *:  i:T :: Tr
>> 
*)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
Reserved Notation "Gamma '|-' r '*\in' Tr" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      lookup_vdecl x Gamma = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T1 T2 tb,
      add_vdecl x T1 Gamma |- tb \in T2 -> 
      Gamma |- (tabs x T1 tb) \in (TArrow T1 T2)
  | T_App : forall Gamma T1 T2 t1 t2,
      Gamma |- t1 \in (TArrow T1 T2) -> 
      Gamma |- t2 \in T1 -> 
      Gamma |- (tapp t1 t2) \in T2
  | T_Rcd : forall Gamma tr Tr,
      Gamma |- tr *\in Tr ->
      Gamma |- (trcd tr) \in (TRcd Tr)
  | T_Proj : forall Gamma x t Tx Tr,
      Gamma |- t \in (TRcd Tr) ->
      lookup_vdecl x Tr = Some Tx ->
      Gamma |- (tproj t x) \in Tx
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall Gamma t1 t2 t3 T,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

with rcd_has_type : context -> (list def) -> (list decl) -> Prop :=
  | TR_Nil : forall Gamma,
      Gamma |- nil *\in nil
  | TR_Cons : forall Gamma x t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr *\in Tr ->
      Gamma |- (add_vdef x t tr) *\in (add_vdecl x T Tr)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T)
and   "Gamma '|-' r '*\in' Tr" := (rcd_has_type Gamma r Tr).

Hint Constructors has_type rcd_has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Rcd" | Case_aux c "T_Proj" 
  | Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If" ].

Tactic Notation "rcd_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TR_Nil" | Case_aux c "TR_Cons" ].

(** *** Extended induction principle for [has_type] *)

Scheme has_type_xind := Minimality for has_type Sort Prop
with rcd_has_type_xind := Minimality for rcd_has_type Sort Prop.

Tactic Notation "has_type_xcases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Rcd" | Case_aux c "T_Proj" 
  | Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "TR_Nil" | Case_aux c "TR_Cons" ].

Ltac has_type_xind_tactic Hht Qv C := 
  has_type_xcases (induction Hht 
    as [ ?Gamma ?x ?T ?Hlk | ?Gamma ?x ?T1 ?T2 ?tb ?Htb ?IHHtb
         | ?Gamma ?T1 ?T2 ?t1 ?t2 ?Ht1 ?IHHt1 ?Ht2 ?IHHt2 
         | ?Gamma ?tr ?Tr ?Htr ?IHHtr 
         | ?Gamma ?x ?t ?Tx ?Tr ?Ht ?IHHt ?Hlk
         | ?Gamma | ?Gamma 
         | ?Gamma ?tb ?tt ?te ?T ?Htb ?IHHtb ?Htt ?IHHtt ?Hte ?IHHte
         | ?Gamma | ?Gamma ?x ?t ?T ?tr ?Tr ?Ht ?IHHt ?Htr ?IHHtr ]
    using has_type_xind with (P0:=Qv)) C.

