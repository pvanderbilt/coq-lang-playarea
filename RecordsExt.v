(** * RecordsExt: Adding Records to STLC *)

(** This file started out as SF's Records.v but has been modified to 
    have records as association lists. *)

Add LoadPath "/Users/pv/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

(* Require Export Stlc. *)
Require Export Common LDef.
Import P3Common.
Import LDEF.

Module Records.

(* ###################################################################### *)

(**  ** Syntax:
<<
       t ::=                          Terms:
           | ...
           | {i1=t1, ..., in=tn}         record 
           | t.i                         projection

       v ::=                          Values:
           | ...
           | {i1=v1, ..., in=vn}         record value

       T ::=                          Types:
           | ...
           | {i1:T1, ..., in:Tn}         record type
>> 
*)

(**  *** Redefinition of types, [ty].
      The last clause was added: *)

Inductive ty : Type :=
  | TBase     : id -> ty
  | TArrow    : ty -> ty -> ty
  | TRcd      : (alist ty) -> ty.

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TBase" | Case_aux c "TArrow" | Case_aux c "TRcd" ].

(** In SF there is a note here about how this doesn't give the 
    induction principle we want.
    Here we do it this way and fix the induction principle. *)

(**  *** Redefinition of terms, [tm].
        The last two clauses were added: *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tproj : tm -> id -> tm
  | trcd: alist tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" | Case_aux c "tabs"
  | Case_aux c "tproj" | Case_aux c "trcd"  ].

(** Some variables, for examples... *)

Notation a := (Id 0).
Notation f := (Id 1).
Notation g := (Id 2).
Notation l := (Id 3).
Notation A := (TBase (Id 4)).
Notation B := (TBase (Id 5)).
Notation k := (Id 6).
Notation i1 := (Id 7).
Notation i2 := (Id 8).

(** [{ i1:A }] *)

Example er1 : exists (t:ty), t = TRcd [(i1, A)].
Proof. eauto. Qed.

(** [{ i1:A->B, i2:A }] *)
Example er2 : exists (t:ty), t = 
  TRcd [(i1, (TArrow A B)); (i2, A)].
Proof. eauto. Qed.


(* ###################################################################### *)
(** ** Custom recursion principles. *)

(** *** Recursion on types, [ty_nested_rect]

    The coq-generated recursion function has the following type:
<< 
  ty_rect : 
    forall P : ty -> Type,
      (forall i : id, P (TBase i)) ->
      (forall t : ty, P t -> forall t0 : ty, P t0 -> P (TArrow t t0)) ->
      (forall r : alist ty, P (TRcd r)) ->
    forall t : ty, P t
>>

    The following custom recursion function replaces the last case 
    (a proof of [P (TRcd r)] given only that [r : aliast ty])
    with four:
      - an additional proposition function [Q] over [alist ty] (at the top),
      - a proof that for record body type, [Trb], [Q Trb] implies [P (TRcd Trb)],
      - a proof of [Q nil] and
      - a proof that [P T] and [Q Trb] implies [Q (cons x T Trb))]

    The definition may be a little hard to follow, as it is using the 
    coq-generated [ty_rect] and [alist_rect].
*)

Definition ty_nested_rect
  (P: ty -> Type) 
  (Q: alist ty -> Type)
    (fTBase : forall x : id, P (TBase x))
    (fTArrow : forall T1 : ty, P T1 -> forall T2 : ty, P T2 -> P (TArrow T1 T2))
    (fTRcd' : forall Trb : alist ty, Q Trb -> P (TRcd Trb))
      (fTRcd_nil' : Q nil)
      (fTRcd_cons' : forall (x : id) (T : ty) (Trb : alist ty), 
                       P T -> Q Trb -> Q ((x, T) :: Trb))
  : forall T : ty, P T
  := fix F (T : ty) : P T :=
    let fTRcd_cons b Trb := match b with (x,T) => fTRcd_cons' x T Trb (F T) end
    in let fTRcd Trb := fTRcd' Trb (list_rect Q fTRcd_nil' fTRcd_cons Trb)
    in ty_rect P fTBase fTArrow fTRcd T.

Definition ty_nested_rect'
  (P: ty -> Type) 
  (Q: alist ty -> Type)
    (fTBase : forall x : id, P (TBase x))
    (fTArrow : forall T1 : ty, P T1 -> forall T2 : ty, P T2 -> P (TArrow T1 T2))
    (fTRcd' : forall Trb : alist ty, Q Trb -> P (TRcd Trb))
      (fTRcd_nil' : Q nil)
      (fTRcd_cons' : forall (x : id) (T : ty) (Trb : alist ty), 
                       P T -> Q Trb -> Q ((x, T) :: Trb))
  : forall T : ty, P T
  := fix F (T : ty) : P T :=
     let fix G (Trb : alist ty) : Q Trb :=
         match Trb with
           | nil => fTRcd_nil'
           | (x,T) :: Trb' => fTRcd_cons' x T Trb' (F T) (G Trb')
         end
     in match T with
       | TBase x => fTBase x
       | TArrow T1 T2 => fTArrow T1 (F T1) T2 (F T2)
       | TRcd Trb => fTRcd' Trb (G Trb)
     end.


(** *** Recursion on terms, [tm_nested_rect]

    This is similar to above, except that it is dealing with terms rather than types.
*)

Definition tm_nest_rect
  (P: tm -> Type) 
  (Q: alist tm -> Type)
    (fvar : forall x : id, P (tvar x))
    (fapp : forall t1 : tm, P t1 -> forall t2 : tm, P t2 -> P (tapp t1 t2))
    (fabs : forall (x : id) (T : ty) (t : tm), P t -> P (tabs x T t))
    (fproj : forall t : tm, P t -> forall x : id, P (tproj t x))
    (frcd' : forall rb : alist tm, Q rb -> P (trcd rb))
      (frcd_nil' : Q nil)
      (frcd_cons' : forall (x : id) (t : tm) (rb : alist tm), 
                      P t -> Q rb -> Q ((x, t) :: rb))
  : forall t : tm, P t
  := fix F (t : tm) : P t := 
    let frcd_cons bxt rb := match bxt with (x,t) => frcd_cons' x t rb (F t) end
    in let frcd rb := frcd' rb (list_rect Q frcd_nil' frcd_cons rb)
    in tm_rect P fvar fapp fabs fproj frcd t.

Tactic Notation "t_both_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" | Case_aux c "tabs"
  | Case_aux c "tproj" | Case_aux c "trcd" 
  | Case_aux c "trnil" | Case_aux c "trcons"  ].



(* ###################################################################### *)
(** ** Reduction *)
(** *** Substitution *)

(**  Coq complains when subst is defined with [Fixpoint ... with] 
     as it cannot figure out that the term is not increasing in the 
     [with] clause.  [subst] can be defined with a nested fixpoint, as follows: 
*)

Fixpoint subst (x:id) (s:tm) (t:tm) {struct t} : tm :=
  let rsubst := (fix rsubst  (a: alist tm) : alist tm := 
    match a with
      | nil => nil 
      | (i, t) :: r' => (i, (subst x s t)) :: (rsubst r')
    end)
  in
  match t with
    | tvar y => if eq_id_dec x y then s else t
    | tabs y T t1 =>  tabs y T (if eq_id_dec x y then t1 else (subst x s t1))
    | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
    | tproj t1 i => tproj (subst x s t1) i
    | trcd r => trcd (rsubst r)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(**  In order to make the nested fixpoint visible, it is defined again as
     [subst_rcd] and a lemma is given that supports rewriting the nested
     fixpoint to it. *)

Fixpoint subst_rcd (x:id) (s:tm) (a: alist tm) : alist tm := 
  match a with
    | nil => nil 
    | (i, t) :: rb' => (i, subst x s t) :: (subst_rcd x s rb')
  end.

Notation "'[' x ':=' s ']*' r" := (subst_rcd x s r) (at level 20).


Lemma subst_rcd_eqv :
  forall x s a,
    [x := s]* a =
    ((fix rsubst (a0 : alist tm) : alist tm :=
         match a0 with
         | nil => nil
         | (i, t) :: r' => (i, [x := s]t) :: (rsubst r')
         end) a).
Proof.
  intros. induction a.
    reflexivity.
    simpl. rewrite <- IHa. reflexivity.
Qed.


(**   Here is substitution defined using the custom recursion defined above.
      However, I don't know how to use the match syntax with a custom 
      recursion principle, so it's not easy to read.  Further, it simplifies 
      into a mess that I can't fold back up, so we're not using this. *)

Definition subst_ugly (x:id) (s:tm) :tm -> tm := 
  tm_nest_rect (fun _ => tm) (fun _ => alist tm)
    (fun y => if eq_id_dec x y then s else (tvar y))                  (* tvar y *)
    (fun t1 mt1 t2 mt2 => tapp mt1 mt2)                               (* tapp t1 t2 *)
    (fun y T t1 mt1 =>  tabs y T (if eq_id_dec x y then t1 else mt1)) (* tabs y T t1 *)
    (fun t1 mt1 i => tproj mt1 i)                                     (* tproj t1 i *)
    (fun r mr => trcd mr)                                             (* trcd r *)
      (nil)                                                           (* r=nil *)
      (fun i t r mt mr => (i, mt) :: mr).                             (* r=cons i t r *)


(*
Definition tm_rect_nest (P: tm -> Type) (Q: alist tm -> Type)
  (fvar : forall i : id, P (tvar i))
  (fapp : forall t : tm,
        P t -> forall t0 : tm, P t0 -> P (tapp t t0))
  (fabs : forall (i : id) (t : ty) (t0 : tm),
        P t0 -> P (tabs i t t0))
  (fproj : forall t : tm, P t -> forall i : id, P (tproj t i))
  (frcd : forall a : alist tm, Q a -> P (trcd a))
  (frcd_nil : Q nil)
  (frcd_cons : forall (i : id) (t : tm) (a : alist tm), P t -> Q a -> Q (cons i t a))
 := fix F (t : tm) : P t := 
  match t as t' return (P t') with
    | tvar i => fvar i
    | tapp t0 t1 => fapp t0 (F t0) t1 (F t1)
    | tabs i t0 t1 => fabs i t0 t1 (F t1)
    | tproj t0 i => fproj t0 (F t0) i
    | trcd r => let frcd_cons' := (fun i y r' => frcd_cons i y r' (F y) )
      in frcd r (alist_rect tm Q frcd_nil frcd_cons' r)
  end.
 *)


Definition substf_ok (sfunc:  id -> tm -> tm -> tm) :=
  sfunc a (tvar f) (tvar a) = tvar f
    /\ sfunc a (tvar f) (tvar g) = tvar g
    /\ sfunc g (tvar f) (tvar a) = tvar a
    /\ sfunc a (tvar g) (tproj (tvar a) a) = tproj (tvar g) a
    /\ sfunc a (tvar g) (tapp (tvar f) (tvar a)) = tapp (tvar f) (tvar g)
    /\ sfunc a  (tapp (tvar f) (tvar a)) (tproj (tvar a) a)
        =  tproj  (tapp (tvar f) (tvar a)) a.

Example subst_ok :substf_ok subst.
Proof. unfold substf_ok. repeat split. Qed.

(* Some other stuff: *)

Fixpoint alist_all {T : Type} (P : T-> Prop) (a: alist T) : Prop :=
  match a with
    | nil => True
    | (i, t) :: r => P t /\ alist_all P r
  end.

Definition tm_rect_nest_map
  (fvar : id -> tm)
  (fapp : tm -> tm -> tm -> tm -> tm)
  (fabs : id -> ty ->  tm -> tm -> tm)
  (fproj : tm -> tm -> id -> tm)
 := tm_nest_rect
      (fun _ => tm)  (fun _ => alist tm) fvar fapp fabs fproj
      (fun r mr => trcd mr) nil (fun i t r mt mr => (i, mt) :: mr).


Definition subst'' (x:id) (s:tm) :tm -> tm := 
  tm_rect_nest_map
    (fun y => if eq_id_dec x y then s else (tvar y))
    (fun  t1 mt1 t2 mt2 => tapp mt1 mt2)
    (fun y T t1 mt1 =>  tabs y T (if eq_id_dec x y then t1 else mt1))
    (fun  t1 mt1 i => tproj mt1 i).

Example subst''_ok :substf_ok subst''.
Proof. unfold substf_ok. repeat split. Qed.


Definition tm_id (t : tm) : tm := 
  tm_nest_rect (fun _ => tm) (fun _ => alist tm)
    (fun y => tvar y)
    (fun  t1 mt1 t2 mt2 => tapp mt1 mt2)
    (fun y T t1 mt1 =>  tabs y T t1)
    (fun  t1 mt1 i => tproj mt1 i)
    (fun r mr => trcd mr)
    (nil)
    (fun i t r mt mr => (i, mt) :: mr)
    t.

Example ex_id1 : (tm_id (tapp (tvar f) (tvar a)))
    =  (tapp (tvar f) (tvar a)).
Proof. reflexivity. Qed.


(* ###################################################################### *)



(** *** Values *)

(** Next we define the values of our language.  A record is a value if
    all of its fields are. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tabs x T11 t12)
  | v_rcd : forall r, value_rcd r -> value (trcd r)

with value_rcd : (alist tm) -> Prop :=
  | vr_nil : value_rcd nil
  | vr_cons : forall x v1 vr,
      value v1 ->
      value_rcd vr ->
      value_rcd (aextend x v1 vr).

Hint Constructors value value_rcd.


(** *** Reduction rules:
<<
                                 ti ==> ti'                            (ST_Rcd)
    --------------------------------------------------------------------  
    {i1=v1, ..., im=vm, in=tn, ...} ==> {i1=v1, ..., im=vm, in=tn', ...}

                                 t1 ==> t1'
                               --------------                        (ST_Proj1)
                               t1.i ==> t1'.i

                          -------------------------                (ST_ProjRcd)
                          {..., i=vi, ...}.i ==> vi
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
        alookup x r = Some vx ->
        (tproj (trcd r) x) ==> vx
  | ST_Rcd : forall rb rb',
        rb *==> rb' ->
        (trcd rb) ==> (trcd rb')

with step_rcd : (alist tm) -> (alist tm) -> Prop := 
  | STR_Head : forall x t t' rb,
        t ==> t' ->
        (aextend x t rb) *==> (aextend x t' rb)
  | STR_Tail : forall x v rb rb',
        value v ->
        rb *==> rb' ->
        (aextend x v rb) *==> (aextend x v rb')

where "t1 '==>' t2" := (step t1 t2)
and "rb1 '*==>' rb2" := (step_rcd rb1 rb2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
  | Case_aux c "ST_Proj1" | Case_aux c "ST_ProjRcd" | Case_aux c "ST_Rcd" ].

Tactic Notation "step_rcd_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "STR_Head" | Case_aux c "STR_Tail" ].

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step step_rcd.
 

(* ###################################################################### *)
(** ** Typing:
<<
                                 ti ==> ti'                            (ST_Rcd)
    --------------------------------------------------------------------  
    {i1=v1, ..., im=vm, in=tn, ...} ==> {i1=v1, ..., im=vm, in=tn', ...}

                                 t1 ==> t1'
                               --------------                        (ST_Proj1)
                               t1.i ==> t1'.i

                          -------------------------                (ST_ProjRcd)
                          {..., i=vi, ...}.i ==> vi
   Typing:
               Gamma |- t1 : T1     ...     Gamma |- tn : Tn
             --------------------------------------------------         (T_Rcd)
             Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn}

                       Gamma |- t : {..., i:Ti, ...}
                       -----------------------------                   (T_Proj)
                             Gamma |- t.i : Ti
>> 
*)


Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
Reserved Notation "Gamma '|-' r '*\in' Tr" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- (tvar x) \in T
  | T_Abs : forall Gamma x T1 T2 tb,
      (extend Gamma x T1) |- tb \in T2 -> 
      Gamma |- (tabs x T1 tb) \in (TArrow T1 T2)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (TArrow T1 T2) -> 
      Gamma |- t2 \in T1 -> 
      Gamma |- (tapp t1 t2) \in T2
  (* records: *)
  | T_Proj : forall Gamma x t Tx Tr,
      Gamma |- t \in (TRcd Tr) ->
      alookup x Tr = Some Tx ->
      Gamma |- (tproj t x) \in Tx
  | T_Rcd : forall Gamma tr Tr,
      Gamma |- tr *\in Tr ->
      Gamma |- (trcd tr) \in (TRcd Tr)

with rcd_has_type : context -> (alist tm) -> (alist ty) -> Prop :=
  | TR_Nil : forall Gamma,
      Gamma |- nil *\in nil
  | TR_Cons : forall Gamma x t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr *\in Tr ->
      Gamma |- (aextend x t tr) *\in (aextend x T Tr)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T)
and   "Gamma '|-' r '*\in' Tr" := (rcd_has_type Gamma r Tr).

(* Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- (tvar x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (extend Gamma x T11) |- t12 \in T12 -> 
      Gamma |- (tabs x T11 t12) \in (TArrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (TArrow T1 T2) -> 
      Gamma |- t2 \in T1 -> 
      Gamma |- (tapp t1 t2) \in T2
  (* records: *)
  | T_Proj : forall Gamma i t Ti Tr,
      Gamma |- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |- (tproj t i) \in Ti
  | T_RNil : forall Gamma,
      Gamma |- trnil \in TRNil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- (trcons i t tr) \in (TRCons i T Tr)
 *)
Hint Constructors has_type rcd_has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Proj" | Case_aux c "T_Rcd" ].

Tactic Notation "rcd_has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TR_Nil" | Case_aux c "TR_Cons" ].

Scheme has_type_ind_both := Minimality for has_type Sort Prop
with rcd_has_type_ind_both := Minimality for rcd_has_type Sort Prop.

Tactic Notation "has_type_both_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Proj" | Case_aux c "T_Rcd" 
  | Case_aux c "TR_Nil" | Case_aux c "TR_Cons" ].



(* ###################################################################### *)
(** ** Examples *)

(** **** Exercise: 2 stars (examples)  *)
(** Finish the proofs. *)

(** Feel free to use Coq's automation features in this proof.
    However, if you are not confident about how the type system works,
    you may want to carry out the proof first using the basic
    features ([apply] instead of [eapply], in particular) and then
    perhaps compress it using automation. *)

Lemma typing_example_2 : 
  empty |- 
    (tapp (tabs a (TRcd [(i1, (TArrow A A)); (i2, (TArrow B B))])
              (tproj (tvar a) i2))
            (trcd [(i1, (tabs a A (tvar a))); (i2, (tabs a B (tvar a)))]) )
    \in (TArrow B B).
Proof. eauto 20 using extend_eq, eq_id. 
       (* FIX EAUTO USAGE ABOVE *)
  eapply T_App.
    eapply T_Abs. eapply T_Proj.
      apply T_Var. unfold extend. apply eq_id.
      reflexivity. 
    apply T_Rcd. apply TR_Cons.
      apply T_Abs. apply T_Var. apply extend_eq.
      apply TR_Cons.
        apply T_Abs. apply T_Var. apply extend_eq.
        apply TR_Nil.
Qed.

(** Before starting to prove this fact (or the one above!), make sure
    you understand what it is saying. *)

Example typing_nonexample : 
  ~ exists T,
      (extend empty a (TRcd (cons (i2, (TArrow A A)) nil)))  |-
               (trcd (cons (i1, (tabs a B (tvar a))) nil)) \in
               T.
  (* no T | a : { i2 : A->A } |- { i1 = λ a:B . a } : T *)
Proof.
  (* FILL IN HERE *) Admitted.

Example typing_nonexample_2 : forall y,
  ~ exists T,
    (extend empty y A) |-
           (tapp (tabs a (TRcd (cons (i1, A) nil))
                     (tproj (tvar a) i1))
                   (trcd (cons (i1, (tvar y)) (cons (i2, (tvar y)) nil))) ) \in
           T.
  (* forall y, ~ exists T, y : A |- (λ a : { i1 : A} . a.i1) { i1 = y; i2 = y } : T *)
Proof.
  (* FILL IN HERE *) Admitted.

(* ###################################################################### *)
(** ** Properties of Typing *)


(* ###################################################################### *)
(** *** Field Lookup *)

(* OLD: Delete or modify:
 Lemma: If [empty |- v : T] and [Tlookup i T] returns [Some Ti],
     then [tlookup i v] returns [Some ti] for some term [ti] such
     that [empty |- ti \in Ti].

    Proof: By induction on the typing derivation [Htyp].  Since
      [Tlookup i T = Some Ti], [T] must be a record type, this and
      the fact that [v] is a value eliminate most cases by inspection,
      leaving only the [T_RCons] case.

      If the last step in the typing derivation is by [T_RCons], then
      [t = trcons i0 t tr] and [T = TRCons i0 T Tr] for some [i0],
      [t], [tr], [T] and [Tr].

      This leaves two possiblities to consider - either [i0 = i] or
      not.

      - If [i = i0], then since [Tlookup i (TRCons i0 T Tr) = Some
        Ti] we have [T = Ti].  It follows that [t] itself satisfies
        the theorem.

      - On the other hand, suppose [i <> i0].  Then 
        Tlookup i T = Tlookup i Tr
        and 
        tlookup i t = tlookup i tr,
        so the result follows from the induction hypothesis. [] *)



Lemma rcd_field_alookup : 
  forall Gamma rb Trb x Tx,
    value_rcd rb ->
    Gamma |- rb *\in Trb ->
    alookup x Trb = Some Tx ->
    exists vx, alookup x rb = Some vx /\ Gamma |- vx \in Tx.
Proof.
  intros rb Gamma Tr x Tx Hv Ht Hl.
  induction Ht as [| G y vy Ty rb' Trb' Hty Ht]. 
  (* induction 2 as [| G y vy Ty rb' Trb' Hty Ht]; intro Hl. *)
  Case "nil". inversion Hl.
  Case "cons".
    inverts Hv. 
    destruct (eq_id_dec y x).
      SCase "x=y". subst. 
        rewrite (alookup_aextend_eq _ _ Ty Trb' ) in Hl. inverts Hl.
        exists vy. split.
          apply alookup_cons_eq.
          apply Hty.
      SCase "y<>x".
        rewrite (alookup_aextend_neq _ _ _ Ty _ n) in Hl. 
        destruct (IHHt H3 Hl) as [vx [Hlx HTx]]; clear IHHt.
        exists vx. split.
          rewrite (alookup_aextend_neq _ _ _ _ _ n). apply Hlx.
          apply HTx.
Qed.

(* An attempt at moving Q down to where it comes up: 

Definition has_type_ind_both' (P : context -> tm -> ty -> Prop)  
      (fvar : forall (Gamma : id -> option ty) (x : id) (T : ty),
        Gamma x = Some T -> P Gamma (tvar x) T)
      (fabs : forall (Gamma : partial_map ty) (x : id) (T1 T2 : ty) (tb : tm),
        extend Gamma x T1 |- tb \in T2 ->
        P (extend Gamma x T1) tb T2 -> P Gamma (tabs x T1 tb) (TArrow T1 T2))
      (fapp : forall (T1 T2 : ty) (Gamma : context) (t1 t2 : tm),
        Gamma |- t1 \in TArrow T1 T2 ->
        P Gamma t1 (TArrow T1 T2) ->
        Gamma |- t2 \in T1 -> P Gamma t2 T1 -> P Gamma (tapp t1 t2) T2)
      (fproj : forall (Gamma : context) (x : id) (t : tm) (Tx : ty) (Tr : alist ty),
        Gamma |- t \in TRcd Tr ->
        P Gamma t (TRcd Tr) -> alookup x Tr = Some Tx -> P Gamma (tproj t x) Tx)
      (frcd' : forall (Gamma : context) (tr : alist tm) (Tr : alist ty),
        rcd_has_type Gamma tr Tr ->
          (forall (Q : context -> alist tm -> alist ty -> Prop), 
            (forall (Gamma : context) (tr : alist tm) (Tr : alist ty),
              rcd_has_type Gamma tr Tr -> Q Gamma tr Tr -> P Gamma (trcd tr) (TRcd Tr)) ->
            (forall Gamma : context, Q Gamma nil nil) ->
            ((forall (Gamma : context) (x : id) (t : tm) (T : ty) (tr : alist tm) (Tr : alist ty),
              Gamma |- t \in T -> P Gamma t T ->
              rcd_has_type Gamma tr Tr -> Q Gamma tr Tr -> Q Gamma (cons x t tr) (cons x T Tr))))
          -> P Gamma (trcd tr) (TRcd Tr))
    : forall (c : context) (t : tm) (t0 : ty), c |- t \in t0 -> P c t t0.
Proof.
  refine (has_type_ind P fvar fabs fapp fproj _).
  intros G t T Hty. apply (frcd' G _ _ Hty).
  intros Q frcd fnil fcons.

refine (has_type_ind P fvar fabs fapp fproj _ G t T Hty).
   
  := 
    match RCD with ex_intro Q (conj frcd (conj frnil frcons)) => 
      has_type_ind_both P Q fvar fabs fapp fproj frcd frnil frcons
    end.
*)

(* ###################################################################### *)
(** *** Progress *)

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'. 
Proof with eauto.
  (* Theorem: Suppose empty |- t : T.  Then either
       1. t is a value, or
       2. t ==> t' for some t'.
     Proof: By induction on the given typing derivation. *)
  intros t T Ht.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  Ltac p_ind_tactic Ht := induction Ht using has_type_ind_both
    with (P0 := fun G tr Tr => 
       G = \empty -> 
       value_rcd tr \/ (exists tr', tr *==> tr')).
  has_type_both_cases (p_ind_tactic Ht) Case; intros HeqGamma; subst.
  (* was:  has_type_cases (induction Ht) Case; intros HeqGamma; subst. *)

  Case "T_Var".
    (* The final rule in the given typing derivation cannot be [T_Var],
       since it can never be the case that [empty |- x : T] (since the
       context is empty). *)
    inversion H.

  Case "T_Abs".
    (* If the [T_Abs] rule was the last used, then [t = tabs x T11 t12],
       which is a value. *)
    left...

  Case "T_App".
    (* If the last rule applied was T_App, then [t = t1 t2], and we know 
       from the form of the rule that
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       By the induction hypothesis, each of t1 and t2 either is a value 
       or can take a step. *)
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
      (* If both [t1] and [t2] are values, then we know that 
         [t1 = tabs x T11 t12], since abstractions are the only values
         that can have an arrow type.  But 
         [(tabs x T11 t12) t2 ==> [x:=t2]t12] by [ST_AppAbs]. *)
        inversion H; subst; try (solve by inversion).
        exists ([x:=t2]t12)...
      SSCase "t2 steps".
        (* If [t1] is a value and [t2 ==> t2'], then [t1 t2 ==> t1 t2'] 
           by [ST_App2]. *)
        destruct H0 as [t2' Hstp]. exists (tapp t1 t2')...
    SCase "t1 steps".
      (* Finally, If [t1 ==> t1'], then [t1 t2 ==> t1' t2] by [ST_App1]. *)
      destruct H as [t1' Hstp]. exists (tapp t1' t2)...

  Case "T_Proj".
    (* If the last rule in the given derivation is [T_Proj], then 
       [t = tproj t i] and
           [empty |- t : (TRcd Tr)]
       By the IH, [t] either is a value or takes a step. *)
    right. destruct IHHt...
    SCase "rcd is value".
      (* Starting here, this differs from SF. *)
      (* If [t] is a value, then we may use lemma
         [rcd_field_alookup] to show [alookup x tr = Some vx] for
         some [vx] which gives us [tproj i t ==> ti] by [ST_ProjRcd].  *)
      inversion Ht; subst; clear Ht; try solve by inversion...
      inversion H0; subst; clear H0.
      destruct (rcd_field_alookup _ _ _ _ Tx H2 H4 H) as [vx [Hlxr Htx]].
      exists vx. apply (ST_ProjRcd _ _ _ H2 Hlxr).
    SCase "rcd_steps".
      (* On the other hand, if [t ==> t'], then [tproj t i ==> tproj t' i]
         by [ST_Proj1]. *)
      destruct H0 as [t' Hstp]. exists (tproj t' x)...

  Case "T_Rcd".
    (* If the last rule in the given derivation is [T_Rcd], then 
       [t = (trcd tr)], [T=(Trcd Tr)] and [empty |- tr *: Tr]. 
      The combined induction rule requires that P0->P 
      which is what we establish here. *)
    destruct (IHHt eq_refl) as [Hv | [tr' Hst]]; clear IHHt.
      SCase "value_rcd tr". left. apply (v_rcd _ Hv).
      SCase "tr *==> tr". right. exists (trcd tr'). apply (ST_Rcd _ _ Hst).

  Case "TR_Nil". 
    (* If the last rule was [T_Rcd] established by [TR_Nil], it's a value. *)
    left. apply vr_nil.

  Case "TR_Cons".
    (* If the last rule was [T_Rcd] established by [TR_Cons], then 
          [tr = cons (x, t) tr],
          [Tr = cons (x, T) Tr],
          [ empty |- t : Tx] and
          [empty |- tr *: Tr].
        By the P IH, either t is a value or it steps and
        by the P0 IH, either tr is a value or it steps. *)
    destruct (IHHt eq_refl) as [Hvt | [t' Hstt']]; clear IHHt.
      SSCase "value t". 
          destruct (IHHt0 eq_refl) as [Hvtr | [tr' Hsttr']]; clear IHHt0.
        SSSCase "value_rcd tr". 
          left. apply (vr_cons _ _ _ Hvt Hvtr).
        SSSCase "tr *==> tr'". 
          right. eexists. apply (STR_Tail _ _ _ _ Hvt Hsttr').
      SSCase "t ==> t'". right. eexists. apply (STR_Head _ _ _ _ Hstt').
Qed.

(* ###################################################################### *)
(** *** Context Invariance *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (tabs y T11 t12)
  | afi_proj : forall x t i,
     appears_free_in x t ->
     appears_free_in x (tproj t i)
  | afi_rcd : forall x r,
     appears_free_in_rcd x r -> 
     appears_free_in x (trcd r)

with appears_free_in_rcd : id -> (alist tm) -> Prop :=
  | afi_rhead : forall x i ti r',
      appears_free_in x ti ->
      appears_free_in_rcd x (aextend i ti r')
  | afi_rtail : forall x i ti r',
      appears_free_in_rcd x r' ->
      appears_free_in_rcd x (aextend i ti r').

Hint Constructors appears_free_in appears_free_in_rcd.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |- t \in S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  Ltac ci_ind_tactic H := induction H using has_type_ind_both with 
    (P0 := fun Gamma r RS => 
      forall Gamma' : id -> option ty,
      (forall x : id, appears_free_in_rcd x r -> Gamma x = Gamma' x) ->
      Gamma' |- r *\in RS).
  has_type_both_cases (ci_ind_tactic H) Case; intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold extend. destruct (eq_id_dec x y)...
  Case "T_App".
    apply T_App with T1...
  Case "TR_Cons".
    apply TR_Cons...
Qed.


Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  Ltac fic_ind_tactic H x := induction H using has_type_ind_both with 
    (P0 := fun Gamma r RS => 
      appears_free_in_rcd x r ->
      Gamma |- r *\in RS ->
      exists T', Gamma x = Some T').
  has_type_both_cases (fic_ind_tactic Htyp x) Case; 
    inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold extend in Hctx. 
    rewrite neq_id in Hctx... 
Qed.


(* ###################################################################### *)
(** *** Preservation *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (extend Gamma x U) |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- ([x:=v]t) \in S.
Proof with eauto 15.
  (* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then 
     Gamma |- ([x:=v]t) S. *)
  intros Gamma x U v t S Htypt Htypv. 
  generalize dependent Gamma. generalize dependent S.
  (* Proof: By induction on the term t.  Most cases follow directly
     from the IH, with the exception of tvar, tabs, trcons.
     The former aren't automatic because we must reason about how the
     variables interact. In the case of trcons, we must do a little
     extra work to show that substituting into a term doesn't change
     whether it is a record term. *)
  Ltac spt_induction t x v U := induction t using tm_nest_rect with 
    (Q := fun r =>
      forall (RT : alist ty) (Gamma : partial_map ty),
        (extend Gamma x U) |- r *\in RT -> 
        Gamma |- (subst_rcd x v r) *\in RT).
  t_both_cases (spt_induction t x v U) Case; 
    intros S Gamma Htypt; simpl; inverts Htypt...

  Case "tvar".
    simpl. rename x0 into y.
    (* If t = y, we know that
         [empty |- v : U] and
         [Gamma,x:U |- y : S]
       and, by inversion, [extend Gamma x U y = Some S].  We want to
       show that [Gamma |- [x:=v]y : S].

       There are two cases to consider: either [x=y] or [x<>y]. *)
    destruct (eq_id_dec x y). 
    SCase "x=y".
    (* If [x = y], then we know that [U = S], and that [[x:=v]y = v].
       So what we really must show is that if [empty |- v : U] then
       [Gamma |- v : U].  We have already proven a more general version
       of this theorem, called context invariance. *)
      subst.
      unfold extend in H1. rewrite eq_id in H1. 
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
      apply T_Var... unfold extend in H1. rewrite neq_id in H1...

  Case "tabs".
    rename x0 into y. rename T into T1.
    (* If [t = tabs y T1 t0], then we know that
         [Gamma,x:U |- tabs y T11 t0 : T1->T2]
         [Gamma,x:U,y:T1 |- t0 : T2]
         [empty |- v : U]
       As our IH, we know that forall S Gamma, 
         [Gamma,x:U |- t0 : S -> Gamma |- [x:=v]t0 S].
    
       We can calculate that 
         [x:=v]t = tabs y T11 (if beq_id x y then t0 else [x:=v]t0)
       And we must show that [Gamma |- [x:=v]t : T11->T12].  We know
       we will do so using [T_Abs], so it remains to be shown that:
         [Gamma,y:T11 |- if beq_id x y then t0 else [x:=v]t0 : T12]
       We consider two cases: [x = y] and [x <> y].
    *)
    apply T_Abs...
    destruct (eq_id_dec x y).
    SCase "x=y".
    (* If [x = y], then the substitution has no effect.  Context
       invariance shows that [Gamma,y:U,y:T11] and [Gamma,y:T11] are
       equivalent.  Since the former context shows that [t0 : T12], so
       does the latter. *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold extend.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
    (* If [x <> y], then the IH and context invariance allow us to show that
         [Gamma,x:U,y:T1 |- t : T2]       =>
         [Gamma,y:T11,x:U |- t : T2]      =>
         [Gamma,y:T11 |- [x:=v]t : T2] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y z)... 
      subst. rewrite neq_id...

  Case "trcd". 
    rewrite <- (subst_rcd_eqv x v rb)... 

  Case "trcons".
    apply TR_Cons...
Qed.


Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  (* Theorem: If [empty |- t : T] and [t ==> t'], then [empty |- t' : T]. *)
  remember (@empty ty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many cases are
     contradictory ([T_Var], [T_Abs]) or follow directly from the IH
     ([T_RCons]).  We show just the interesting ones. *)
  Ltac pres_ind_tactic HT := induction HT using has_type_ind_both
    with (P0 := fun Gamma tr Tr => forall tr' : alist tm,
       Gamma = \empty -> 
       tr *==> tr' ->
       Gamma |- tr' *\in Tr).
  has_type_both_cases (pres_ind_tactic HT) Case;
    introv HeqGamma HE; subst; inverts HE... 

  Case "T_App".
    (* If the last rule used was [T_App], then [t = t1 t2], and three rules
       could have been used to show [t ==> t']: [ST_App1], [ST_App2], and 
       [ST_AppAbs]. In the first two cases, the result follows directly from 
       the IH. *)
    SCase "ST_AppAbs".
      (* For the third case, suppose 
           [t1 = tabs x T11 t12]
         and
           [t2 = v2].  We must show that [empty |- [x:=v2]t12 : T2]. 
         We know by assumption that
             [empty |- tabs x T11 t12 : T1->T2]
         and by inversion
             [x:T1 |- t12 : T2]
         We have already proven that substitution_preserves_typing and 
             [empty |- v2 : T1]
         by assumption, so we are done. *)
      apply substitution_preserves_typing with T1...
      inversion HT1...

  Case "T_Proj".
  (* If the last rule was [T_Proj], then [t = tproj t1 i].  Two rules
     could have caused [t ==> t']: [T_Proj1] and [T_ProjRcd].  The typing
     of [t'] follows from the IH in the former case, so we only
     consider [T_ProjRcd].

     Here we have that [t] is a record value.  Since rule T_Proj was
     used, we know [empty |- t \in Tr] and [Talookup i Tr = Some
     Ti] for some [i] and [Tr].  We may therefore apply lemma
     [alookup_field_in_value] to find the record element this
     projection steps to. *)
    inverts HT.
    destruct (rcd_field_alookup _ _ _ _ _ H2 H5 H) as [vx [ Hlxr Htx]].
    rewrite H4 in Hlxr. inversion Hlxr...

Qed.
(** [] *)

End Records.

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

