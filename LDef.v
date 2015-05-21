(** * LDef: STLC with records (as lists). *)

(** This file started out as SF's Records.v but has been modified to 
    have records as lists of declarations. 
    This is in contrast to SF's approach. *)

Load Init.
Require Export SfLib.
Require Import LibTactics.

Require Export Common.
Import P3Common.

Module LDEF.

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
           | X                           type variable (not used)
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
    principle.  Similarly, record terms will be lists of definitions.
*)

(** *** "Case" tactic notations *)

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TBase" | Case_aux c "TBool" 
  | Case_aux c "TArrow" | Case_aux c "TRcd" ].

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ttrue" | Case_aux c "tfalse" 
  | Case_aux c "tvar" | Case_aux c "tapp" | Case_aux c "tabs"
  | Case_aux c "trcd" | Case_aux c "tproj"| Case_aux c "tif" ].


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

(* TBD: Try some of these attempts at making the above more generic:

Definition lookup_generic {T U : Type} 
    (extrf : T -> option U) (xs : list T) : option U := 
  match xs with 
    | nil => None
    | x :: xs' => 
      match extrf x with
        | None => lookup_generic extrf xs'
        | Some v => Some v
      end
  end.

Definition vdef_xf (x : id) (vd : def) : option tm :=
  match vd with 
    | (Vd y t) => if id_eq_dec x y then Some t else None
    | _ => None
  end.
Definition lookup_vdef x Fs := lookup_generic (vdef_xf x) Fs.

Definition unapply_vdef (vd : vdef) : option (id * tm) :=
  match vd with (Fv y t) => Some (y, t) | _ => None end.
  
Definition lookup_gen {T U : Type} (unapplyf : T -> option (id * U)) 
    (x : id) (ts : list T) : option U :=
  match ts with
    | nil => None
    | t : ts' => 
      match unapplyf t with
        | Some (y v) => 
            if id_eq_dec x y then Some v else lookup_gen unapplyf x ts'
        | None => lookup_gen unapplyf x ts'
      end
  end.
Definition lookup_vdef := lookup_gen unapply_vdef.
*)


(* ###################################################################### *)
(** ** Custom recursion principles. *)

(** *** Recursion on types, [ty_nested_rect]

    The coq-generated recursion function has the following type:
<< 
  ty_rect : 
    forall P : ty -> Type,
      (forall i : id, P (TBase i)) ->
      P TBool ->
      (forall t : ty, P t -> forall t0 : ty, P t0 -> P (TArrow t t0)) ->
      (forall r : list decl, P (TRcd r)) -> (* records *)
    forall t : ty, P t
>>

    The following custom recursion function replaces the last case 
    (a proof of [P (TRcd r)] given only that [r : list decl])
    with four:
      - an additional proposition function [Q] over [list decl] (at the top),
      - a proof that for record body type, [Trb], [Q Trb] implies [P (TRcd Trb)],
      - a proof of [Q nil] and
      - a proof that [P T] and [Q Trb] implies [Q (cons x T Trb))]

    The definition may be a little hard to follow, as it is using the 
    coq-generated [ty_rect] and [list_rect].  
    The primed version should be the same thing using match expressions.
*)

Definition ty_nested_rect
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
    let fTRcd_cons b Trb := 
      match b with (Lv x T) => fTRcd_cons' x T Trb (F T) end
    in let fTRcd Trb := fTRcd' Trb (list_rect Q fTRcd_nil' fTRcd_cons Trb)
    in ty_rect P fTBase fTBool fTArrow fTRcd T.

Definition ty_nested_rect'
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

(* An attempt to do it as a Lemma, but the lack of a good IH kills it.

Lemma ty_nested_rect'' :
  forall 
    (P: ty -> Type) 
    (Q: list decl -> Type),
    (forall x : id, P (TBase x)) ->
    (forall T1 : ty, P T1 -> forall T2 : ty, P T2 -> P (TArrow T1 T2)) ->
    (forall Trb : list decl, Q Trb -> P (TRcd Trb)) ->
      (Q nil) ->
      (forall (x : id) (T : ty) (Trb : list decl), 
           P T -> Q Trb -> Q ((x, T) :: Trb)) ->
  forall T : ty, P T.
Proof.
  intros P Q Hbase Harrow Hrcd Hnil Hcons T.
  T_cases (induction T) Case; auto.
    Case "TRcd". (* no IH *) apply Hrcd. induction a; auto.
      SCase "cons". destruct a as [x T]. apply Hcons. (* Can't prove P T *)
Abort All.
*)

(** It would be nice if one did not have to specify Q at the start, 
    but rather when it comes up in the TRcd case. *)
(*
Definition ty_nested_rect_plus
  (P: ty -> Type) 
    (fTBase : forall x : id, P (TBase x))
    (fTArrow : forall T1 : ty, P T1 -> forall T2 : ty, P T2 -> P (TArrow T1 T2))
    (fTRcd : forall Trb : list decl, 
      (exists (Q: list decl -> Type),
              (Q nil) *
              (forall (x : id) (T : ty) (Trb : list decl), 
                       P T -> Q Trb -> Q ((x, T) :: Trb)) *
              (forall Trb : list decl, (Q Trb) -> P (TRcd Trb)) ???
      ) -> P (TRcd Trb))   
  : forall T : ty, P T := admit.
  := fix F (T : ty) : P T :=
     let fix G (Trb : list decl) : Q Trb :=
         match Trb with
           | nil => fTRcd_nil'
           | (x,T) :: Trb' => fTRcd_cons' x T Trb' (F T) (G Trb')
         end
     in match T with
       | TBase x => fTBase x
       | TArrow T1 T2 => fTArrow T1 (F T1) T2 (F T2)
       | TRcd Trb => fTRcd' Trb (G Trb)
     end.
*)


(** *** Recursion on terms, [tm_nested_rect]

    This is similar to above, except that it is dealing with terms rather than types.
*)

Definition tm_nest_rect
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

Tactic Notation "t_both_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ttrue" | Case_aux c "tfalse" 
  | Case_aux c "tvar" | Case_aux c "tapp" | Case_aux c "tabs"
  | Case_aux c "trcd" | Case_aux c "trnil" | Case_aux c "trcons"
  | Case_aux c "tproj" | Case_aux c "tif" ].



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
  let rsubst := (fix rsubst  (a: list def) : list def := 
    match a with
      | nil => nil 
      | (Fv i t) :: r' => (Fv i ([x:=s] t)) :: (rsubst r')
    end)
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


(**   Here is substitution defined using the custom recursion defined above.
      However, I don't know how to use the match syntax with a custom 
      recursion principle, so it's not easy to read.  Further, it simplifies 
      into a mess that I can't fold back up, so we're not using this. *)

Definition subst_ugly (x:id) (s:tm) :tm -> tm := 
  tm_nest_rect (fun _ => tm) (fun _ => list def)
    ttrue                                               (* ttrue *)
    tfalse                                              (* tfalse *)
    (fun y => if eq_id_dec x y then s else (tvar y))    (* tvar y *)
    (fun t1 mt1 t2 mt2 => tapp mt1 mt2)                 (* tapp t1 t2 *)
    (fun y T t1 mt1 =>                                  (* tabs y T t1 *)
       tabs y T (if eq_id_dec x y then t1 else mt1))
    (fun r mr => trcd mr)                               (* trcd r *)
      (nil)                                               (* nil *)
      (fun i t r mt mr => (Fv i mt) :: mr)                (* cons i t r *)
    (fun t1 mt1 i => tproj mt1 i)                       (* tproj t1 i *)
    (fun tb mtb tt mtt te mte => tif mtb mtt mte)       (* tif tb tt te *)
    .

(*
Definition tm_rect_nest (P: tm -> Type) (Q: list def -> Type)
  (fvar : forall i : id, P (tvar i))
  (fapp : forall t : tm,
        P t -> forall t0 : tm, P t0 -> P (tapp t t0))
  (fabs : forall (i : id) (t : ty) (t0 : tm),
        P t0 -> P (tabs i t t0))
  (fproj : forall t : tm, P t -> forall i : id, P (tproj t i))
  (frcd : forall a : list def, Q a -> P (trcd a))
  (frcd_nil : Q nil)
  (frcd_cons : forall (i : id) (t : tm) (a : list def), P t -> Q a -> Q (cons i t a))
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



(* Some other stuff: *)

Fixpoint alist_all {T : Type} (P : T-> Prop) (a: alist T) : Prop :=
  match a with
    | nil => True
    | (i, t) :: r => P t /\ alist_all P r
  end.

Definition tm_rect_nest_map
  (ftrue : tm)
  (ffalse : tm)
  (fvar : id -> tm)
  (fapp : tm -> tm -> tm -> tm -> tm)
  (fabs : id -> ty ->  tm -> tm -> tm)
  (fproj : tm -> tm -> id -> tm)
  (fif : tm -> tm -> tm -> tm -> tm -> tm -> tm)
 := tm_nest_rect
      (fun _ => tm)  (fun _ => list def) ftrue ffalse fvar fapp fabs
      (fun r mr => trcd mr) nil (fun i t r mt mr => (Fv i mt) :: mr) fproj fif.


Definition subst'' (x:id) (s:tm) : tm -> tm := 
  tm_rect_nest_map
    ttrue
    tfalse
    (fun y => if eq_id_dec x y then s else (tvar y))
    (fun t1 mt1 t2 mt2 => tapp mt1 mt2)
    (fun y T t1 mt1 =>  tabs y T (if eq_id_dec x y then t1 else mt1))
    (fun t1 mt1 i => tproj mt1 i)
    (fun tb mtb tt mtt te mte => tif mtb mtt mte).

(*
Example subst''_ok :substf_ok subst''.
Proof. unfold substf_ok. repeat split. Qed.
*)

Definition tm_id : tm -> tm := 
  tm_nest_rect (fun _ => tm) (fun _ => list def)
    ttrue 
    tfalse
    (fun y => tvar y)
    (fun t1 mt1 t2 mt2 => tapp t1 t2)
    (fun y T t1 mt1 =>  tabs y T t1)
    (fun r mr => trcd r)
    (nil)
    (fun i t r mt mr => (Fv i t) :: r)
    (fun t1 mt1 i => tproj t1 i)
    (fun tb mtb tt mtt te mte => tif tb tt te).
(*
Example ex_id1 : (tm_id (tapp (tvar f) (tvar a)))
    =  (tapp (tvar f) (tvar a)).
Proof. reflexivity. Qed.
*)

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

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" := 
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
  | T_App : forall T1 T2 Gamma t1 t2,
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
  | T_If : forall t1 t2 t3 T Gamma,
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

(** *** Custom induction principle for typing *)

Scheme has_type_ind_both := Minimality for has_type Sort Prop
with rcd_has_type_ind_both := Minimality for rcd_has_type Sort Prop.

Tactic Notation "has_type_both_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Rcd" | Case_aux c "T_Proj" 
  | Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "TR_Nil" | Case_aux c "TR_Cons" ].



End LDEF.
