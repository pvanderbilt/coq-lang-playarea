(** * RecordsExt: Adding Records to STLC *)

(** This file started out as SF's Records.v but has been modified to 
    have records as lists of declarations. 
    This is in contrast to SF's approach. *)

Load Init.
Require Export SfLib.
Require Import LibTactics.

Require Export Common LDef.
Import P3Common.
(* Import LDEF. *)

Module Records.

(* ###################################################################### *)

(**  ** Syntax *)

(**  *** Types [ty]
<<
           | X                           base type X
           | Bool                        boolean type
           | T1 -> T2                    function type
           | {i1:T1, ..., in:Tn}         record type
>> 
 *)

Inductive ty : Type :=
  | TBase     : id -> ty
  | TBool     : ty
  | TArrow    : ty -> ty -> ty
  | TRcd      : (list decl) -> ty
with decl : Type :=
  | Lv        : id -> ty -> decl.

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TBase" | Case_aux c "TBool" 
  | Case_aux c "TArrow" | Case_aux c "TRcd" ].

(** In SF there is a note about how something like this doesn't 
    give a useful induction principle we want.  So they have
    the following:
<<
      | TRNil : ty
      | TRCons : id -> ty -> ty -> ty
>>
    Since this allows TRCons to be applied to non-record components,
    they have a way to tell whether types are well-formed.  The same
    thing applies to terms.

    Instead, we use lists of declarations and fix the induction 
    principle.  Similarly, record terms will be lists of definitions.
*)

(** *** Terms [tm]
<<
       t ::=                          Terms:
           | true, false                 boolean values
           | x                           variable
           | t1 t2                       application
           | \x:T1.t2                    abstraction
           | {i1=t1, ..., in=tn}         record 
           | t.i                         projection
           | if tb then te else tf       conditional
>> 
*)

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

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ttrue" | Case_aux c "tfalse" 
  | Case_aux c "tvar" | Case_aux c "tapp" | Case_aux c "tabs"
  | Case_aux c "trcd" | Case_aux c "tproj"| Case_aux c "tif" ].


(* *** Functions for dealing with def and decl- lists *)

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
      (forall r : list decl, P (TRcd r)) ->
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

(**  Coq complains when subst is defined with [Fixpoint ... with] 
     as it cannot figure out that the term is not increasing in the 
     [with] clause.  [subst] can be defined with a nested fixpoint, as follows: 
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
    ttrue                                                             (* ttrue *)
    tfalse                                                            (* tfalse *)
    (fun y => if eq_id_dec x y then s else (tvar y))                  (* tvar y *)
    (fun t1 mt1 t2 mt2 => tapp mt1 mt2)                               (* tapp t1 t2 *)
    (fun y T t1 mt1 =>  tabs y T (if eq_id_dec x y then t1 else mt1)) (* tabs y T t1 *)
    (fun r mr => trcd mr)                                             (* trcd r *)
      (nil)                                                           (* r=nil *)
      (fun i t r mt mr => (Fv i mt) :: mr)                            (* r=cons i t r *)
    (fun t1 mt1 i => tproj mt1 i)                                     (* tproj t1 i *)
    (fun tb mtb tt mtt te mte => tif mtb mtt mte)                     (* tif tb tt te *)
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
           | true | false
           | lambda x : T . t
           | {i1=v1, ..., in=vn}         record value

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

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step step_rcd.
 

(* ###################################################################### *)
(** ** Typing *)

(** ** Contexts *)

Definition context := list decl.
Definition empty := nil (A:=decl).
Definition extend (Gamma : context) (x : id) (T : ty) := (Lv x T) :: Gamma.

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
      (extend Gamma x T1) |- tb \in T2 -> 
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

Scheme has_type_ind_both := Minimality for has_type Sort Prop
with rcd_has_type_ind_both := Minimality for rcd_has_type Sort Prop.

Tactic Notation "has_type_both_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Rcd" | Case_aux c "T_Proj" 
  | Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "TR_Nil" | Case_aux c "TR_Cons" ].



(* ###################################################################### *)
(** ** Properties of Typing *)


(* ###################################################################### *)
(** *** Record Field Lookup *)

Lemma rcd_field_lookup : 
  forall rb Trb x Tx,
    empty |- rb *\in Trb ->
    lookup_vdecl x Trb = Some Tx ->
    exists vx, lookup_vdef x rb = Some vx /\ empty |- vx \in Tx.
Proof.
  intros rb Tr x Tx Ht Hl.
  induction Ht as [| G y vy Ty rb' Trb' Hty Ht]. 
  Case "nil". inversion Hl.
  Case "cons".
    destruct (eq_id_dec y x).
      SCase "x=y". subst. 
        rewrite (lookup_add_vdecl_eq x Ty Trb') in Hl. inverts Hl.
        exists vy. split.
          apply lookup_add_vdef_eq.
          apply Hty.
      SCase "y<>x".
        rewrite (lookup_add_vdecl_neq _ _ Ty Trb' n) in Hl. 
        destruct (IHHt Hl) as [vx [Hlx HTx]]; clear IHHt.
        exists vx. split.
          rewrite (lookup_add_vdef_neq _ _ _ _ n). apply Hlx.
          apply HTx.
Qed.

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
  remember (empty) as Gamma.
  generalize dependent HeqGamma.
  Ltac p_ind_tactic Ht := induction Ht using has_type_ind_both
    with (P0 := fun G tr Tr => 
       G = empty -> 
       value_rcd tr \/ (exists tr', tr *==> tr')).
  has_type_both_cases (p_ind_tactic Ht) Case; intros HeqGamma; subst; 
    try (left; auto; fail).
     (* the [try  (left; auto; fail)] tactic handles the value cases 
      (T_Abs, T_True, T_False, TR_Nil) *)

  Case "T_Var".
    (* The final rule in the given typing derivation cannot be [T_Var],
       since it can never be the case that [empty |- x : T] (since the
       context is empty). *)
    inversion H.

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

  Case "T_Rcd".
    (* If the last rule in the given derivation is [T_Rcd], then 
       [t = (trcd tr)], [T=(Trcd Tr)] and [empty |- tr *: Tr]. 
      The combined induction rule requires that P0->P 
      which is what we establish here. *)
    destruct (IHHt eq_refl) as [Hv | [tr' Hst]]; clear IHHt.
      SCase "value_rcd tr". left. apply (v_rcd _ Hv).
      SCase "tr *==> tr". right. exists (trcd tr'). apply (ST_Rcd _ _ Hst).

  Case "T_Proj".
    (* If the last rule in the given derivation is [T_Proj], then 
       [t = tproj t i] and
           [empty |- t : (TRcd Tr)]
       By the IH, [t] either is a value or takes a step. *)
    right. destruct IHHt...
    SCase "rcd is value".
      (* Starting here, this differs from SF. *)
      (* If [t] is a value and [t : TRcd Tr], we can invert the
          latter to get that [t = (trcd tr)] with [tr *: Tr] *)
      inverts Ht; try solve by inversion...
      (* Lemma [rcd_field_lookup] shows that [lookup_vdef x tr = Some vx] for
         some [vx].*)
      destruct (rcd_field_lookup _ _ _ Tx H4 H) as [vx [Hlxr Htx]].
      (* So [tproj x t ==> vx] by [ST_ProjRcd] with the inversion of H0
         to get that [vx] is a value.  *)
      exists vx. inverts H0 as H0. apply (ST_ProjRcd _ _ _ H0 Hlxr).
    SCase "rcd_steps".
      (* On the other hand, if [t ==> t'], then [tproj t i ==> tproj t' i]
         by [ST_Proj1]. *)
      destruct H0 as [t' Hstp]. exists (tproj t' x)...

  Case "T_If".
    right. destruct IHHt1...

    SCase "t1 is a value".
      inverts H; try inversion Ht1; eauto.
      (* destruct (canonical_forms_bool t1); subst; eauto.*)

    SCase "t1 also steps".
      inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...

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
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif t1 t2 t3)

with appears_free_in_rcd : id -> (list def) -> Prop :=
  | afi_rhead : forall x i ti r',
      appears_free_in x ti ->
      appears_free_in_rcd x (add_vdef i ti r')
  | afi_rtail : forall x i ti r',
      appears_free_in_rcd x r' ->
      appears_free_in_rcd x (add_vdef i ti r').

Hint Constructors appears_free_in appears_free_in_rcd.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> 
                lookup_vdecl x Gamma = lookup_vdecl x Gamma') ->
     Gamma' |- t \in S.
Proof with eauto 15.
  intros. generalize dependent Gamma'.
  Ltac ci_ind_tactic H := induction H using has_type_ind_both with 
    (P0 := fun Gamma r RS => 
      forall Gamma' : context,
      (forall x : id, appears_free_in_rcd x r -> 
                      lookup_vdecl x Gamma = lookup_vdecl x Gamma') ->
      Gamma' |- r *\in RS).
  has_type_both_cases (ci_ind_tactic H) Case; intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold extend, lookup_vdecl. destruct (eq_id_dec x y)...
Qed.


Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T',  lookup_vdecl x Gamma = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  Ltac fic_ind_tactic H x := induction H using has_type_ind_both with 
    (P0 := fun Gamma r RS => 
      appears_free_in_rcd x r ->
      Gamma |- r *\in RS ->
      exists T', lookup_vdecl x Gamma = Some T').
  has_type_both_cases (fic_ind_tactic Htyp x) Case; 
    inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold extend, lookup_vdecl in Hctx. 
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
      forall (RT : list decl) (Gamma : context),
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
      unfold extend, lookup_vdecl in H1. rewrite eq_id in H1. 
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
      apply T_Var... unfold extend, lookup_vdecl in H1. rewrite neq_id in H1...

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
      intros x Hafi. unfold extend, lookup_vdecl.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
    (* If [x <> y], then the IH and context invariance allow us to show that
         [Gamma,x:U,y:T1 |- t : T2]       =>
         [Gamma,y:T11,x:U |- t : T2]      =>
         [Gamma,y:T11 |- [x:=v]t : T2] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend, lookup_vdecl.
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
  remember (empty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many cases are
     contradictory ([T_Var], [T_Abs]) or follow directly from the IH
     ([T_RCons]).  We show just the interesting ones. *)
  Ltac pres_ind_tactic HT := induction HT using has_type_ind_both
    with (P0 := fun Gamma tr Tr => forall tr' : list def,
       Gamma = empty -> 
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
    (* If the last rule was [T_Proj], then [t = tproj t0 x] 
       where [t0 : (TRcd Tr)] and [lookup_vdecl x Tr = Some T]
       for some [t0], [x] and [Tr]. Two rules could have caused 
       [t ==> t']: [ST_Proj1] and [ST_ProjRcd].  The typing
       of [t'] follows from the IH in the former case.

       In the [ST_ProjRcd] case, [t0 = (trcd r)] for some [r]
       where [value_rcd r] and [lookup_vdef x r = Some t'].
       Inverting Ht gives [r *: Tr] and we can apply lemma
       [rcd_field_lookup] to find the record element this
       projection steps to. *)
    inverts HT.
    destruct (rcd_field_lookup _ _ _ _ H5 H) as [vx [ Hlxr Htx]].
    rewrite H4 in Hlxr. inversion Hlxr...

Qed.
(** [] *)

End Records.

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

