(** * Records: Adding Records to STLC *)

Add LoadPath "/Users/pv/Polya/Coq/pierce_software_foundations_3.2".

Require Export Stlc.

(* ###################################################################### *)
(** * Pete's version of ""Adding Records *)


(**
    Syntax:
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
   Reduction:
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
*)

(* ###################################################################### *)
(** * Formalizing Records *)

Module STLCExtendedRecords.

(* ###################################################################### *)
(** *** Syntax and Operational Semantics *)

(**  ALISTS *)

Inductive alist (T : Type) : Type :=
  | nil    : alist T
  | cons : id -> T -> alist T  -> alist T.

Arguments nil {T}.
Arguments cons {T} _ _ _.

Fixpoint lookup {X: Type} (x: id) : (alist X) -> option X :=
  fix fLookup a  := match a with
    | nil => None
    | cons y t r => if eq_id_dec x y then (Some t) else (fLookup r)
    end.

Fixpoint map {X Y: Type} (f: X -> Y) (a: alist X) : alist Y :=
  match a with
  | nil => nil
  | cons x t r => cons x (f t) (map f r)
  end.

Tactic Notation "A_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "nil" | Case_aux c "cons" ].



(**  types *)

Inductive ty : Type :=
  | TBase     : id -> ty
  | TArrow    : ty -> ty -> ty
  | TRcd      : (alist ty) -> ty.

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TBase" | Case_aux c "TArrow"
  | Case_aux c "TRcd" ].

(** Pierce: Unfortunately, we encounter here a limitation in Coq: this type
    does not automatically give us the induction principle we expect
    -- the induction hypothesis in the [TRcd] case doesn't give us
    any information about the [ty] elements of the list, making it
    useless for the proofs we want to do.  *)

(* Check ty_ind. 
   ====>
    ty_ind : 
      forall P : ty -> Prop,
        (forall i : id, P (TBase i)) ->
        (forall t : ty, P t -> forall t0 : ty, P t0 -> P (TArrow t t0)) ->
        (forall a : alist ty, P (TRcd a)) ->    (* ??? *)
        forall t : ty, P t
*)

(** It is possible to get a better induction principle out of Coq, but
    the details of how this is done are not very pretty, and it is not
    as intuitive to use as the ones Coq generates automatically for
    simple [Inductive] definitions.

    Fortunately, there is a different way of formalizing records that
    is, in some ways, even simpler and more natural: instead of using
    the existing [list] type, we can essentially include its
    constructors ("nil" and "cons") in the syntax of types. *)

(* Inductive ty : Type :=
  | TBase : id -> ty
  | TArrow : ty -> ty -> ty
  | TRNil : ty
  | TRCons : id -> ty -> ty -> ty.
 *)


(** Similarly, at the level of terms, we have constructors [trnil]
    -- the empty record -- and [trcons], which adds a single field to
    the front of a list of fields. *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  (* records *)
  | tproj : tm -> id -> tm
  | trcd: alist tm -> tm.

(*   | trnil :  tm
  | trcons : id -> tm -> tm -> tm.
 *)

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

(* Check (TRcd (cons ty i1 A (nil ty))). *)

(** [{ i1:A->B, i2:A }] *)

(* 
Check (TRcd (cons ty i1 (TArrow A B) 
           (cons ty i2 A (nil ty)))). 
 *)
(* ###################################################################### *)


(* ###################################################################### *)
(** *** Substitution *)

Fixpoint subst (x:id) (s:tm) (t:tm) {struct t} : tm :=
  let rsubst := (fix rsubst  (a: alist tm) : alist tm := 
    match a with
      | nil => nil 
      | cons i t r' => cons  i (subst x s t) (rsubst r')
    end)
  in
  match t with
    | tvar y => if eq_id_dec x y then s else t
    | tabs y T t1 =>  tabs y T (if eq_id_dec x y then t1 else (subst x s t1))
    | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
    | tproj t1 i => tproj (subst x s t1) i
    | trcd r => trcd (rsubst r)
  end.


Definition tm_rect_nest (P: tm -> Type) (Q: alist tm -> Type)
  (fvar : forall i : id, P (tvar i))
  (fapp : forall t : tm,
        P t -> forall t0 : tm, P t0 -> P (tapp t t0))
  (fabs : forall (i : id) (t : ty) (t0 : tm),
        P t0 -> P (tabs i t t0))
  (fproj : forall t : tm, P t -> forall i : id, P (tproj t i))
  (frcd' : forall a : alist tm, Q a -> P (trcd a))
  (frcd_nil' : Q nil)
  (frcd_cons' : forall (i : id) (t : tm) (a : alist tm), P t -> Q a -> Q (cons i t a))
 := fix F (t : tm) : P t := 
    let frcd_cons  i y r := frcd_cons' i y r (F y)
    in let frcd  r := frcd' r (alist_rect tm Q frcd_nil' frcd_cons r)
    in tm_rect P fvar fapp fabs fproj frcd t.

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
(*

fun F : forall (t : tm), P t => fun (a: alist tm) =>
    let frcd_cons' := (fun i y r => frcd_cons i y r (F y) )
    in frcd a (alist_rect tm Q frcd_nil frcd_cons' a).

 *)

Definition subst' (x:id) (s:tm) :tm -> tm := 
  tm_rect_nest (fun _ => tm) (fun _ => alist tm)
    (fun y => if eq_id_dec x y then s else (tvar y))
    (fun  t1 mt1 t2 mt2 => tapp mt1 mt2)
    (fun y T t1 mt1 =>  tabs y T (if eq_id_dec x y then t1 else mt1))
    (fun  t1 mt1 i => tproj mt1 i)
    (fun r mr => trcd mr)
    (nil)
    (fun i t r mt mr => cons i mt mr).

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

Example subst'_ok :substf_ok subst'.
Proof. unfold substf_ok. repeat split. Qed.

Fixpoint alist_all {T : Type} (P : T-> Prop) (a: alist T) : Prop :=
  match a with
    | nil => True
    | cons i t r => P t /\ alist_all P r
  end.

Definition tm_rect_nest_map
  (fvar : id -> tm)
  (fapp : tm -> tm -> tm -> tm -> tm)
  (fabs : id -> ty ->  tm -> tm -> tm)
  (fproj : tm -> tm -> id -> tm)
 := tm_rect_nest
      (fun _ => tm)  (fun _ => alist tm) fvar fapp fabs fproj
      (fun r mr => trcd mr) nil (fun i t r mt mr => cons i mt mr).

(* Inlined version, pointless. *)
Definition tm_rect_nest_map'
  (fvar : id -> tm)
  (fapp : tm -> tm -> tm -> tm -> tm)
  (fabs : id -> ty ->  tm -> tm -> tm)
  (fproj : tm -> tm -> id -> tm)
 := fix F (t : tm) : tm :=
    let frcd_cons i y r mr := cons i (F y) mr
    in let frcd  r := trcd (alist_rect tm  (fun _ => alist tm) nil frcd_cons r)
    in tm_rect (fun _ => tm) fvar fapp fabs fproj frcd t.


Definition subst'' (x:id) (s:tm) :tm -> tm := 
  tm_rect_nest_map
    (fun y => if eq_id_dec x y then s else (tvar y))
    (fun  t1 mt1 t2 mt2 => tapp mt1 mt2)
    (fun y T t1 mt1 =>  tabs y T (if eq_id_dec x y then t1 else mt1))
    (fun  t1 mt1 i => tproj mt1 i).

Example subst''_ok :substf_ok subst''.
Proof. unfold substf_ok. repeat split. Qed.


Definition tm_id (t : tm) : tm := 
  tm_rect_nest (fun _ => tm) (fun _ => alist tm)
    (fun y => tvar y)
    (fun  t1 mt1 t2 mt2 => tapp mt1 mt2)
    (fun y T t1 mt1 =>  tabs y T t1)
    (fun  t1 mt1 i => tproj mt1 i)
    (fun r mr => trcd mr)
    (nil)
    (fun i t r mt mr => cons i mt mr)
    t.

Example ex_id1 : (tm_id (tapp (tvar f) (tvar a)))
    =  (tapp (tvar f) (tvar a)).
Proof. reflexivity. Qed.


(*
 Inductive ty : Type :=
  | TBase     : id -> ty
  | TArrow    : ty -> ty -> ty
  | TRcd      : (alist ty) -> ty.
 *)
Definition ty_nested_rect  (P: ty -> Type) (Q: alist ty -> Type)
  (fTBase : forall i : id, P (TBase i))
  (fTArrow : forall t : ty,
        P t -> forall t0 : ty, P t0 -> P (TArrow t t0))
  (fTRcd' : forall r : alist ty, Q r -> P (TRcd r))
  (fTRcd_nil' : Q nil)
  (fTRcd_cons' : forall (i : id) (t : ty) (a : alist ty), P t -> Q a -> Q (cons i t a))
 := fix F (t : ty) : P t :=
    let fTRcd_cons  i y r :=  fTRcd_cons' i y r (F y) 
    in let fTRcd r :=  fTRcd' r (alist_rect ty Q fTRcd_nil' fTRcd_cons r)
    in ty_rect P fTBase fTArrow fTRcd t.

(* WAS
Definition ty_nested_rect  (P: ty -> Type) (Q: alist ty -> Type)
  (fTBase : forall i : id, P (TBase i))
  (fTArrow : forall t : ty,
        P t -> forall t0 : ty, P t0 -> P (TArrow t t0))
  (fTRcd : forall r : alist ty, Q r -> P (TRcd r))
  (fTRcd_nil : Q nil)
  (fTRcd_cons : forall (i : id) (t : ty) (a : alist ty), P t -> Q a -> Q (cons i t a))
 := fix F (t : ty) : P t := 
  match t as t0 return (P t0) with
    | TBase i => fTBase i
    | TArrow t0 t1 => fTArrow t0 (F t0) t1 (F t1)
    | TRcd r => let frcd_cons' := (fun i y r' => fTRcd_cons i y r' (F y) )
      in fTRcd r (alist_rect ty Q fTRcd_nil frcd_cons' r)
  end.

 *)
(* 
Definition subst' (x:id) (s:tm) : tm -> tm :=
  fix F t :=
    match t with
      | tvar y => if eq_id_dec x y then s else t
      | tabs y T t1 =>  tabs y T (if eq_id_dec x y then t1 else (F t1))
      | tapp t1 t2 => tapp (F t1) (F t2)
      | tproj t1 i => tproj (F t1) i
      | trcd nil => trcd nil
      | trcd (cons i t1 r) => let sr := (match (F (trcd r)) with trcd r' => r' end) 
          in trcd (cons i (F t1) sr)
    end.

 *)(* 
Definition subst (x:id) (s:tm) : tm -> tm :=
  fix F t :=
    match t with
      | tvar y => if eq_id_dec x y then s else t
      | tabs y T t1 =>  tabs y T (if eq_id_dec x y then t1 else (F t1))
      | tapp t1 t2 => tapp (F t1) (F t2)
      | tproj t1 i => tproj (F t1) i
      | trcd r => trcd (map (fun (x:tm) =>(F x)) r) (* (map F r) *)
    end.

 *)(* 

with rsubst (x:id) (s:tm) (a: alist tm) {struct a} : alist tm := 

 *)

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* ###################################################################### *)
(** *** Reduction *)

(** Next we define the values of our language.  A record is a value if
    all of its fields are. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tabs x T11 t12)
  | v_rcd : forall r, value_rcd r -> value (trcd r)
with value_rcd : (alist tm) -> Prop :=
  | vr_nil : value_rcd nil
  | vr_cons : forall i v1 vr,
      value v1 ->
      value_rcd vr ->
      value_rcd (cons i v1 vr).

(*Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tabs x T11 t12)
  | v_rnil : value trnil
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value (trcons i v1 vr).
*)
Hint Constructors value.

(** Utility functions for extracting one field from record type or
    term: *)

Fixpoint Tlookup (i:id) (Tr:ty) : option ty :=
  match Tr with
  | TRCons i' T Tr' => if eq_id_dec i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Fixpoint tlookup (i:id) (tr:tm) : option tm :=
  match tr with
  | trcons i' t tr' => if eq_id_dec i i' then Some t else tlookup i tr'
  | _ => None
  end.

(** The [step] function uses the term-level lookup function (for the
    projection rule), while the type-level lookup is needed for
    [has_type]. *)

Reserved Notation "t1 '==>' t2" (at level 40).

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
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
        (tproj tr i) ==> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 ==> t1' ->
        (trcons i t1 tr2) ==> (trcons i t1' tr2)
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 ==> tr2' ->
        (trcons i v1 tr2) ==> (trcons i v1 tr2')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
  | Case_aux c "ST_Proj1" | Case_aux c "ST_ProjRcd"
  | Case_aux c "ST_Rcd_Head" | Case_aux c "ST_Rcd_Tail" ].

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

(* ###################################################################### *)
(** *** Typing *)

Definition context := partial_map ty.

(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above.  The only major
    difference is the use of [well_formed_ty].  In the informal
    presentation we used a grammar that only allowed well formed
    record types, so we didn't have to add a separate check.

    We'd like to set things up so that that whenever [has_type Gamma t
    T] holds, we also have [well_formed_ty T].  That is, [has_type]
    never assigns ill-formed types to terms.  In fact, we prove this
    theorem below.

    However, we don't want to clutter the definition of [has_type]
    with unnecessary uses of [well_formed_ty].  Instead, we place
    [well_formed_ty] checks only where needed - where an inductive
    call to [has_type] won't already be checking the well-formedness
    of a type.

    For example, we check [well_formed_ty T] in the [T_Var] case,
    because there is no inductive [has_type] call that would 
    enforce this.  Similarly, in the [T_Abs] case, we require a
    proof of [well_formed_ty T11] because the inductive call to
    [has_type] only guarantees that [T12] is well-formed.

    In the rules you must write, the only necessary [well_formed_ty]
    check comes in the [tnil] case.  *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
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

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Proj" | Case_aux c "T_RNil" | Case_aux c "T_RCons" ].

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
    (tapp (tabs a (TRCons i1 (TArrow A A)
                      (TRCons i2 (TArrow B B)
                       TRNil))
              (tproj (tvar a) i2))
            (trcons i1 (tabs a A (tvar a)) 
            (trcons i2 (tabs a B (tvar a))
             trnil))) \in
    (TArrow B B).
Proof. 
  (* FILL IN HERE *) Admitted.

(** Before starting to prove this fact (or the one above!), make sure
    you understand what it is saying. *)

Example typing_nonexample : 
  ~ exists T,
      (extend empty a (TRCons i2 (TArrow A A) 
                                TRNil)) |-
               (trcons i1 (tabs a B (tvar a)) (tvar a)) \in
               T.
Proof.
  (* FILL IN HERE *) Admitted.

Example typing_nonexample_2 : forall y,
  ~ exists T,
    (extend empty y A) |-
           (tapp (tabs a (TRCons i1 A TRNil)
                     (tproj (tvar a) i1))
                   (trcons i1 (tvar y) (trcons i2 (tvar y) trnil))) \in
           T.
Proof.
  (* FILL IN HERE *) Admitted.

(* ###################################################################### *)
(** ** Properties of Typing *)

(** The proofs of progress and preservation for this system are
    essentially the same as for the pure simply typed lambda-calculus,
    but we need to add some technical lemmas involving records. *)

(* ###################################################################### *)
(** *** Well-Formedness *)

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  T_cases (induction T) Case; intros; try solve by inversion.
  Case "TRCons".
    inversion H. subst. unfold Tlookup in H0.
    destruct (eq_id_dec i i0)...
    inversion H0. subst...  Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr ==> tr' ->
  record_tm tr'.
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; auto.
Qed.

Lemma has_type__wf : forall Gamma t T,
  Gamma |- t \in T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  has_type_cases (induction Htyp) Case...
  Case "T_App".
    inversion IHHtyp1... 
  Case "T_Proj".
    eapply wf_rcd_lookup...
Qed.

(* ###################################################################### *)
(** *** Field Lookup *)

(** Lemma: If [empty |- v : T] and [Tlookup i T] returns [Some Ti],
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

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |- v \in T ->
  Tlookup i T = Some Ti ->
  exists ti, tlookup i v = Some ti /\ empty |- ti \in Ti.
Proof with eauto.
  intros v T i Ti Hval Htyp Hget.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Htyp) Case; subst; try solve by inversion...
  Case "T_RCons".
    simpl in Hget. simpl. destruct (eq_id_dec i i0).
    SCase "i is first".
      simpl. inversion Hget. subst.
      exists t...
    SCase "get tail".
      destruct IHHtyp2 as [vi [Hgeti Htypi]]...
      inversion Hval... Qed.

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
  has_type_cases (induction Ht) Case; intros HeqGamma; subst.
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
      (* If [t] is a value, then we may use lemma
         [lookup_field_in_value] to show [tlookup i t = Some ti] for
         some [ti] which gives us [tproj i t ==> ti] by [ST_ProjRcd]
         *)
      destruct (lookup_field_in_value _ _ _ _ H0 Ht H) as [ti [Hlkup _]].
      exists ti...
    SCase "rcd_steps".
      (* On the other hand, if [t ==> t'], then [tproj t i ==> tproj t' i]
         by [ST_Proj1]. *)
      destruct H0 as [t' Hstp]. exists (tproj t' i)...
  Case "T_RNil".
    (* If the last rule in the given derivation is [T_RNil], then 
       [t = trnil], which is a value. *)
    left...
  Case "T_RCons".
    (* If the last rule is [T_RCons], then [t = trcons i t tr] and
         [empty |- t : T]
         [empty |- tr : Tr]
       By the IH, each of [t] and [tr] either is a value or can take
       a step. *)
    destruct IHHt1...
    SCase "head is a value".
      destruct IHHt2; try reflexivity.
      SSCase "tail is a value".
      (* If [t] and [tr] are both values, then [trcons i t tr]
         is a value as well. *)
        left...
      SSCase "tail steps".
        (* If [t] is a value and [tr ==> tr'], then 
           [trcons i t tr ==> trcons i t tr'] by 
           [ST_Rcd_Tail]. *)
        right. destruct H2 as [tr' Hstp].
        exists (trcons i t tr')...
    SCase "head steps".      
      (* If [t ==> t'], then 
         [trcons i t tr ==> trcons i t' tr] 
         by [ST_Rcd_Head]. *)
      right. destruct H1 as [t' Hstp].
      exists (trcons i t' tr)...  Qed.

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
  | afi_rhead : forall x i ti tr,
      appears_free_in x ti ->
      appears_free_in x (trcons i ti tr)
  | afi_rtail : forall x i ti tr,
      appears_free_in x tr ->
      appears_free_in x (trcons i ti tr).

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |- t \in S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  has_type_cases (induction H) Case; 
    intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold extend. destruct (eq_id_dec x y)...
  Case "T_App".
    apply T_App with T1...
  Case "T_RCons".
    apply T_RCons...  Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case; inversion Hafi; subst...
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
Proof with eauto.
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
  t_cases (induction t) Case;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  Case "tvar".
    simpl. rename i into y.
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
      unfold extend in H0. rewrite eq_id in H0. 
      inversion H0; subst. clear H0.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
      apply T_Var... unfold extend in H0. rewrite neq_id in H0... 
  Case "tabs".
    rename i into y. rename t into T11.
    (* If [t = tabs y T11 t0], then we know that
         [Gamma,x:U |- tabs y T11 t0 : T11->T12]
         [Gamma,x:U,y:T11 |- t0 : T12]
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
         [Gamma,x:U,y:T11 |- t0 : T12]       =>
         [Gamma,y:T11,x:U |- t0 : T12]       =>
         [Gamma,y:T11 |- [x:=v]t0 : T12] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y z)... 
      subst. rewrite neq_id...
  Case "trcons".
    apply T_RCons... inversion H7; subst; simpl...
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
  has_type_cases (induction HT) Case; 
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
    (* If the last rule used was [T_App], then [t = t1 t2], and three rules
       could have been used to show [t ==> t']: [ST_App1], [ST_App2], and 
       [ST_AppAbs]. In the first two cases, the result follows directly from 
       the IH. *)
    inversion HE; subst...
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
     used, we know [empty |- t \in Tr] and [Tlookup i Tr = Some
     Ti] for some [i] and [Tr].  We may therefore apply lemma
     [lookup_field_in_value] to find the record element this
     projection steps to. *)
    destruct (lookup_field_in_value _ _ _ _ H2 HT H)
      as [vi [Hget Htyp]].
    rewrite H4 in Hget. inversion Hget. subst...
  Case "T_RCons".
  (* If the last rule was [T_RCons], then [t = trcons i t tr] for
     some [i], [t] and [tr] such that [record_tm tr].  If the step is
     by [ST_Rcd_Head], the result is immediate by the IH.  If the step
     is by [ST_Rcd_Tail], [tr ==> tr2'] for some [tr2'] and we must also
     use lemma [step_preserves_record_tm] to show [record_tm tr2']. *)
    apply T_RCons... eapply step_preserves_record_tm...
Qed.
(** [] *)

End STLCExtendedRecords.

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

