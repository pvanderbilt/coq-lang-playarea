(** * Experiments. *)

(** This file has material from LDef.v and LProps.v that I've experiemnted with 
    and needs more investigation. *)

Load Init.
Require Export SfLib.
Require Import LibTactics.

Require Export Common LDef LProps.
Import Common LDef LProps.

Lemma len_zero_is_empty: forall (T: Type) (l : list T),
                           length l = 0 -> l = nil.
Proof.
  intros T l Hl0. destruct l.
    reflexivity.
    inversion Hl0.
Qed.

Print len_zero_is_empty.

Lemma zero_neq_one: (0=1) -> False.
Proof. intro.
inversion H.       
Qed.
(* This generates: *)
Definition zero_neq_one_generated : 0 = 1 -> False := 
fun H : 0 = 1 =>
(fun H0 : 1 = 1 -> False => H0 eq_refl)
  match H in (_ = y) return (y = 1 -> False) with
  | eq_refl =>
      fun H0 : 0 = 1 =>
      (fun H1 : 0 = 1 =>
       (fun H2 : False => (fun H3 : False => False_ind False H3) H2)
         (eq_ind 0
            (fun e : nat => match e with
                            | 0 => True
                            | S _ => False
                            end) I 1 H1)) H0
  end.

(* My hand-generated version: *)
Definition zero_neq_one' : 0 = 1 -> False :=
  fun H : 0 = 1 =>
    let P (n : nat) :=
      match n with
        | 0 => True
        | S _ => False
      end
    in (eq_ind 0 P I 1 H).

(* Note: match is used to implement nat_rect, not the other way around. *)

Definition zero_neq_succ : forall m: nat, ~ 0 = S m :=
  fun m : nat =>
    fun H : 0 = (S m) =>
      let P (n : nat) :=
        match n with
          | 0 => True
          | S _ => False
        end
      in eq_ind 0 P I (S m) H.


(* Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x 
eq_ind = 
fun (A : Type) (x : A) (P : A -> Prop) => eq_rect x P
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y
*)
(*
False_ind = fun P : Prop => False_rect P
     : forall P : Prop, False -> P *)


Definition list_hd0 {T : Type} (l : list T) (p1 : length l > 0) : T.
  (* refine (match l with nil => _ | cons hd _ => hd end). *)
  (* case l; intros. *)
  (* destruct l. *)
  case_eq l; intros; subst l.
  (* generalize dependent p1. case l; intros. *)
      apply (False_rect _ (le_Sn_0 _ p1)).
      exact t.
Defined.
Print list_hd0.

Definition list_hd0'' {T : Type} (l : list T) : (length l > 0) -> T.
  (* refine (match l with nil => _ | cons hd _ => hd end). *)
  (* case l; intros. *)
  (* destruct l. *)
  (* case_eq l; intros; subst l. *)
  (* generalize dependent p1. *)
  refine (match l with nil => fun p1' => _ | cons hd _ => fun _ => hd end).
  exact (False_rect _ (le_Sn_0 _ p1')).
Defined.
Print list_hd0''.

Definition list_hd0' {T : Type} (l : list T) (p1 : length l > 0) : T.
  (* refine (match l with nil => _ | cons hd _ => hd end). *)
  (* case l; intros. *)
  (* destruct l. *)
  (* case_eq l; intros; subst l. *)
  generalize dependent p1.
  refine (match l with nil => fun p1' => _ | cons hd _ => fun _ => hd end).
  exact (False_rect _ (le_Sn_0 _ p1')).
Defined.

  (* NOTES: 
         case l // loses connection of l to [] (needs intros.)
         case_eq // adds appropriate equation, l=[], but needs intros and subst.
                        gens code with a bunch of eq_rect_r calls.
         destruct l ==  case_eq l; intros; subst l.
         generalize dependent p1. // makes goal a function from p1; needs intros.
*)
  

Definition list_hd'' {T : Type} (l : list T) (p1 : length l > 0) : T.
  destruct l.
  (* refine (match l with nil => _ | cons hd tl => hd end). *)
  unfold length in p1. unfold gt in p1. unfold lt in p1.
  apply le_Sn_0 in p1. inversion p1.
  apply t.
Defined.
Print list_hd''.

Definition list_hd' {T : Type} (l : list T) (p1 : length l > 0) : T :=
  match l as l' return (length l' > 0 -> T) with
    | nil => (fun p1' => match (le_Sn_0 (length [] (A:=T)) p1') with end)
    | hd :: _ => fun _ => hd
  end p1.
Print list_hd'.

Definition list_hd {T : Type} (l : list T) (p1 : length l > 0) : T :=
  list_rect (fun l => (length l > 0) -> T)
            (fun p1 => False_rect T (le_Sn_0 (length (A:=T) []) p1))
            (fun hd _ _ _ => hd)
            l p1.

Definition list_hd_ne {T : Type} (l : list T) (p1 : length l <> 0) : T :=
  match l as l' return (length l' <> 0 -> T) with
    | nil => (fun p1' => match (p1' eq_refl) with end)
    | hd :: _ => fun _ => hd
  end p1.

(*
ex_falso_quodlibet  = 
fun (P : Prop) (contra : False) =>
(fun H : P => H) match contra return P with
                 end
: forall P : Prop, False -> P

False_rect = 
fun (P : Type) (f : False) => match f return P with
                              end
     : forall P : Type, False -> P 
 *)

(*
le_Sn_0 = 
fun (n : nat) (H : S n <= 0) =>
le_ind (S n) (fun n0 : nat => IsSucc n0) I
  (fun (m : nat) (_ : S n <= m) (_ : IsSucc m) => I) 0 H
     : forall n : nat, ~ S n <= 0

Inductive le (n : nat) : nat -> Prop :=
    le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m

le_ind = 
fun (n : nat) (P : nat -> Prop) (f : P n)
  (f0 : forall m : nat, n <= m -> P m -> P (S m)) =>
fix F (n0 : nat) (l : n <= n0) {struct l} : P n0 :=
  match l in (_ <= n1) return (P n1) with
  | le_n => f
  | le_S m l0 => f0 m l0 (F m l0)
  end
     : forall (n : nat) (P : nat -> Prop),
       P n ->
       (forall m : nat, n <= m -> P m -> P (S m)) ->
       forall n0 : nat, n <= n0 -> P n0

list_rect = 
fun (A : Type) (P : list A -> Type) (f : P [])
  (f0 : forall (a : A) (l : list A), P l -> P (a :: l)) =>
fix F (l : list A) : P l :=
  match l as l0 return (P l0) with
  | [] => f
  | y :: l0 => f0 y l0 (F l0)
  end
     : forall (A : Type) (P : list A -> Type),
       P [] ->
       (forall (a : A) (l : list A), P l -> P (a :: l)) ->
       forall l : list A, P l
*)

Lemma le_Sn_0 : forall n : nat, ~ S n <= 0.
  intros n Hle. admit.
Qed.

(*
Fixpoint list_index {T : Type} (l : list T) (k : nat) (p: k < length l) : T
  := match (k, l) with
       | (0, x::_) => x
       | (S k', _::r) => list_index k' r _
     end.
*)

(* TBD: Try some of these attempts at making the lookup stuff more generic:

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

(* Here is a version of [ty_xrect] that uses the underlying recursion principles,
   [ty_rect] and [list_rect].
*)

Definition ty_xrect'
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

(* This doesn't work:
  := fix F (T : ty) {struct T} : P T :=
     match T as T0 return (P T0) with
       | TBase x => fTBase x
       | TBool => fTBool
       | TArrow T1 T2 => fTArrow T1 (F T1) T2 (F T2)
       | TRcd Trb => fTRcd' Trb (G Trb)
     end
   with G (Trb : list decl) {struct Trb} : Q Trb :=
     match Trb as Trb0 return (Q Trb0) with
       | nil => fTRcd_nil'
       | (Lv x T) :: Trb' => fTRcd_cons' x T Trb' (F T) (G Trb')
     end
   for F.
*)

(* An attempt to do it as a Lemma, but the lack of a good IH kills it.

Lemma ty_xrect'' :
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
Definition ty_xrect_plus
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

(**   Here is substitution defined using the custom recursion defined in [LDef.v].
      However, I don't know how to use the match syntax with a custom 
      recursion principle, so it's not easy to read.  Further, it simplifies 
      into a mess that I can't fold back up, so I'm not using it. *)

Definition subst_ugly (x:id) (s:tm) :tm -> tm := 
  tm_xrect (fun _ => tm) (fun _ => list def)
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
 := tm_xrect
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
  tm_xrect (fun _ => tm) (fun _ => list def)
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
