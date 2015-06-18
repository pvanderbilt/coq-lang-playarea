(** * Experiments. *)

(** This file has material from LDef.v and LProps.v that I've experiemnted with 
    and needs more investigation. *)

Load Init.
Require Export SfLib.
Require Import LibTactics.

Require Export Common LDef LProps.
Import Common LDef LProps.

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
