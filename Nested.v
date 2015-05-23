(* Nested recursive structure *)

Add LoadPath "/Users/pv/Polya/Coq/pierce_software_foundations_3.2".
Require Export Stlc.
Require Export LibTactics.

Definition alist (X : Type) := list (id * X).

Fixpoint alist_map {X Y: Type} (f: X -> Y) (a: alist X) : alist Y :=
  match a with
    | nil => nil
    | cons (x, t) r => cons (x, (f t)) (alist_map f r)
  end.

(*
Inductive tm : Type :=
  | tvar : id -> tm
  | tnum : nat -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  (* records *)
  | tproj : tm -> id -> tm
  | trcd: rcd_tm -> tm
with rcd_tm : Type := 
  | nil : rcd_tm
  | cons : id -> tm -> rcd_tm -> rcd_tm.

Scheme tm_rec2 := Induction for tm Sort Type
  with rcd_tm_rec2 := Induction for rcd_tm Sort Type.
 *)

(*
Inductive alist2 (X: Type) : Type :=
  | nil : alist2 X
  | cons : id -> X -> alist2 X -> alist2 X.
*)
Inductive tm : Type :=
  | tvar : id -> tm
  | tnum : nat -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  (* records *)
  | tproj : tm -> id -> tm
  | trcd: (alist tm) -> tm.

Inductive ty : Type :=
  | TBase     : id -> ty
  | TArrow    : ty -> ty -> ty
  | TRcd      : (alist ty) -> ty.

Definition al1 := cons (Id 0, tnum 0) (cons (Id 1, tnum 1) nil).

Definition al1m := map (fun t => 
  match t with (i, tnum n) => (i, tnum(n+1)) | _ => (Id 0, tvar (Id 0)) end) al1.

Eval compute in al1m.

Definition al1m' := alist_map (fun t => 
  match t with tnum n => tnum(n+1) | _ => tvar (Id 0) end) al1.

Theorem maps_same_onal1m : al1m = al1m'.
Proof. reflexivity. Qed.

Theorem xxx: forall (n : nat) (ns: list nat), cons n ns = cons (n+0) ns.
Proof. intros. fequals. apply plus_n_O. Qed.

Theorem maps_same : 
  forall (a : alist tm) (f : tm-> tm), 
    alist_map f a = map (fun p => match p with (i, t') => (i, (f t')) end) a.
Proof. 
  intros. induction a as [| p r IHr].
    reflexivity. 
    simpl. rewrite <- IHr. clear IHr. destruct p.  reflexivity.
Qed.

(* Consider use of Acc to somehow create a recursive function that
  (structurally) decreases on a "proof of assessibility of x" (?) (rather than x).
*)


Fixpoint subst'' (x:id) (s:tm) (t : tm) {struct t} :  tm :=
    let fix asubst (x:id) (s:tm) (a:alist tm) {struct a} : alist tm := 
      match a with
        | [] => []
        | (x, t) :: r => (x, subst'' x s t) :: asubst x s r
      end
   in match t with
    | tvar y => if eq_id_dec x y then s else t
    | tnum n => t
    | tabs y T t1 =>  tabs y T (if eq_id_dec x y then t1 else (subst'' x s t1))
    | tapp t1 t2 => tapp (subst'' x s t1) (subst'' x s t2)
    | tproj t1 i => tproj (subst'' x s t1) i
    | trcd r => trcd (asubst x s r)
  end.

Fixpoint subst'' (x:id) (s:tm) : tm -> tm :=
  fix F (t : tm) := 
   match t with
    | tvar y => if eq_id_dec x y then s else t
    | tnum n => t
    | tabs y T t1 =>  tabs y T (if eq_id_dec x y then t1 else (F t1))
    | tapp t1 t2 => tapp (F t1) (F t2)
    | tproj t1 i => tproj (F t1) i
    | trcd r => trcd (alist_map (fun t' => F t') r)
  end.


Fixpoint subst' (x:id) (s:tm) (t:tm) {struct t} : tm :=
  let fix rsubst  (a: alist tm) : alist tm := alist_map (fun t' => (subst' x s t')) a
(*     match a with
      | nil => nil
      | cons (i, t) r' => cons  (i, (fun t' => (subst' x s t')) t) (rsubst r')
    end *)
  in
  match t with
    | tvar y => if eq_id_dec x y then s else t
    | tabs y T t1 =>  tabs y T (if eq_id_dec x y then t1 else (subst' x s t1))
    | tapp t1 t2 => tapp (subst' x s t1) (subst' x s t2)
    | tproj t1 i => tproj (subst' x s t1) i
    | trcd r => trcd (rsubst r)
  end.

Fixpoint subst (x:id) (s:tm) (t:tm) {struct t} : tm :=
  let fix rsubst  (a: alist tm) : alist tm := 
    match a with
      | nil => nil
      | cons (i, t) r' => cons  (i, (subst x s t)) (rsubst r')
    end
  in
  match t with
    | tvar y => if eq_id_dec x y then s else t
    | tabs y T t1 =>  tabs y T (if eq_id_dec x y then t1 else (subst x s t1))
    | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
    | tproj t1 i => tproj (subst x s t1) i
    | trcd r => trcd (rsubst r)
  end.


Fixpoint subst' (x:id) (s:tm) : tm -> tm :=
  fix F (t : tm) := 
    let fix amap  (f: tm -> tm) (a: alist tm) : alist tm :=
      match a with
       | nil => nil
       | cons (x, t) r => cons (x, (f t)) (alist_map f r)
     end
  in match t with
    | tvar y => if eq_id_dec x y then s else t
    | tabs y T t1 =>  tabs y T (if eq_id_dec x y then t1 else (F t1))
    | tapp t1 t2 => tapp (F t1) (F t2)
    | tproj t1 i => tproj (F t1) i
    | trcd r => trcd (amap (fun x => F x) r)
  end.



