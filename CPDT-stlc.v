(* From CPDT book *)

Inductive type : Type :=
  | Nat : type
  | Func : type -> type -> type.

Fixpoint typeDenote (t : type) : Type := 
  match t with
    | Nat => nat
    | Func t1 t2 => typeDenote t1 -> typeDenote t2
  end.

Section var.
  Variable var : type -> Type.
  Inductive term : type -> Type := 
    | Var : forall t, var t -> term t
    | Const : nat -> term Nat
    | Plus: term Nat -> term Nat -> term Nat
    | Abs : forall td tr, (var td -> term tr) -> term (Func td tr)
    | App : forall td tr, term (Func td tr) -> term td -> term tr
    | Let: forall t1 t2, term t1 ->(var t1 ->term t2)->term t2. 
End var.
Implicit Arguments Var [var t].
Implicit Arguments Const [var].
Implicit Arguments Plus [var].
Implicit Arguments Abs [var td tr].
Implicit Arguments App [var td tr].
Implicit Arguments Let [var t1 t2].


Definition Term t := forall var, term var t.

Example add : Term (Func Nat (Func Nat Nat)) := 
	fun var => Abs (fun x => Abs (fun y => Plus (Var x) (Var y))).
Example three_the_hard_way : Term Nat := 
	fun var => App (App (add var) (Const 1)) (Const 2).

Fixpoint termDenote t (e : term typeDenote t) : typeDenote t := 
  match e with
    | Var _ v => v
    | Const n => n
    | Plus e1 e2 => termDenote _ e1 + termDenote _ e2
    | Abs _ _ e1 => fun x => termDenote _ (e1 x)
    | App _ _ e1 e2 => (termDenote _ e1) (termDenote _ e2)
    | Let _ _ e1 e2 => termDenote _ (e2 (termDenote _ e1))
  end.

Definition TermDenote t (E : Term t) : typeDenote t := termDenote _ (E typeDenote).
Eval compute in TermDenote _ three_the_hard_way.
Eval compute in TermDenote _ add.

(* Fixpoint eval vt t (e : term (term vt) t) : term vt t :=
  match e with
    | Var e1 => e1
    | Const n => Const n
    | Plus e1 e2 => Plus (eval vt Nat e1) (eval vt Nat e2)
    | Abs td tr e1 => Abs (fun x => eval vt tr (e1 (Var x)))
    | App _ _ e1 e2 => App (eval vt t e1) (eval vt t e2)
    | Let _ _ e1 e2 => Let (eval vt t e1) (fun x => eval vt t (e2 (Var x)))
  end.

 *)
