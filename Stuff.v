Print LoadPath. 

Inductive eq' (A:Type) (x:A) : A -> Type :=
    eq_refl : eq' A x x.
Print eq'_rect. Print eq_rect. Print nat_rect. 

Require Coq.Sorting.Heap.  Import Coq.Sorting.Heap. Print Tree. Print Tree_rect.

Lemma zne1 : 0 <> 1.
Proof. intro Hc.  inversion Hc. Qed. Print zne1.
(* simplies to (I think:) zne1 = 
fun Hc : 0 = 1 => 
  eq_ind 0 (fun e : nat => match e with 0 => True | S _ => False end) I 1 Hc
*)
Lemma zne1' : 1 <> 0.
Proof. intro Hc.  inversion Hc. Qed. Print zne1'.
(* zne1' = fun Hc : 1 = 0 => 
      eq_ind 1 (fun e : nat => match e with 0 => False | S _ => True end) I 0 Hc
*)
Lemma nf: ~ False.
Proof. info_auto. Qed. Print nf.
(* nf = fun H : False => H *)

Lemma nnt: ~ ~ True.
Proof. info_auto. Qed. Print nnt.
(* nnt = fun H : True -> False => H I *)

Lemma snnz: forall n: nat, (S n) <>0.
Proof. intros n H. inversion H. Qed. Print snnz.

(*
snnz = 
fun (n : nat) (H : S n = 0) =>
    // "False_ind False" -- not needed, I think
        eq_ind (S n) 
            (fun e : nat => match e with 0 => False | S _ => True end) 
            I 0 H).

False_rect = 
fun (P : Type) (f : False) => match f return P with
                              end
     : forall P : Type, False -> P

eq_rect = 
fun (A : Type) (x : A) (P : A -> Type) (f : P x) (y : A) (e : x = y) =>
match e in (_ = y0) return (P y0) with
| Logic.eq_refl => f
end
     : forall (A : Type) (x : A) (P : A -> Type), P x -> forall y : A, x = y -> P y

*)

 Print tree.
Print eq'_ind.
Print list.

Print eq_rect. Print eq_reci. Print nat_rect. Print list_rect. Print and_rect.
Cd "~". Pwd.