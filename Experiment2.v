

Inductive le (n : nat) : nat -> Prop :=
  | le_n : n <= n 
  | le_S : forall m : nat, n <= m -> n <= S m 
where "a '<=' b" := (le a b).

Lemma le_ind_def : le_ind = 
  fun (n : nat) (P : nat -> Prop) 
    (f_n : P n)
    (f_S : forall m : nat, n <= m -> P m -> P (S m)) =>
  fix F (n0 : nat) (e : n <= n0) {struct e} : P n0 :=
    match e in (_ <= n1) return (P n1) with
      | le_n => f_n
      | le_S m e' => f_S m e' (F m e')
    end.
Proof. reflexivity. Qed.
