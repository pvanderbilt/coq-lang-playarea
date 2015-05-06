(** This library contains utilities, primarily theorems and tactics, 
    to help with theorem proving.  It was motivated by some of the proofs is SF's
    Hoare.v.*)

Module PVUTILS.

(* For the examples: *)
Require Import Arith.

(*******************************************************************)
(** * Tactics for dealing with hypotheses that are implications. *)
(** ** Tactic [adapt_implication]
        Given an hypothesis of the form [H:P->Q] 
        where [Q] does not match the goal;
        [adapt_implication H] generates [P] as a subgoal and, when proven, 
        returns to proving the goal with hypothesis [H:Q].
*)

(**  The following theorem drives the tactic: *)

Theorem MP2 : forall P Q R : Prop, (P->Q) -> P -> (Q->R) -> R.
Proof. 
  exact (fun _ _ _ Hpq Hp Hqr => Hqr (Hpq Hp)).
Qed.

(* Alternate definitions: 
Definition MP2' : forall P Q R : Prop, (P->Q) -> P -> (Q->R) -> R
  := fun _ _ _ Hpq Hp Hqr => Hqr (Hpq Hp).

Definition MP2'' (P Q R : Prop) (Hpq : P->Q) (Hp : P) (Hqr : Q->R) : R
  :=  Hqr (Hpq Hp).

Definition MP2''' := 
  fun (P Q R : Prop) (Hpq : P->Q) (Hp : P) (Hqr : Q->R) => Hqr (Hpq Hp).
*)

(** A simple example of directly using the theorem: *)

Example MP2_ex1_prim : ~ ( 1 = 1*1 -> 1 > 1 ).
Proof. 
  intro HC. apply (MP2 _ _ _ HC). 
    auto. 
    intro. apply (gt_irrefl 1 H). 
Qed.

(** The tactic definition: *)

Ltac adapt_implication H := apply (MP2 _ _ _ H); clear H; [ | intro H].

(** A simple example of  directly using the tactic: *)

Example MP2_ex1 : ~ ( 1 = 1*1 -> 1 > 1 ).
Proof. 
  intro HC. adapt_implication HC. 
    auto. 
    apply (gt_irrefl 1 HC). 
Qed.

(** ** Tactics [adapt_universal] and [adapt_universal2]
        Given a hypothesis of the form [H: forall x, P->Q] 
        where [Q] does not match the goal,
        [adapt_universal H] generates [P] as a subgoal 
        with [x] replaced by an "existential" variable.
        When the subgoal is proven, the tactic returns to the goal
        with [H:Q'] as the hypothesis where [Q'] is [Q] with [x] replaced by
        whatever value was established for
        the existential variable that replaced [x].

      For a hypothesis of the form [H: forall y x, P->Q],
      [adapt_universal2 H v] first specializes H with [v] for [y]
      and then acts like [adapt_universal H].
*)

(**  The following theorem drives the tactics: *)

Theorem MPQ :
  forall (T : Type) (P Q : T -> Prop) (R : Prop),
    (forall x : T, P x -> Q x) -> (exists (x : T), P x /\ (Q x -> R)) -> R.
Proof. 
  intros T P Q R HfPQ Hex. 
  inversion Hex as [x [HPx HQxR]]; clear Hex.
  apply (HQxR (HfPQ x HPx)).
Qed.

(** A simple example of directly using the theorem: *)

Example MPQ_ex1_prim : ~ forall x y: nat,  y = x*x -> y > x.
Proof. intro HC. specialize (HC 1). apply (MPQ _ _ _ _ HC).
  eexists. split.
    reflexivity.
    intro. apply (gt_irrefl 1 H). 
Qed.

(** The tactic definitions: *)

Ltac adapt_universal H := 
  apply (MPQ _ _ _ _ H); clear H; eexists; split;  [  | intro H].

Ltac adapt_universal2 H y := 
  apply (MPQ _ _ _ _ (H y)); clear H; eexists; split;  [  | intro H].

(** Simple examples of using the tactics. *)

Example MPQ_ex1 : ~ forall x y: nat,  y = x*x -> y > x.
Proof. intro HC. specialize (HC 1). adapt_universal HC.
    reflexivity.
    apply (gt_irrefl 1 HC).
Qed.

Example MPQ_ex1' : ~ forall x y: nat,  y = x*x -> y > x.
Proof. intro HC. adapt_universal2 HC 1.
    reflexivity.
    apply (gt_irrefl 1 HC).
Qed.


(** An example of using both adapt_universal2 and adapt_implication. *)

Example MP2_MPQ_ex1 : ~ forall x y: nat, x >= 1  ->  y = x*x  ->  y > x.
Proof. 
  intro HC. adapt_universal2 HC 1.
    apply le_n.
    adapt_implication HC.
      reflexivity.
      apply (gt_irrefl 1 HC).
Qed.


(** ** Tactic [simplify_term_in]
        Given a hypothesis [H:P] where [P] contains a term [t],
        [simplify_term_in t H] creates a subgoal [t=?n] 
        (for some "existential" variable [?n]) which allows [t] to be simplified
        or evaluated (by [reflexivity]) in isolation.  
        Once completed, the tactic returns to the goal
        with [H:P'] as the hypothesis where [P'] is [P] with [t] replaced by its value.
*)

(**  The theorem that drives the tactic: *)

Theorem TH_simplify_term_in : 
  forall (T : Type) (x : T) (R : Prop),
    (exists z, x = z /\ (x = z -> R)) -> R.
Proof.
  intros T x R Hex.
  inversion Hex as  [z [Hxz HxzR]]; clear Hex.
  apply (HxzR Hxz).
Qed.

(**  The tactic definition: *)

Ltac simplify_term_in t H :=
  let Ht := fresh "H_sti_eq" in
  apply (TH_simplify_term_in _ t _ ); eexists; split; 
    [ | intro Ht; rewrite Ht in H; clear Ht].

(** An example of using [simplify_term_in] 
  (where the [simpl (f 10) in HC] tactic doesn't do anything): *)

Example sti_ex1 : 
  forall (f g : nat -> nat), 
    f = (fun x => x*x) -> 
    g = (fix g n := match n with 0 => 1 | (S n') => 2* (g n') end) ->
      f 10 <> g 7.
Proof.
  intros f g Df Dg HC.
     simpl (f 10) in HC.
     simplify_term_in (f 10) HC. rewrite Df. simpl. reflexivity.
     simplify_term_in (g 7) HC. rewrite Dg. simpl. reflexivity.
    inversion HC.
Qed.

(* An example of  using adapt_implication with remember.  
    BUT Doesn't do anything good.
Example MP2_ex2'' : ~ forall x: nat, x>=1 -> x*x  > x.
Proof. intro HC. specialize (HC 1). adapt_implication HC.
    apply le_n. 
    remember (1*1) as y. generalize dependent y.
    intros y H1 H2. simpl in H1. subst.
      apply (gt_irrefl 1 H2).
Qed.
*)

(* Attempting to build-in the MP2 theorem. 
Section sh.

Let MP2x : forall P Q R : Prop, (P->Q) -> P -> (Q->R) -> R
  := fun _ _ _ Hpq Hp Hqr => Hqr (Hpq Hp).

Ltac split_hyp' H :=  apply (MP2x _ _ _ H); clear H; [ | intro H ].

End sh.

Example MP2_ex1a' : ~ ( 1 = 1*1 -> 1 > 1 ).
Proof. intro HC. sh.split_hyp' HC. auto. apply (gt_irrefl 1 HC). Qed.

*)

End PVUTILS.

