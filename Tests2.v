(** * Tests of the big-step semantics defined in LEval.v.

    This file contains tests of the big-step relation [eval] and function [evalF] as
    defined in [LEval.v].
 *)

Add LoadPath  "~/Polya/coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

Require Export Common RecordsExt LEval.
Import P3Common Records LEVAL.

(* ###################################################################### *)
(** ** Some definitions to use in testing *)

Definition rctx0 : rctx := nil.

Definition id_x := Id(0).
Definition id_y := Id(1).
Definition id_b := Id(10).

Notation f_ident T := (tabs id_x T (tvar id_x)).

Definition f_not := (tabs id_b TBool (tif (tvar id_b) tfalse ttrue)).
Definition f_pair := (tabs id_x TBool (tabs id_y TBool 
    (tabs id_b TBool (tif (tvar id_b) (tvar id_x) (tvar id_y))) )).
Definition t_pair1 :=  (tapp (tapp f_pair ttrue) tfalse).

Hint Extern 1 (alookup _ _ = _) => simpl.
Hint Extern 1 (eval (tapp ?F _) _ _) => unfold F. 
Hint Extern 1 (eval (?F) _ _) => unfold F.

(** *** Term constructors: [let1] and [lets] *)

Definition let1 (b: id * ty * tm)  (ti : tm) := 
  match b with (x, Tx, tx)  => tapp (tabs x Tx ti) tx end.

Fixpoint lets (bs: list (id * ty * tm))  (ti : tm) := 
  match bs with 
    | nil => ti 
    | b :: bs' => let1 b (lets bs' ti)
  end.

(* ###################################################################### *)
(** ** Tests of [eval] *)

(*
Ltac test_eauto := info_eauto.
Ltac test_eauto10 := info_eauto 10.
Ltac test_eauto20 := info_eauto 20.
 *)
Ltac test_eauto := eauto.
Ltac test_eauto10 := eauto 10.
Ltac test_eauto20 := eauto 20.

Example e_true : eval ttrue rctx0 vtrue.
Proof. apply E_True. Qed.

Example e_false : eval tfalse rctx0 vfalse.
Proof. auto. Qed.

Example e_id_true : eval (tapp (f_ident TBool) ttrue) rctx0 vtrue.
Proof.  test_eauto. Qed.

Example e_not_true : eval (tapp f_not ttrue) rctx0 vfalse.
Proof.  test_eauto10. Qed.

Example e_fpair: exists v, eval f_pair rctx0 v.
Proof. eauto. Qed.
(*
e_fpair = ex_intro
  (fun v : sval => eval f_pair rctx0 v)
  (vabs id_x
     (tabs id_y TBool (tabs id_b TBool (tif (tvar id_b) (tvar id_x) (tvar id_y))))
     rctx0)
  (E_Abs id_x TBool
     (tabs id_y TBool (tabs id_b TBool (tif (tvar id_b) (tvar id_x) (tvar id_y))))
     rctx0)
     : exists v, eval f_pair rctx0 v
*)

Example e_pair_p : exists v, eval (tapp f_pair ttrue) rctx0 v. 
Proof. eauto. Qed.

Example e_pair1 : exists v, eval t_pair1 rctx0 v. 
Proof. test_eauto10. Qed.

Example e_pair1t : eval (tapp t_pair1 ttrue) rctx0 vtrue.
Proof. test_eauto20. Qed.

(* ###################################################################### *)
(** ** Tests of [evalF] *)

Example ef_true : evalF ttrue rctx0 10 = efr_normal vtrue.
Proof. reflexivity. Qed.

Example ef_nogas : evalF ttrue rctx0 0 = efr_nogas.
Proof. reflexivity. Qed.

Example ef_id_true : evalF (tapp (f_ident TBool) ttrue) rctx0 10  = efr_normal vtrue.
Proof. reflexivity. Qed.

Example ef_not_true : evalF (tapp f_not ttrue) rctx0 10 = efr_normal vfalse.
Proof. reflexivity. Qed.

Example ef_fpair: exists v, evalF f_pair rctx0 10 = efr_normal v.
Proof. eexists. reflexivity. Qed.

Example ef_pair_p : exists v, evalF (tapp f_pair ttrue) rctx0 10 = efr_normal v. 
Proof. eexists. reflexivity. Qed.

Example ef_pair1 : exists v, evalF t_pair1 rctx0 10 = efr_normal v. 
Proof. eexists. reflexivity. Qed.

Example ef_pair1t : evalF (tapp t_pair1 ttrue) rctx0 10 = efr_normal vtrue.
Proof. reflexivity. Qed.

Example ef_pair_f : evalF (tapp (tabs id_x TBool (tapp (tvar id_x) ttrue)) t_pair1) rctx0 10 = efr_normal vtrue.
Proof. reflexivity. Qed.

(** ***  Tests of [let1] and [lets] *)

Definition elet1 := let1 (id_x, TBool, ttrue) (tvar id_x).
Definition elet1' := lets [(id_x, TBool, ttrue)] (tvar id_x).

Example e_let1 : evalF (elet1) rctx0 10 = efr_normal vtrue.
Proof. reflexivity. Qed.

Example e_let1' : evalF (elet1') rctx0 10 = efr_normal vtrue.
Proof. reflexivity. Qed.

(** *** Definitions of [evalF_yields_v]  and [evalF_ok] *)
Definition evalF_yields_v (t : tm) (v: evalue) : Prop :=
  evalF t rctx0 10 = efr_normal v.

Definition evalF_ok (t : tm)  : Prop :=
  exists (v: evalue), evalF_yields_v t v.

(** *** More tests *)

Definition f_and := (tabs id_x TBool (tabs id_y TBool (tif (tvar id_x) (tvar id_y) tfalse))).
Definition f_or := (tabs id_x TBool (tabs id_y TBool (tif (tvar id_x) ttrue (tvar id_y)))).

Example e_andf : evalF_yields_v 
    f_and
    (vabs id_x (tabs id_y TBool (tif (tvar id_x) (tvar id_y) tfalse)) rctx0).
Proof. (* eexists. unfold f_and. simpl. *) reflexivity. Qed.

Example e_andf_bind : evalF_ok (tapp f_and ttrue).
Proof. eexists. unfold f_and. reflexivity. Qed.

Example e_let_andf_bind : evalF_ok (let1 (id_x, TBool, ttrue) (tapp f_and ttrue)).
Proof. eexists. unfold let1, f_and. simpl. reflexivity. Qed.

(* let x = true in let x = not x in x should equal false, not true *)
Example e_bind_test1 : 
  evalF_yields_v 
    (lets [(id_x, TBool, ttrue); (id_x, TBool, (tapp f_not (tvar id_x)))] 
      (tvar id_x))
    vfalse.
Proof. reflexivity. Qed.

(* let y = true in let x = y in let y = false in x /\ ~y should equal true *)
Example e_bind_test2 : 
  evalF_yields_v 
    (lets [(id_y, TBool, ttrue); (id_x, TBool, (tvar id_y)); (id_y, TBool, tfalse)] 
      (tapp (tapp f_and (tvar id_x)) (tapp f_not (tvar id_y))))
    vtrue.
Proof. reflexivity. Qed.

(* Tests of Records *)

Definition i1 := Id (21).
Definition i2 := Id (22).

Example e_rcd0 :
  evalF_yields_v (trcd []) (vrcd []).
Proof. reflexivity. Qed.


Definition rcd1 := (trcd [
    (Fv i1 (tabs id_x TBool (tvar id_x))); 
    (Fv i2 (tabs id_x TBool (tvar id_x)))
    ]).

Example e_rcd1 :
  evalF_yields_v 
    rcd1
    (vrcd (aextend i1 (vabs id_x (tvar id_x) rctx0)
          (aextend i2 (vabs id_x (tvar id_x) rctx0) []))).
Proof. reflexivity. Qed.

Example e_rcd1p :
  evalF_yields_v 
    (tproj rcd1 i1) 
    (vabs id_x (tvar id_x) rctx0).
Proof. reflexivity. Qed.

(* Turn this into a way to explore what EvalF does.
Example e_rcd1' :

  exists v, evalF rcd1 rctx0 10 = efr_normal v.
Proof.
  eexists. simpl. reflexivity.
Qed.
*)
