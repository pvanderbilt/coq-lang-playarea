(** * LEval: A big-step semantics for LDef *)

(**  This file defines a "big-step" evaluation relation and function 
      for the language defined in LDef.v. *)

Load Init.
Require Export SfLib.
Require Import LibTactics.

Require Export Common LDef.
Import Common LDef.

(* ###################################################################### *)
(** ** Values (type [evalue]) *)

Inductive evalue : Type :=
  | vabs : id -> tm -> (alist evalue) -> evalue
  | vtrue : evalue
  | vfalse : evalue
  | vrcd : (alist evalue) -> evalue.

(* ###################################################################### *)
(**  ** The [eval] relation for big-step semantics *)

Definition rctx := alist evalue.

Reserved Notation "t '/' c '||' v" (at level 40, c at level 39).
Reserved Notation "Fs '/' c '>>*' bs" (at level 40, c at level 39).

Inductive eval : tm -> rctx -> evalue -> Prop :=
  | E_Var : forall x c v,
      alookup x c = Some v ->
        tvar x / c || v
  | E_Abs : forall x T t c,
        tabs x T t / c || vabs x t c
  | E_App : forall t1 t2 v1 v2 c v,
      t1 / c || v1 ->
      t2 / c || v2 ->
      apply v1 v2 v ->
        tapp t1 t2 / c || v
  | E_Rcd : forall Fs c bs, 
      Fs / c >>* bs -> 
        trcd Fs / c || vrcd bs
  | E_Proj : forall t c bs x v, 
     t / c || vrcd bs -> 
     alookup x bs = Some v -> 
       tproj t x / c || v
  | E_True : forall c,
        ttrue / c || vtrue
  | E_False : forall c,
        tfalse / c || vfalse
  | E_If : forall tb tt te v c vb,
      tb / c || vb ->
      eval_bool vb tt te c v ->
        tif tb tt te / c || v
  | E_Let : forall x1 t1 t2 c v1 v,
      t1 / c || v1 ->
      t2 / (aextend x1 v1 c) || v ->
        tlet (Fv x1 t1) t2 / c || v

with apply : evalue -> evalue -> evalue -> Prop :=
  | EA : forall xf tf cf va vr,
      tf / (aextend xf va cf) || vr -> 
        apply (vabs xf tf cf) va vr

with eval_bool : evalue -> tm -> tm -> rctx -> evalue -> Prop :=
  | EB_true : forall tt te c v, 
      tt / c || v -> 
        eval_bool vtrue tt te c v
  | EB_false : forall tt te c v, 
      te / c || v -> 
        eval_bool vfalse tt te c v

with exec_list : list def -> rctx -> alist evalue -> Prop :=
  | EL_Nil : forall c,
        nil / c >>* nil
  | EL_Cons : forall t1 c v1 Fs' bs' x1,
      t1 / c || v1 ->
      Fs' / c >>* bs' ->
        (add_vdef x1 t1 Fs') / c >>* (aextend x1 v1 bs')

where "t '/' c '||' v" := (eval t c v) : type_scope
and  "Fs '/' c '>>*' bs" := (exec_list Fs c bs) : type_scope.

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Var" | Case_aux c "E_Abs"  | Case_aux c "E_App" 
  | Case_aux c "E_Rcd" | Case_aux c "E_Proj"
  | Case_aux c "E_True" | Case_aux c "E_False"  | Case_aux c "E_If"  ].

Hint Constructors eval apply eval_bool exec_list.

(* ###################################################################### *)
(**  ** The evalF function for big-step semantics *)


Definition vbinding := prod id evalue.
Definition vlist := list vbinding.

(** *** Return types *)

Inductive ef_return_g (Tr : Type) :  Type :=
  | efr_normal : Tr -> ef_return_g Tr
  | efr_nogas : ef_return_g Tr
  | efr_stuck : ef_return_g Tr.

Arguments efr_normal [Tr] _.
Arguments efr_nogas [Tr].
Arguments efr_stuck [Tr].

Definition ef_return := ef_return_g evalue.
Definition bf_return := ef_return_g vbinding.
Definition xf_return := ef_return_g (alist evalue).

(*
Inductive ef_return : Type :=
  | efr_normal : evalue -> ef_return
  | efr_nogas : ef_return
  | efr_stuck : ef_return .

Inductive xf_return : Type :=
  | xfr_normal : alist evalue -> xf_return
  | xfr_nogas : xf_return
  | xfr_stuck : xf_return .
*)

(** *** [LETRT] notation *)

Notation "'LETRT' x <== er1 'IN' er2" 
   := (match er1 with
         | efr_normal x => er2
         | efr_nogas => efr_nogas
         | efr_stuck => efr_stuck
       end)
   (right associativity, at level 60).

(** *** Function [evalF] *)

Fixpoint evalF (t : tm) (g : rctx) (gas : nat) {struct gas} : ef_return :=
  match gas with
    | O => efr_nogas
    | S gas' => 
      let execF_def (F : def)  (g : rctx) : bf_return :=
        match F with
          | (Fv x t) =>
              LETRT v <== evalF t g gas' IN efr_normal (x, v)
        end
      in let fix execF_pdefs (Fs : list def)  (g : rctx) : xf_return :=
        match Fs with
          | nil => efr_normal nil
          | F :: Fs' =>
              LETRT b <== execF_def F g IN
                LETRT bs' <== execF_pdefs Fs' g IN 
                  efr_normal (b :: bs')
        end
      in match t with
        | ttrue => efr_normal vtrue
        | tfalse => efr_normal vfalse
        | tvar x => 
            match alookup x g with 
              | Some v => efr_normal v 
              | None => efr_stuck 
            end
        | tabs x T t => efr_normal (vabs x t g)
        | tapp t1 t2 =>
            LETRT v1 <== evalF t1 g gas' IN
              LETRT v2 <== evalF t2 g gas' IN
                match v1 with 
                  | vabs x tf te => evalF tf (aextend x v2 te) gas'
                  | _ => efr_stuck
                end
        | trcd Fs => 
            LETRT bs <== execF_pdefs Fs g IN efr_normal (vrcd bs)
        | tproj t x => 
            LETRT v <== evalF t g gas' IN
              match v with
                | vrcd bs => match alookup x bs with
                               | Some v => efr_normal v
                               | _ => efr_stuck
                             end
                | _ => efr_stuck
              end
        | tif tb t1 t2 => 
            LETRT vb <== evalF tb g gas' IN
              match vb with
                | vtrue => evalF t1 g gas'
                | vfalse => evalF t2 g gas'
                | _ => efr_stuck
              end
        | tlet F t2 => 
            LETRT b <== execF_def F g IN
              evalF t2 (b :: g) gas'
      end
  end.

(** Pull out [execF_pdefs] and prove that it's equivalent to the inner fixpoint. *)

Definition execF_def (F : def) (g : rctx) (gas' : nat) : bf_return := 
      match F with
        | (Fv x t) =>
            LETRT v <== evalF t g gas' IN efr_normal (x, v)
      end.

Fixpoint execF_pdefs (Fs : list def) (g : rctx) (gas' : nat) : xf_return := 
      match Fs with
        | nil => efr_normal nil
        | F :: Fs' =>
              LETRT b <== execF_def F g gas' IN
                LETRT bs' <== execF_pdefs Fs' g gas' IN 
                  efr_normal (b :: bs')
      end.

Lemma execF_def_eq :
  forall (F : def) (g : rctx) (n' : nat),
    execF_def F g n' = 
    (match F with
        | Fv x t => LETRT v <== evalF t g n' IN efr_normal (x, v)
      end).
Proof.
  intros. reflexivity.
Qed.

Lemma execF_pdefs_eq :
  forall (Fs : list def) (g : rctx) (n' : nat),
    execF_pdefs Fs g n' = 
    ((fix execF_pdefs (Fs0 : list def) (g : rctx) : xf_return :=
           match Fs0 with
           | nil => efr_normal nil
           |  F :: Fs' =>
               LETRT b <==
                 match F with
                   | Fv x t => LETRT v <== evalF t g n' IN efr_normal (x, v)
                 end
               IN LETRT bs' <== execF_pdefs Fs' g IN efr_normal (b :: bs')
           end) Fs g).
Proof.
  intros. induction Fs as [ |F Fs'].
    Case "Fs=[]". reflexivity.
    Case "Fs=F::Fs'". simpl. destruct F as [x t].
      rewrite <- IHFs'. reflexivity.
Qed.

(* DOESN'T WORK :
Fixpoint evalF (t : tm) (g : rctx) (gas : nat) {struct gas} : ef_return :=
  match gas with
    | O => efr_nogas
    | S gas' => evalF' t g gas'
  end

with evalF' (t : tm) (e : rctx) (gas' : nat) {struct gas'} : ef_return :=
  match t with
    | tvar x => 
      match alookup x g with 
          | Some v => efr_normal v 
          | None => efr_stuck 
      end
    | tapp t1 t2 =>
        LETRT v1 <== evalF t1 g gas' IN
          LETRT v2 <== evalF t2 g gas' IN
            match v1 with 
              | vabs tx tf te => evalF tf (aextend tx v2 te) gas'
              | _ => efr_stuck
            end
    | [...]
  end.
*)

