(** * LEval: A big-step semantics for LDef *)

(**  This file defines a "big-step" evaluation relation and function 
      for the language defined in LDef.v. *)

Add LoadPath "~/Polya/Coq/pierce_software_foundations_3.2".
Require Export SfLib.
Require Import LibTactics.

Require Export LDef.
Import LDEF.

Module LEVAL.

(* ###################################################################### *)
(** ** Values *)

(**  *** association lists (alist) *)

Inductive alist (T : Type) : Type :=
  | anil    : alist T
  | acons : id -> T -> alist T  -> alist T.

Arguments anil {T}.
Arguments acons {T} _ _ _.

Tactic Notation "alist_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "anil" | Case_aux c "acons" ].

Fixpoint alookup {T: Type} (x: id) (a : alist T) : option T :=
  match a with
    | anil => None
    | acons y t r => if eq_id_dec y x then (Some t) else (alookup x r)
  end.

Fixpoint amap {T V: Type} (f: T -> V) (a: alist T) : alist V :=
  match a with
    | anil => anil
    | acons x t r => acons x (f t) (amap f r)
  end.


(**  *** values (evalue) *)

Inductive evalue : Type :=
  | vabs : id -> tm -> (alist evalue) -> evalue
  | vtrue : evalue
  | vfalse : evalue.

(* ###################################################################### *)
(**  ** The eval relation for big-step semantics *)

Definition rctx := alist evalue.

Reserved Notation "t '/' g '||' v" (at level 40, g at level 39).

Inductive eval : tm -> rctx -> evalue -> Prop :=
  | E_Var : forall x c v,
      alookup x c = Some v ->
        tvar x / c || v
  | E_Abs : forall x T t c,
        tabs x T t / c || vabs x t c
  | E_App : forall (t1 t2 : tm) (v1 v2 v : evalue) (c : rctx),
      t1 / c || v1 ->
      t2 / c || v2 ->
      apply v1 v2 v ->
        tapp t1 t2 / c || v
  | E_True : forall c,
        ttrue / c || vtrue
  | E_False : forall c,
        tfalse / c || vfalse
  | E_If : forall tb tt te v c vb,
      tb / c || vb ->
      eval_bool vb tt te c v ->
        tif tb tt te / c || v

with apply : evalue -> evalue -> evalue -> Prop :=
  | EA : forall xf tf cf va vr,
      tf / acons xf va cf || vr -> apply (vabs xf tf cf) va vr

with eval_bool : evalue -> tm -> tm -> rctx -> evalue -> Prop :=
  | EB_true : forall tt te c v, tt / c || v -> eval_bool vtrue tt te c v
  | EB_false : forall tt te c v, te / c || v -> eval_bool vfalse tt te c v

where "t '/' g '||' v" := (eval t g v) : type_scope.

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Var" | Case_aux c "E_Abs"  | Case_aux c "E_App"  
  | Case_aux c "E_True" | Case_aux c "E_False"  | Case_aux c "E_If"  ].
    (* | Case_aux c "E_If_True"  | Case_aux c "E_If_False" *)

Hint Constructors eval apply eval_bool.

(* ###################################################################### *)
(**  ** The evalF function for big-step semantics *)

(** *** Return type *)

Inductive ef_return : Type :=
  | efr_normal : evalue -> ef_return
  | efr_nogas : ef_return
  | efr_stuck : ef_return .

(** *** [LETRT] notation *)

Notation "'LETRT' x <== er1 'IN' er2" 
   := (match er1 with
         | efr_normal x => er2
         | efr_nogas => efr_nogas
         | efr_stuck => efr_stuck
       end)
   (right associativity, at level 60).

(** *** Function [evalF] *)

Fixpoint evalF (t : tm) (g : rctx) (gas : nat) : ef_return :=
  match gas with
    | O => efr_nogas
    | S gas' => 
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
                  | vabs tx tf te => evalF tf (acons tx v2 te) gas'
                  | _ => efr_stuck
                end
        | tabs x T t => efr_normal (vabs x t g)
        | ttrue => efr_normal vtrue
        | tfalse => efr_normal vfalse
        | tif tb t1 t2 => 
            LETRT vb <== evalF tb g gas' IN
              match vb with
                | vtrue => evalF t1 g gas'
                | vfalse => evalF t2 g gas'
                | _ => efr_stuck
              end
      end
  end.

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
              | vabs tx tf te => evalF tf (acons tx v2 te) gas'
              | _ => efr_stuck
            end
    | tabs x T t => efr_normal (vabs x t e)
    | ttrue => efr_normal vtrue
    | tfalse => efr_normal vfalse
    | tif tb t1 t2 => 
        LETRT vb <== evalF tb g gas' IN
          match vb with
            | vtrue => evalF t1 g gas'
            | vfalse => evalF t2 g gas'
            | _ => efr_stuck
          end
  end.
*)

End LEVAL.