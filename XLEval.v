(** ** An experiment using extended recursion to define [Eval] *)

(**
    This file contains an attempt at using the extended induction principle 
    for terms to define the [eval] function.  Since it recurses on the 
    structure of terms, it doesn't need the notion of gas (until we add recursion).

   It works pretty well until we get to [tapp]: we can get [v1] and [v2] and
   turn [v2] into [(vabs x t gf)] but there's no way to evaluate [t]
   since there's no direct access to [eval].

   However, the [tabs x T t] branch has [ev_t] which is essentially [(eval t)].
   So what we want is to store ev_t in [vabs] instead of the raw term, [t].
   But the type of [ev_t] is [(valist -> nat -> ef_return)] which runs into the
   "Non strictly positive occurrence" prohibition because [valist] is to the left of
   an arrow.  Variations with [value] or [vbinding] to the left also don't work.
*)


Load Init.
Require Export SfLib.
Require Import LibTactics.

Require Export Common LDef.
Import Common LDef.

Inductive ef_return_g (Tr : Type) :  Type :=
  | efr_normal : Tr -> ef_return_g Tr
  | efr_nogas : ef_return_g Tr
  | efr_stuck : ef_return_g Tr.

Arguments efr_normal [Tr] _.
Arguments efr_nogas [Tr].
Arguments efr_stuck [Tr].


Inductive value : Type :=
  | vid : id -> value
  | vabs : id -> (valist -> nat -> ef_return_g value) -> valist -> value
  | vtrue : value
  | vfalse : value
  | vrcd : valist -> value
with vbinding : Type :=
  | vbF : id -> value -> vbinding
with valist : Type :=
  | vl_nil : valist
  | vl_cons : vbinding -> valist -> valist.


Definition ef_return := ef_return_g value.
Definition bf_return := ef_return_g vbinding.
Definition xf_return := ef_return_g valist.


Notation "'LETRT' x <== er1 'IN' er2" 
   := (match er1 with
         | efr_normal x => er2
         | efr_nogas => efr_nogas
         | efr_stuck => efr_stuck
       end)
   (right associativity, at level 60).

Fixpoint alookup (x: id) (a: valist) : option value :=
  match a with
    | vl_nil => None
    | vl_cons (vbF y v) a' => 
        if eq_id_dec y x then (Some v) else (alookup x a')
    end.

Definition eval_tmf : tm -> valist -> nat -> ef_return :=
  tm_xrect 
    (*P*)    (fun _ => valist -> nat -> ef_return)
    (*Q*)    (fun _ => valist -> nat -> bf_return)
    (*QL*)   (fun _ => valist -> nat -> xf_return)
    (* ttrue *) (fun _ _ => efr_normal vtrue)
    (* ttfalse *) (fun _ _ => efr_normal vfalse)
    (* tvar *) (fun x g n' => 
                  match alookup x g with 
                    | Some v => efr_normal v 
                    | None => efr_stuck 
                  end)
    (* tabs *) (fun x T t ev_t g n' => 
                  efr_normal (vabs x (ev_t vl_nil) g))
    (* tapp *) (fun t1 ef_t1 t2 ef_t2 g n' =>
                  LETRT v1 <== ef_t1 g n' IN
                    LETRT v2 <== ef_t2 g n' IN
                      match v1 with 
                        | vabs x tf te => 
                            tf (* (vl_cons (vbF x v2) te) *) n' 
                        | _ => efr_stuck
                      end)
    (* trcd *) (fun Fs ef_Fs g n' => 
                  LETRT bs <== ef_Fs g n' IN efr_normal (vrcd bs))
    (* tproj *) (fun t ef_t x g n' => 
                  LETRT v <== ef_t g n' IN
                    match v with
                      | vrcd bs => match alookup x bs with
                                     | Some v => efr_normal v
                                     | _ => efr_stuck
                                   end
                      | _ => efr_stuck
                    end)
      (* tif *) (fun tb ef_tb tt ef_tt te ef_te g n' => 
                  LETRT vb <== ef_tb g n' IN
                    match vb with
                      | vtrue => ef_tt g n'
                      | vfalse => ef_te g n'
                      | _ => efr_stuck
                    end)
      (* tlet *) (fun F ef_F t2 ef_t2 g n' => 
                  LETRT b <== ef_F g n' IN
                    ef_t2 (vl_cons b g) n')
      (* Fv *) (fun x t ef_t g n' => 
                  LETRT v <== ef_t g n' IN 
                    efr_normal (vbF x v))
      (* nil *) (fun _ _ => efr_normal vl_nil)
      (* cons *) (fun F ef_F Fs' ef_Fs' g n' => 
                  LETRT b <== ef_F g n' IN
                    LETRT bs' <== ef_Fs' g n' IN 
                      efr_normal (vl_cons b bs')).


Fixpoint evalF (t : tm) (g : valist) (n : nat) : ef_return :=
  match n with
    | O => efr_nogas
    | S n' => eval_tmf t g n'
  end.
