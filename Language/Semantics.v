From Language Require Import Language.
From Language Require Import Parse.
From Language Require Import Error.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Require Import Integers.
Import ListNotations.

(*********************************
   Relation Operational Semantics
**********************************)
Inductive semantics_expression : execution_state -> execution_state -> Prop :=
  | VarSem (ex1 ex2 : execution_state) : semantics_expression ex1 ex2.

Module SemanticsRelationTest.
(* Example example50 : forall (x : variable) (tau : type), *)
  (* (type_expression [(x, (None, tau))] x tau). *)
(* Proof. apply Env_Empty. Qed. *)
End SemanticsRelationTest.

(********************************
  Function Operational Semantics
*********************************)
Fixpoint semantics_expression_exec 
  (step : nat) (ex : execution_state) : result execution_state :=
  match step with
  | 0 => Error "NonTerminatingFunction"
  | S n =>
  let (sigma, ex_stack) := ex in
  match ex_stack with
  | [] => Error "Todo"
  | (env_stack, e)::ex_stack' =>
    match e with
    | _ => Error "Todo"
    end
      (* semantics_expression_exec i (sigma, ex_stack') *)
  end
  end.

(* Example example250 : forall (x : variable), *)
  (* semantics_expression_exec BigNat []. *)

