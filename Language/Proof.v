From Language Require Import Language.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Integers.
Import ListNotations.

(* Type Definition *)
Definition variable : Type := nat.
Definition function : Type := nat.
Inductive type : Type :=
  | Unit
  | Bool
  | Int
  | String.
  (* | Fun (args : list type) (return_type : type). *)

(* Type Equality *)
Definition type_eqb (tau1 tau2 : type) : bool :=
  match (tau1, tau2) with
    | (Bool, Bool) | (Int, Int) | (String, String) => true
    | _ => false
  end.

(* Value Definition *)
Inductive value : Type :=
  | UnitValue
  | BoolValue (b : bool)
  | IntValue (i : nat)
  | StringValue (s : nat).

(* Type of each value *)
Definition value_to_type (v : value) : type :=
  match v with
  | UnitValue => Unit
  | BoolValue _ => Bool
  | IntValue _ => Int
  | StringValue _ => String
  end.

(* Syntax Definition *)
Inductive expression : Type :=
  | Sequence (e1 e2 : expression)
  | Let (x : variable) (e1 e2 : expression)
  | FunctionCall (f : function) (args : list expression)
  | Var (x : variable)
  | Assign (x : variable) (e : expression)
  | Value (v : value).

(* Refinement for types *)
Inductive refinement : Type := 
  | None
  | NotAccessible.

(* Complete types with refinement *)
Definition refined_type : Type := refinement * type.

(* Typing Environment *)
Definition typingEnv : Type := list (variable * refined_type).

(* Memory Model Definition *)
Definition memory : Type := list variable.
Definition symbol_table : Type := list (variable * nat).
Definition execution_stack : Type := list (symbol_table * expression).
Definition execution_state : Type := (memory * execution_stack).

(*********************************
   Relation Operational Semantics
**********************************)
Inductive semantics_expression : execution_state -> execution_state -> Prop :=
  | VarSem (ex1 ex2 : execution_state) : semantics_expression ex1 ex2.

(* Example example50 : forall (x : variable) (tau : type), *)
  (* (type_expression [(x, (None, tau))] x tau). *)
(* Proof. apply Env_Empty. Qed. *)

(****************************
   Relation Typing Expression
****************************)

Inductive type_expression : typingEnv -> expression -> type -> typingEnv -> Prop :=
  | VarType (x : variable) (tau : type) :
    type_expression [(x, (None, tau))] (Var x) tau [(x, (None, tau))]
  | Env_Rec (gamma : typingEnv) (x y : variable) (taux tauy : type) :
      x <> y
      -> type_expression ((y, (None, tauy))::gamma) (Var x) taux ((y, (None, tauy))::gamma)
      -> type_expression gamma (Var x) taux gamma.
Example example100 : forall (x : variable) (tau : type),
  type_expression [(x, (None, tau))] (Var x) tau [(x, (None, tau))].
Proof. apply VarType. Qed.

(* Result Type for Function that can fail *)
Inductive result (A E: Type) : Type :=
| Ok (x : A)
| Error (error : E).
Arguments Ok [A E].
Arguments Error [A E].

(* return monad TODO *)

Inductive customError : Type :=
  | ExecutionError
  | NonTerminatingFunction
  | Todo
  | VariableNotTypable
  | TypeError (expected given : type).

(***************************
  Function Typing Variable
***************************)
Fixpoint type_var_exec
  (gamma : typingEnv) (x : variable) : (result (type * typingEnv) customError) :=
    match gamma with
    | [] => Error VariableNotTypable
    | (y , (_, tau))::gamma' =>
        if (Nat.eqb x y)
        then
          match tau with
          | Unit | Bool | Int => Ok (tau, gamma)
          | String => Ok (tau, (y, (NotAccessible, tau))::gamma')
          end
        else (type_var_exec gamma' x)
  end.

Example example150 : forall (x : variable),
  type_var_exec [] x = Error VariableNotTypable.
Proof. reflexivity. Qed.
Example example151 : forall (x y : variable),
  Nat.eqb x y = true ->
  type_var_exec [(y, (None, Int))] x = Ok (Int, [(y, (None, Int))]).
Proof. intros. simpl. rewrite H. reflexivity. Qed.
Example example152 : forall (x : variable),
  type_var_exec [] x = Error VariableNotTypable.
Proof. reflexivity. Qed.

(*****************************
  Function Typing Expression
*****************************)
Fixpoint type_expression_exec
  (n : nat) (gamma : typingEnv) (e : expression)
  : (result (type * typingEnv) customError) :=
  match n with
  | 0 => Error NonTerminatingFunction
  | S i =>
  match e with
  | Sequence e1 e2 =>
      match type_expression_exec i gamma e1 with
      | Error err => Error err
      | Ok (tau1, gamma1) =>
          match type_expression_exec i gamma1 e2 with
          | Error err => Error err
          | Ok (tau2, gamma2) =>
              if (type_eqb tau1 Unit)
              then Ok (tau2, gamma2)
              else Error (TypeError Unit tau1)
          end
      end
  | Let x e1 e2 =>
      match type_expression_exec i gamma e1 with
      | Ok (tau1, gamma1) =>
          type_expression_exec i ((x, (None, tau1))::gamma1) e2
      | err => err
      end
  | Var x =>
    match type_var_exec gamma x with
    | Error err => Error err
    | Ok (tau, gamma') => Ok (tau, gamma') (* TODO get different gamma borrow checking *)
    end
  | Value v => Ok (value_to_type v, gamma)
  | Assign x e =>
    match type_expression_exec i gamma e with
    | Error err => Error err
    | Ok (tau, gamma') => Error Todo
    end
  | _ => Error Todo
  end
  end.

(* BigInt use for making sure function terminates *)
Definition BigNat := 10000.
(* Check BigNat. *)

Example example200 : forall (x : variable),
  type_expression_exec BigNat [] (Value (IntValue 4128)) = Ok (Int, []).
  (* 4128 : int *)
Proof. intros. reflexivity. Qed.
Example example201 : forall (x : variable),
  type_expression_exec BigNat []
  (Let x (Value (IntValue 4128)) (Var x))
  (* let x = 4128; x : int *)
    = Ok (Int, [(x, (None, Int))]).
Proof. intros. simpl. Search "eqb_refl". rewrite Nat.eqb_refl. reflexivity. Qed.
Example example202 : forall (x : variable) (s : nat),
  type_expression_exec BigNat [] 
  (Let x (Value (StringValue s)) (Var x))
  (* let x = s; x *)
    = Ok (String, [(x, (NotAccessible, String))]).
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Compute type_expression_exec BigNat [] 
  (Let 0 (Value (StringValue 1)) (Var 0)).

(**********************
  Function Semantics
**********************)
Fixpoint semantics_expression_exec 
  (n : nat) (ex : execution_state) : result execution_state customError :=
  match n with
  | 0 => Error NonTerminatingFunction
  | S i =>
  let (sigma, ex_stack) := ex in
  match ex_stack with
  | [] => Error Todo
  | (env_stack, e)::ex_stack' =>
    match e with
    | _ => Error Todo
    end
      (* semantics_expression_exec i (sigma, ex_stack') *)
  end
  end.

(* Example example250 : forall (x : variable), *)
  (* semantics_expression_exec BigNat []. *)

