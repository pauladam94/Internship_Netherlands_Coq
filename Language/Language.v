From Coq Require Import Strings.String.

(* Type Definition *)
(* Definition variable : Type := nat. *)
Definition variable : Type := string.
Definition function : Type := string.
Inductive type : Type :=
  | UnitT
  | BoolT
  | IntT
  | StringT.
  (* | Fun (args : list type) (return_type : type). *)

(* Type Equality *)
Definition type_eqb (tau1 tau2 : type) : bool :=
  match (tau1, tau2) with
    | (BoolT, BoolT) | (IntT, IntT) | (StringT, StringT) => true
    | _ => false
  end.

(* Value Definition *)
Inductive value : Type :=
  | UnitV
  | BoolV (b : bool)
  | IntV (i : nat)
  | StringV (s : nat).

(* Type of each value *)
Definition value_to_type (v : value) : type :=
  match v with
  | UnitV => UnitT
  | BoolV _ => BoolT
  | IntV _ => IntT
  | StringV _ => StringT
  end.

(* Syntax Definition *)
Inductive expression : Type :=
  | Let (x : variable) (e1 e2 : expression)
  | FunctionCall (f : function) (args : list expression)
  | Assign (x : variable) (e : expression)
  | Var (x : variable)
  | Value (v : value)
  | Sequence (e1 e2 : expression).

(* Refinement for types *)
Inductive refinement : Type :=
  | None
  | NotAccessible.

(* Complete types with refinement *)
Definition refined_type : Type := refinement * type.

(* Typing Environment *)
Definition typingEnv : Type := list (variable * refined_type).

(* Memory Model Definition *)
Inductive semaphore : Type :=
  | Writing
  | Reading (n : nat).
Definition memory : Type := list variable.
Definition symbol_table : Type := list (variable * nat).
Definition execution_stack : Type := list (symbol_table * expression).
Definition execution_state : Type := (memory * execution_stack).
