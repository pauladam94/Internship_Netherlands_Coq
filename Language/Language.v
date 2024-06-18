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
