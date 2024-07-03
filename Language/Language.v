From Coq Require Import Strings.String.
From Language Require Import Utils.
From Coq Require Import Lists.List. Import ListNotations.
(* Type Definition *)
(* Definition variable : Type := nat. *)
Definition variable : Type := string.

Definition function : Type := string.
Inductive type : Type :=
  | PoisonT
  | IntT
  | ProductT.

Definition type_to_string (t : type) : string :=
  match t with
  | PoisonT => "Unit"
  | IntT => "Int"
  | ProductT => "Product"
  end.

(* Type Equality *)
Definition type_eqb (tau1 tau2 : type) : bool :=
  match (tau1, tau2) with
    | (IntT, IntT) | (ProductT, ProductT) | (PoisonT, PoisonT) => true
    | _ => false
  end.

(* Value Definition *)
Inductive value : Type :=
  | PoisonV
  | IntV (i : nat).

(* Type of each value *)
Definition value_to_type (v : value) : type :=
  match v with
  | PoisonV => PoisonT
  | IntV _ => IntT
  end.

(* Syntax Definition *)
Inductive expression : Type :=
  | Let (x : variable) (e1 e2 : expression)
  | FunctionCall (f : function) (args : list expression)
  | Assign (x : variable) (e : expression)
  | Var (x : variable)
  | Value (v : value)
  | Product (l : list expression)
  | Sequence (e1 e2 : expression).

(* Refinement for types *)
Inductive refinement : Type :=
  | None
  | NotAccessible.

(* Complete types with refinement *)
Definition refined_type : Type := refinement * type.

(* Typing Environment *)
Definition typingEnv : Type := list (variable * refined_type).

(* Pretty Printing *)
Definition value_to_string (v : value) : string :=
  match v with
  | PoisonV => "Poison"
  | IntV i => nat_to_string i
  end.

Fixpoint args_to_string (step : nat) (args : list expression) : string :=
  match step with
  | O => "too much step"
  | S n =>

  match args with
  | [] => ""
  | [h] => expression_to_string_helper n h
  | h::q => expression_to_string_helper n h ++ "," ++ args_to_string n q
  end

  end

with expression_to_string_helper (step : nat) (e : expression) : string :=
  match step with
  | O => "too much step"
  | S n => 

  match e with
  | Let x e1 e2 => "let " ++ x ++ "=" ++ expression_to_string_helper n e1  ++ ";"
                              ++ expression_to_string_helper n e2
  | FunctionCall f args => f ++ "(" ++ args_to_string n args ++ ")"
  | Assign x e => x ++ "=" ++ expression_to_string_helper n e
  | Var x => x
  | Value v => value_to_string v
  | Product args => "{" ++ args_to_string n args ++ "}"
  | Sequence e1 e2 => expression_to_string_helper n e1 ++ ";" 
                   ++ expression_to_string_helper n e2
  end
  
  end.

Definition expression_to_string (e : expression) : string :=
  expression_to_string_helper BigNat e.
