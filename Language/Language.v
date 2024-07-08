From Coq Require Import Strings.String.
From Language Require Import Utils.
From Coq Require Import Lists.List. Import ListNotations.
(* Type Definition *)
(* Definition variable : Type := nat. *)
Definition variable : Type := string.
Definition block : Type := nat.
Definition offset : Type := nat.
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
  | Poison
  | Integer (i : nat)
  | Ptr (b : block) (off : offset).

(* Type of each value *)
Definition value_to_type (v : value) : type :=
  match v with
  | Poison => PoisonT
  | Integer _ => IntT
  | Ptr b off => ProductT
  end.

(* Syntax Definition *)
Inductive expression : Type :=
  | Let (x : variable) (e1 e2 : expression)
  | FunctionCall (f : function) (args : list variable)
  | Assign (x : variable) (y : variable)
  | Var (x : variable)
  | Value (v : value)
  | Product (l : list variable)
  | Sequence (e1 e2 : expression)
  | Borrow (v : variable)
  | Deref (v : variable).

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
  | Poison => "Poison"
  | Integer i => nat_to_string i
  | Ptr b off => "ptr(" ++ nat_to_string b ++ ", " ++ nat_to_string off ++ ")"
  end.

Fixpoint args_to_string (args : list variable) : string :=
  match args with
  | [] => ""
  | [h] => h
  | h::q => h ++ "," ++ args_to_string q
  end.

Fixpoint expression_to_string (e : expression) : string :=
  match e with
  | Let x e1 e2 => "let " ++ x ++ "=" ++ expression_to_string e1  ++ ";"
                              ++ expression_to_string e2
  | FunctionCall f args => f ++ "(" ++ args_to_string args ++ ")"
  | Assign x y => x ++ "=" ++ y
  | Var x => x
  | Value v => value_to_string v
  | Product args => "{" ++ args_to_string args ++ "}"
  | Sequence e1 e2 => expression_to_string e1 ++ ";" 
                   ++ expression_to_string e2
  | Borrow x => "&" ++ x
  | Deref x => "&" ++ x
  end.

(* Definition expression_to_string (e : expression) : string := *)
(*   expression_to_string_helper BigNat e. *)
