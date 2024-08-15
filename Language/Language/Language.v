From Coq Require Import Strings.String.
Require Import Utils.Utils.
From Coq Require Import Lists.List. Import ListNotations.

(* Type Definition *)
Definition variable : Type := string.
Definition block : Type := nat.
Definition offset : Type := nat.
Definition function_name : Type := string.
Inductive type : Type :=
  | PoisonT
  | IntT
  | ProductT.
Inductive operation : Type := Add | Sub.

Definition operation_to_string (op : operation) : string :=
  match op with
  | Add => "+"
  | Sub => "-"
  end.

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
  | NullPtr
  | Poison
  | Integer (i : nat)
  | Ptr (b : block) (off : offset).

(* Type of each value *)
Definition value_to_type (v : value) : type :=
  match v with
  | NullPtr => ProductT
  | Poison => PoisonT
  | Integer _ => IntT
  | Ptr b off => ProductT
  end.

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
  | NullPtr => "ptr(null)"
  | Poison => "Poison"
  | Integer i => nat_to_string i
  | Ptr b off => "ptr(" ++ nat_to_string b ++ ", " ++ nat_to_string off ++ ")"
  end.

Fixpoint args_to_string (args : list variable) : string :=
  match args with
  | [] => ""
  | [h] => h
  | h::q => h ++ ", " ++ args_to_string q
  end.

Inductive lang_flag : Type :=
  | Rust
  | C.

Definition lang_flag_to_string (lang : lang_flag) : string :=
  match lang with
  | Rust => "Rust"
  | C => "C"
  end.
