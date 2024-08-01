From Coq Require Import Strings.String.
From Language Require Import Language.
From Language Require Import Utils.
From Language Require Import Error.
From Language Require Import Expression.
From Coq Require Import Lists.List. Import ListNotations.

Definition function_definition : Type :=
  (function_name * list variable * expression).
Definition program : Type := list function_definition.

Definition function_definition_to_string (f_def : function_definition)
  : string :=
  let (f_and_args, e) := f_def in
  let (f, args) := f_and_args in
  "fn" ++ "(" ++ args_to_string args ++ ") {" ++ nl
    ++ expression_to_string e ++ nl ++ "}".

Fixpoint program_to_string (p : program) : string :=
  match p with
  | [] => ""
  | f_def::p =>
    function_definition_to_string f_def ++ program_to_string p
  end.

Fixpoint get_function_args_expression (f : function_name) (p : program)
  : result (list variable * expression) :=
  match p with
  | [] => Error "Function 'main' not found in the program"
  | ((f0, args) ,e)::p =>
    if String.eqb f0 f then
      Ok (args, e)
    else
      get_function_args_expression f p
  end.
