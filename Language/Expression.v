From Coq Require Import Strings.String.
From Language Require Import Language.
From Language Require Import Utils.

(* Syntax Definition *)
Inductive real_e : Type :=
  | ALet (x : variable) (e1 e2 : real_e)
  | AFunctionCall (f : function_name) (args : list real_e)
  | ADerefAssign (x : variable) (y : real_e)
  | AAssign (x : variable) (y : real_e)
  | AVar (x : variable)
  | AValue (v : value)
  | AProduct (l : list real_e)
  | ASequence (e1 e2 : real_e)
  | ABorrow (v : variable)
  | ADeref (v : variable).

Inductive expression : Type :=
  | Let (x : variable) (e1 e2 : expression)
  | FunctionCall (f : function_name) (args : list variable)
  | DerefAssign (x : variable) (y : variable)
  | Assign (x : variable) (y : variable)
  | Var (x : variable)
  | Value (v : value)
  | Product (l : list variable)
  (* | Sequence (e1 e2 : expression) *)
  | Borrow (v : variable)
  | Deref (v : variable)
  | Op (op : operation) (x y : variable)
  | IfEqual (x y: variable) (first : expression) (second : expression).

Fixpoint expression_to_string (e : expression) : string :=
  match e with
  | Let x e1 e2 => "(let " ++ x ++ " = " ++ expression_to_string e1  ++ ";"
    ++ nl ++ expression_to_string e2 ++ ")"
  | FunctionCall f args => f ++ "(" ++ args_to_string args ++ ")"
  | DerefAssign x y => "*" ++ x ++ " = " ++ y
  | Assign x y => x ++ " = " ++ y
  | Var x => x
  | Value v => value_to_string v
  | Product args => "{" ++ args_to_string args ++ "}"
  | Borrow x => "&" ++ x
  | Deref x => "*" ++ x
  | Op op x y => x ++ " " ++ operation_to_string op ++ " " ++ y
  | IfEqual x y first second => "if" ++ x ++ "==" ++ y ++ "{" ++ nl ++
    expression_to_string first ++ nl ++
    "} else" ++ "{" ++ nl ++
    expression_to_string second ++ nl ++ "}"
  end.
