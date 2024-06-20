From Language Require Import Language.
From Coq Require Import Strings.String.

(* Result Type for Function that can fail *)
Inductive result (X: Type) : Type :=
  | Ok: X -> result X
  (* | Ok (x : X) *)
  | Error (s : string).

Arguments Ok [X].
Arguments Error [X].

Inductive customError : Type :=
  | ExecutionError
  | NonTerminatingFunction
  | Todo
  | VariableNotTypable
  | TypeError (expected given : type).

(* Notations for Error *)
Notation "'let+' p = e1 ; e2"
   := (match e1 with
       | Ok p => e2
       | Error err => Error err
       end)
   (right associativity, p pattern, at level 60, e1 at next level).

Notation "'try' e1 'or' e2"
   := (
    let result := e1 in
    match result with
       | Ok _  => result
       | Error _ => e2
       end)
   (right associativity,
    at level 60, e1 at next level, e2 at next level).

Module Test.
End Test.
