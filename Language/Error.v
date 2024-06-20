From Language Require Import Language.
From Coq Require Import Strings.String.

(* Result Type for Function that can fail *)
Inductive result (X: Type) : Type :=
  | Ok: X -> result X
  (* | Ok (x : X) *)
  | Error (s : string).

(* Inductive res (A: Type) : Type := *)
(* | OK: A -> res A *)
(* | Error: errmsg -> res A. *)
Arguments Ok [X].
Arguments Error [X].

(* Check Ok. *)

(* Inductive result (A E: Type) : Type := *)
(* | Ok (x : A) *)
(* | Error (error : E). *)
(**)
(* Arguments Ok [A E]. *)
(* Arguments Error [A E]. *)

(* return monad TODO *)

Inductive customError : Type :=
  | ExecutionError
  | NonTerminatingFunction
  | Todo
  | VariableNotTypable
  | TypeError (expected given : type).

(* Notation "let+ x = y ; e " := ( *)
(*   match y with *)
(*     | Ok a => let x := a in e *)
(*     | Error err => Error err *)
(*   end *)
(*   ) (no associativity, only parsing, at level 50). *)

Module Test.
End Test.
