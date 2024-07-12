From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List. Import ListNotations.

From Language Require Import Utils.
From Language Require Import Error.
From Language Require Import Language.
From Language Require Import Expression.
From Language Require Import ParseExpression.
From Language Require Import Program.

Definition parse_function_definition (steps : nat) (rest : list token)
  : result (function_definition * list token) :=
  match steps with
  | O => Error "Too Much Steps for Parsing"
  | S n =>
    let+ ( _, rest) = (expect "fn"%string) rest;
    let+ ( f, rest) = parseIdentifier rest;
    let+ ( _, rest) = (expect "("%string) rest;
    let+ (lv, rest) = (parse_multiple_variable n ","%string) rest;
    let+ ( _, rest) = (expect ")"%string) rest;
    let+ ( _, rest) = (expect "{"%string) rest;
    let+ ( e, rest) = (parseExpression n) rest;
    let+ ( _, rest) = (expect "}"%string) rest;
    Ok (((f, lv), e), rest)
  end.

Fixpoint parse_program_helper (steps : nat) (rest : list token)
  : result (program * list token) :=
  match steps with
  | O => Error "Too Much Steps for Parsing"
  | S n =>

  try
    let+ (f_def, rest) = parse_function_definition n rest;
    let+ (    l, rest) = parse_program_helper n rest;
    Ok (f_def :: l, rest)
  or try
    let+ (f_def, rest) = parse_function_definition n rest;
    Ok ([f_def], rest)
  or
    Ok ([], rest)

  end.

Definition parse_program (s : string) : result program :=
  match parse_program_helper BigNat (tokenize s) with
  | Ok (p, []) => Ok p
  | Ok (p,  l) => Error ("Some token left to parse:" ++ new_line 
                     ++ (token_list_to_string l))
  | Error err => Error err
  end.

Module TestParseProgram.
Compute parse_program "".
Compute parse_program "
fn main() {
  let a = 4;
  a
}".
Compute parse_program "
fn main() {
  let a = 4;
  a
}
fn main(){
  let a = 4;
  a
}
".
Compute parse_program "
fn main() {
  let a = 4;
  a
}
fn foo(x, y2) {
  let a = 4; {3, 2} ; 4 }
".
Compute parse_program "
fn main() {
  let a = 4;
  a
}
fn foo(x, y2) {
  let a = 4; {x, y}; }
".
End TestParseProgram.
