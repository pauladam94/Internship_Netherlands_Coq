From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List. Import ListNotations.

Require Import Utils.Utils.
Require Import Lexer.Lexer.
Require Import Utils.Error.
Require Import Language.Language.
Require Import Expression.Expression.
Require Import Parser.ParserExpression.
Require Import Program.Program.

Definition parse_function_definition (steps : nat) (rest : list token)
  : result (function_definition * list token) :=
  match steps with
  | O => Error "Too Much Steps for Parsing"
  | S n =>
    try
      let+ ( _, rest) = (expect "fnR"%string) rest;
      let+ ( f, rest) = parse_identifier rest;
      let+ ( _, rest) = (expect "("%string) rest;
      let+ (lv, rest) = (parse_multiple_variable n ","%string) rest;
      let+ ( _, rest) = (expect ")"%string) rest;
      let+ ( _, rest) = (expect "{"%string) rest;
      let+ ( e, rest) = (parse_expression n) rest;
      let+ ( _, rest) = (expect "}"%string) rest;
      Ok ((((f, lv), e), Rust), rest)
    or
      let+ ( _, rest) = (expect "fnC"%string) rest;
      let+ ( f, rest) = parse_identifier rest;
      let+ ( _, rest) = (expect "("%string) rest;
      let+ (lv, rest) = (parse_multiple_variable n ","%string) rest;
      let+ ( _, rest) = (expect ")"%string) rest;
      let+ ( _, rest) = (expect "{"%string) rest;
      let+ ( e, rest) = (parse_expression n) rest;
      let+ ( _, rest) = (expect "}"%string) rest;
      Ok ((((f, lv), e), C), rest)
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
                     ++ (list_token_to_string l))
  | Error err => Error err
  end.

Module TestParseProgram.
Compute parse_program "".
Compute parse_program "fnR main() {}".
Compute parse_program "
fnR main() {
  let a = 4;
  a
}".
Compute parse_program "
fnR main() {
  let a = 4;
  a
}
fnR main(){
  let a = 4;
  a
}
".
Compute parse_program "
fnR main() {
  let a = 4;
  a
}
fnR foo(x, y2) {
  let a = 4; {3, 2} ; 4 }
".
Compute parse_program "
fnR main() {
  let a = 4;
  a
}
fnC foo(x, y2) {
  let a = 4; {3, 2} ; 4 }
".
Compute parse_program "
fnR main() {
  let a = 4;
  a
}
fnR foo(x, y2) {
  let a = 4; {x, y}; }
".
Compute parse_program "
fnR fib(n) {
  if n == 0 {
    1
  } else {
    fib(n - 1) + fib(n - 2)
  }
}
".
Compute parse_program "
fnC main() {
  let a = {1, 2};
  foo(&a);
}
fnR foo(a) {
  *a + 1
}
".

Compute parse_program "
fnC main() {
  let c = 10;
  let a = &c;
  let b = &c;
  foo(a, b);
  c
}".

Compute parse_program "
fnR foo(a) {
  let aref = castref(a);
  let bref = castrefmut(b);
  *aref = *aref + *b;
  *a = *a + *b;
}
". (* Error *)
Compute parse_program "
fnC main() {
  let c = 10;
  let a = &c;
  let b = &c;
  foo(a, b);
  c
}
fnR foo(a) {
  let a_ref = cast_ref(a);
  let b_ref = cast_ref_mut(b);
  *a_ref = *a_ref + *b;
  *a = *a + *b;
}
". (* Error *)


End TestParseProgram.
