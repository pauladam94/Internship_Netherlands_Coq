From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List. Import ListNotations.
Require Import Utils.Utils.
Require Import Lexer.Lexer.
Require Import Utils.Error.
Require Import Language.Language.
Require Import Expression.Expression.

(** A parser that expects a given token, followed by [p]: *)
Definition firstExpect {T}
  (t : token)
  (p : list token -> result (T * list token))
  : list token -> result (T * list token) :=
  fun xs => match xs with
            | x::xs' =>
              if string_dec x t
              then p xs'
              else Error ("expected '" ++ t ++ "'.")
            | [] =>
              Error ("expected '" ++ t ++ "'.")
            end.

(** A parser that expects a particular token: *)
Definition expect (t : token) : list token -> result (unit * list token) :=
  firstExpect t (fun xs => Ok (tt, xs)).

(* We suppose that we get token from the previous lexer *)
Definition parse_identifier
  (l : list token) : result (string * list token) :=
  match l with 
  | [] => Error "Expected identifier"
  | h::q => 
      match list_of_string h with
      | [] => Error "Empty token"
      | c::s =>
        if isAlpha c then
          Ok(h, q)
        else 
          Error "Identifier should begin with a Letter"
      end
  end.

Definition parseNumber (xs : list token)
                     : result (nat * list token) :=
match xs with
| [] => Error "Expected number"
| x::xs' =>
    if forallb isDigit (list_of_string x) then
      Ok (fold_left
               (fun n d =>
                  10 * n + (nat_of_ascii d -
                            nat_of_ascii "0"%char))
               (list_of_string x)
               0,
             xs')
    else
      Error "Expected number"
end.

Fixpoint parse_multiple_variable (steps : nat) (end_str : string) (rest : list token)
  : result (list variable * list token) :=
  match steps with
  | 0 => Error "Too much steps for parsing"
  | S n =>

  try
    let+ (e1, rest) = parse_identifier rest;
    let+ ( l, rest) = (firstExpect ","%string 
      (parse_multiple_variable n end_str)) rest;
    Ok (e1 :: l, rest)
  or try
    let+ (e1, rest) = parse_identifier rest;
    Ok ([e1], rest)
  or
    let+ ( _,    _) = (expect ")"%string) rest;
    Ok ([], rest)

  end.

(* Let : string -> expression -> expression -> expression *)
Fixpoint list_expression_style_helper (n : nat) (l : list expression)
  (lv : list variable) (f : list variable -> expression) : expression :=
  match l with
  | [] => f lv
  | e0::l =>
    match e0 with
    | Var x => list_expression_style_helper n l (x::lv) f
    | _ =>
      let x := (String.append "phantom"%string (nat_to_string n)) in
      let e := list_expression_style_helper (S n) l (x::lv) f in
        (Let x e0 e)
    end
  end.

Definition list_expression_style (l : list expression)
  (f : list variable -> expression) : expression :=
  list_expression_style_helper 0 l [] f.

Definition two_expression_style (e1 e2 : expression)
  (f : variable -> variable -> expression) : expression :=
  match e1, e2 with
  | Var x, Var y => f x y
  | Var x, _ => Let "phantom"%string e2 (f x "phantom"%string)
  | _, Var y => Let "phantom"%string e1 (f "phantom"%string y)
  | _, _ => Let "phantom1"%string e1 (Let "phantom2"%string e2 
    (f "phantom1"%string "phantom2"%string))
  end.

Fixpoint parse_expression_prec_10 (steps : nat) (rest : list token)
  : result (expression * list token) :=
  match steps with
  | O => Error "Too Much Steps for Parsing"
  | S n =>
  match rest with
  | [] => Ok(Value Poison, [])
  | _::_ =>

  try
    let+ (  _, rest) = expect "*"%string rest;
    let+ (  x, rest) = parse_identifier rest;
    let+ (  e, rest) = firstExpect "="%string (parse_expression_prec_5 n) rest;
      match e with
      | Var y => Ok (DerefAssign x y, rest)
      | _  => Ok (Let "phantom"%string e (DerefAssign x "phantom"%string), rest)
      end
  or try
    let+ (  _, rest) = expect "*"%string rest;
    let+ (  x, rest) = parse_identifier rest;
    Ok (Deref x, rest)
  or try
    let+ (  _, rest) = expect "if"%string rest;
    let+ ( e1, rest) = parse_expression n rest;
    let+ (  _, rest) = expect "=="%string rest;
    let+ ( e2, rest) = parse_expression n rest;
    let+ (  _, rest) = expect "{"%string rest;
    let+ (fst, rest) = parse_expression n rest;
    let+ (  _, rest) = expect "}"%string rest;
    let+ (  _, rest) = expect "else"%string rest;
    let+ (  _, rest) = expect "{"%string rest;
    let+ (snd, rest) = parse_expression n rest;
    let+ (  _, rest) = expect "}"%string rest;
    Ok (two_expression_style e1 e2 (fun x y => IfEqual x y fst snd), rest)
  or try
    let+ (  _, rest) = expect "&"%string rest;
    let+ (  _, rest) = expect "mut"%string rest;
    let+ (  x, rest) = parse_identifier rest;
    Ok (BorrowMut x, rest)
  or try
    let+ (  _, rest) = expect "&"%string rest;
    let+ (  x, rest) = parse_identifier rest;
    Ok (Borrow x, rest)
  or try
    let+ (  _, rest) = expect "{"%string rest;
    let+ (  l, rest) = parse_multiple n "}"%string rest;
    let+ (  _, rest) = expect "}"%string rest;
    Ok (list_expression_style l Product, rest)
  or try
    let+ (  x, rest) = firstExpect "let"%string parse_identifier rest;
    let+ ( e1, rest) = firstExpect "="%string (parse_expression_prec_5 n) rest;
    let+ ( e2, rest) = firstExpect ";"%string (parse_expression n) rest;
    Ok (Let x e1 e2, rest)
  or try
    let+ (  x, rest) = firstExpect "let"%string parse_identifier rest;
    let+ ( e1, rest) = firstExpect "="%string (parse_expression_prec_5 n) rest;
    let+ ( e2, rest) = expect ";"%string rest;
    Ok (Let x e1 (Value Poison), rest)
  or try
    let+ (  x, rest) = parse_identifier rest;
    let+ (  e, rest) = firstExpect "="%string (parse_expression_prec_5 n) rest;
    match e with
    | Var y => Ok (Assign x y, rest)
    | _  => Ok (Let "phantom"%string e (Assign x "phantom"%string), rest)
    end
  or try
    let+ (  f, rest) = parse_identifier rest;
    let+ (  _, rest) = expect "("%string rest;
    let+ (  l, rest) = parse_multiple n ")"%string rest;
    let+ (  _, rest) = expect ")"%string rest;
    Ok (list_expression_style l (FunctionCall f), rest)
  or try
    let+ (  x, rest) = parse_identifier rest;
    Ok (Var x, rest)
  or try
    let+ (  i, rest) = parseNumber rest;
    Ok (Value (Integer i), rest)
  or
    let+ (  _, rest) = expect "("%string rest;
    let+ (  _, rest) = expect ")"%string rest;
    Ok (Value Poison, rest)
  end
  end


with parse_expression_prec_5 (steps : nat) (rest : list token)
  : result (expression * list token) :=
  match steps with
  | O => Error "Too Much Steps for Parsing"
  | S n =>
  try
    let+ ( e1, rest) = parse_expression_prec_10 n rest;
    let+ (  _, rest) = expect "+"%string rest;
    let+ ( e2, rest) = parse_expression_prec_5 n rest;
    Ok (two_expression_style e1 e2 (Op Add), rest)
  or try
    let+ ( e1, rest) = parse_expression_prec_10 n rest;
    let+ (  _, rest) = expect "-"%string rest;
    let+ ( e2, rest) = parse_expression_prec_5 n rest;
    Ok (two_expression_style e1 e2 (Op Sub), rest)
  or
    let+ ( e, rest) = (parse_expression_prec_10 n) rest;
    Ok (e, rest)
  end


with parse_multiple (steps : nat) (end_str : string) (rest : list token)
  : result (list expression * list token) :=
  match steps with
  | O => Error "Too Much Steps for Parsing"
  | S n =>
  try
    let+ (e1, rest) = (parse_expression n) rest;
    let+ ( l, rest) = (firstExpect ","%string (parse_multiple n end_str)) rest;
      Ok (l ++ [e1], rest)
  or try
    let+ (e1, rest) = (parse_expression n) rest;
    Ok ([e1], rest)
  or
    let+ ( _,    _) = (expect ")"%string) rest;
    Ok ([], rest)
  end

with parse_expression (steps : nat) (rest : list token)
  : result (expression * list token) :=
  match steps with
  | O => Error "Too Much Steps for Parsing"
  | S n =>
  try
    let+ (e1, rest) = (parse_expression_prec_5 n) rest;
    let+ (e2, rest) = (firstExpect ";"%string (parse_expression n)) rest;
    Ok (Let "_"%string e1 e2, rest)
  or try
    let+ (e1, rest) = (parse_expression_prec_5 n) rest;
    let+ (e2, rest) = expect ";"%string rest;
    Ok (Let "_"%string e1 (Value Poison), rest)
  or
    let+ ( e, rest) = (parse_expression_prec_5 n) rest;
    Ok (e, rest)
  end.

(* Definition parseSimple (s : string) : result expression := *)
(*   match parse_expression_prec_10 BigNat (tokenize s) with *)
(*   | Ok (res,  [] ) => Ok res *)
(*   | Ok (res, _::_) => Error "Some token left to parse" *)
(*   | Error err => Error err *)
(*   end. *)

Definition parse (s : string) : result expression :=
  match parse_expression BigNat (tokenize s) with
  | Ok (res, []) => Ok res
  | Ok (res,  l) => Error ("Some token left to parse:" ++ new_line 
                     ++ (list_token_to_string l))
  | Error err => Error err
  end.
Module TestParse.
Compute parse "".
Compute parse "3".
Compute parse "3 + 4".
Compute parse "let a = 3 + 4 ; 2".
Compute parse "x234".
Compute parse "x = 4".
Compute parse "x = y".
Compute parse "let x = y;".
Compute parse "let x = {4, 3}; 5".
Compute parse "{x, 3}".
Compute parse "let x = 4; f(4); 5".
Compute parse "foo(3, 4, x)".
Compute parse "let x = y; 3".
Compute parse "let x = y; let z23 = 3;".
Compute parse "let x = y; let z23 = 3; 42 + a".
Compute parse "let x = y; let z23 = 3". (* Error *)
Compute parse "foo23()".
Compute parse "foo23(x)".
Compute parse "let x = 2; foo23(x, 42)".
Compute parse "foo23(x, y);".
Compute parse "x = {x3, x4, x}".
Compute parse "let x = {x, y, 3}; 4".
Compute parse "let x = {z, y, a2}; {a, b}".
Compute parse "let x = {z, y, A} ; {c, x}".
Compute parse "let x = foo23(); 4; x = 4".
Compute parse "let x = foo23(x, y); 4".
Compute parse "3 ; 4".
Compute parse "x = 3; x = 6".
Compute parse "let x = 4;".
Compute parse "let x = 4; x".
Compute parse "let abc let". (* Error *)
Compute parse "let x = 4; let y = 12 ; 23".
Compute parse "x = 4;".
Compute parse "let x = 4; y = 12; 23".
Compute parse "let x = 4; foo(x, y); x = 12".
Compute parse "let x = &x123; *y".
Compute parse "&x123".
Compute parse "*x = y".
Compute parse "let x = 12; *x = y".
Compute parse "let x = &mut y; 23".
Compute parse "*x = 3".
Compute parse "{{x, y}; , z} ".
Compute parse "if {1, 2} == 4 {3} else {4}".
Compute parse "if x == 2 {3} else {4}".
Compute parse "let a = 4; if a == 1 {4} else {a = 12}".
Compute parse "let a = 4; *a = *b + *b;".

Compute expression_to_string
(Let "x"%string (Value (Integer 4))
            (Let ""%string
               (FunctionCall "foo"%string ["z"%string ;  "y"%string])
               (Assign "x"%string ("x2"%string)))).

End TestParse.
