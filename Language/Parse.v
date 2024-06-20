From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List. Import ListNotations.
From Language Require Import Error.
From Language Require Import Language.

Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32)   (* space *)
           (n =? 9))   (* tab *)
      (orb (n =? 10)   (* linefeed *)
           (n =? 13)). (* Carriage return. *)

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

(* More precise tokenizer *)
(* 
  - cls the chartype your are waiting for
  - acc the accumulator for the current token
  - xs the rest of the string (=list ascii) to parse.
*)
Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with
          | [] => []
          | _::_ => [acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "("      =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")"      =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _    =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x  =>
      tokenize_helper alpha (x::acc) xs'
    | alpha, digit, x =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x  =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x  =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x         =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map
    (fun l => string_of_list (rev l))
    (tokenize_helper white [] (list_of_string s)).

Module TestTokenize.

Compute tokenize "let2if abcdefg123456 if let3 23 cdjnc 2a".
Example test1 :
    tokenize "let abc12=3;  223*(3+(a+c)) ;
    foo(drop(x))"
  = ["let";"abc12"; "="; "3"; ";"; "223";
     "*"; "("; "3"; "+"; "("; "a"; "+"; "c";
     ")"; ")"; ";"; "foo"; "("; "drop"; "(";
     "x"; ")"; ")"]%string.
Proof. reflexivity. Qed.

Example test2 : tokenize "let x = foo ( drop(y)) y;"
= ["let"; "x"; "=";"foo"; "("; "drop"; "("; "y";
   ")"; ")"; "y"; ";"]%string.
Proof. reflexivity. Qed.

Compute tokenize "let x = 4;".

End TestTokenize.

(* TODO put this in Error.v *)

(* Definition parser (T : Type) := *)
(*   list token -> result (T * list token). *)

Fixpoint many_helper {T} 
  (p : list token -> result (T * list token)) 
  acc steps xs :=
  match steps, p xs with
  | 0, _ =>
      Error "Too many recursive calls"
  | _, Error _ =>
      Ok ((rev acc), xs)
  | S steps', Ok (t, xs') =>
      many_helper p (t :: acc) steps' xs'
  end.

(** A (step-indexed) parser that expects zero or more [p]s: *)

Definition many {T}
  (p : list token -> result (T * list token))
  (steps : nat) : list token -> result (list T * list token) :=
  many_helper p [] steps.

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
Definition parseIdentifier
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

Fixpoint parseSimpleExpression (steps : nat) (rest : list token)
  : result (expression * list token) :=
  match steps with
  | O => Error "Too Much Steps for Parsing"
  | S n =>
  match rest with
  | [] => Ok(Value UnitV, [])
  | _::_ =>

  try
    let+ ( x, rest) = (firstExpect "let"%string parseIdentifier) rest;
    let+ (e1, rest) = (firstExpect "="%string (parseSimpleExpression n)) rest;
    let+ (e2, rest) = (firstExpect ";"%string (parseExpression n)) rest;
    Ok (Let x e1 e2, rest)
  or try
    let+ ( x, rest) = parseIdentifier rest;
    let+ ( e, rest) = (firstExpect "="%string (parseSimpleExpression n)) rest;
    Ok (Assign x e, rest)
  or try
    let+ ( f, rest) = parseIdentifier rest;
    let+ ( _, rest) = (expect "("%string) rest;
    let+ ( l, rest) = (parseArguments n) rest;
    let+ ( _, rest) = (expect ")"%string) rest;
    Ok (FunctionCall f l, rest)
  or try
    let+ ( i, rest) = parseNumber rest;
    Ok (Value (IntV i), rest)
  or try
    let+ ( x, rest) = parseIdentifier rest;
    Ok (Var x, rest)
  or try
    let+ ( _, rest) = (expect "("%string) rest;
    let+ ( _, rest) = (expect ")"%string) rest;
    Ok (Value UnitV, rest)
  or
    Error "Not managed to parse"
  end
  end

with parseArguments (steps : nat) (rest : list token)
  : result (list expression * list token) :=
  match steps with
  | O => Error "Too Much Steps for Parsing"
  | S n =>
  try
    let+ (e1, rest) = (parseExpression n) rest;
    let+ ( l, rest) = (firstExpect ","%string (parseArguments n)) rest;
    Ok (e1 :: l, rest)
  or try
    let+ (e1, rest) = (parseExpression n) rest;
    Ok ([e1], rest)
  or
    let+ ( _,    _) = (expect ")"%string) rest;
    Ok ([], rest)
  end

with parseExpression (steps : nat) (rest : list token)
  : result (expression * list token) :=
  match steps with
  | O => Error "Too Much Steps for Parsing"
  | S n =>
  try
    let+ (e1, rest) = (parseSimpleExpression n) rest;
    let+ (e2, rest) = (firstExpect ";"%string (parseExpression n)) rest;
    Ok (Sequence e1 e2, rest)
  or
    let+ ( e, rest) = (parseSimpleExpression n) rest;
    Ok (e, rest)
  end.

Definition BigNat := 1000.

Definition parseSimple (s : string) : result expression :=
  match parseSimpleExpression BigNat (tokenize s) with
  | Ok (res,  [] ) => Ok res
  | Ok (res, _::_) => Error "Some token left to parse"
  | Error err => Error err
  end.

Definition parse (s : string) : result expression :=
  match parseExpression BigNat (tokenize s) with
  | Ok (res,  [] ) => Ok res
  | Ok (res, _::_) => Error "Some token left to parse"
  | Error err => Error err
  end.

Module TestParse.
Compute parse "3".
Compute parse "x234".
Compute parse "x = 4".
Compute parse "x = y".
Compute parse "let x = y;".
Compute parse "let x = y; 3".
Compute parse "let x = y; let z23 = 3;".
Compute parse "let x = y; let z23 = 3". (* Error *)
Compute parse "foo23()".
Compute parse "foo23(x)".
Compute parse "foo23(x, y)".
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
End TestParse.
