From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List. Import ListNotations.
Require Import Utils.Utils.
Require Import Utils.Error.
Require Import Language.Language.
Require Import Expression.Expression.

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
    | _, _, "&"      =>
      tk ++ ["&"]::(tokenize_helper other [] xs')
    | _, _, "*"      =>
      tk ++ ["*"]::(tokenize_helper other [] xs')
    | _, _, ";"      =>
      tk ++ [";"]::(tokenize_helper other [] xs')
    | _, _, "{"      =>
      tk ++ ["{"]::(tokenize_helper other [] xs')
    | _, _, "}"      =>
      tk ++ ["}"]::(tokenize_helper other [] xs')
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

Fixpoint list_token_to_string_helper (l : list token) : string :=
    match l with
    | [] => ""%string
    | [h] => "'" ++ h ++ "'"
    | h::q => "'" ++ h ++ "',"%string ++ list_token_to_string_helper q
    end.

Definition list_token_to_string (l : list token) : string :=
  "["%string ++ list_token_to_string_helper l ++ "]"%string.

Module TestTokenize.

Compute tokenize "let2if abcdefg123456 if let3 23 cdjnc 2a".
Example test1 :
    tokenize "let abc12=3;  223*(3+(a+c));
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

Example test3 : tokenize "let x = {2, y, x = 3}; {3, 4}"
= ["let"; "x"; "="; "{"; "2"; ","; "y"; ","; "x"; 
   "="; "3"; "}"; ";"; "{"; "3"; ","; "4"; "}"]%string.
Proof. reflexivity. Qed.

Example test4 : tokenize "let x = {2, y, 2}; 4"
= ["let"; "x"; "="; "{"; "2"; ","; "y"; ","; "2"; "}";
   ";"; "4"]%string.
Proof. reflexivity. Qed.

Compute tokenize "let x = 4;".

End TestTokenize.
