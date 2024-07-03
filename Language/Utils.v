From Coq Require Import Strings.String.
Local Open Scope string_scope.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Arith.
From Coq Require Import Strings.Ascii.

Definition new_line := "
"%string.

(* BigInt use for making sure function terminates *)
Definition BigNat := 1000.
(* Check BigNat. *)

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

(* Nat to String converter *)

Definition single_digit_to_string (n : nat) : string :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2"
  | 3 => "3" | 4 => "4" | 5 => "5"
  | 6 => "6" | 7 => "7" | 8 => "8"
  | _ => "9"
  end.

Fixpoint nat_to_string_helper (step : nat) (n : nat) : string :=
  match step with
  | O => "too long int"
  | S step' =>
  if (Nat.leb n 10)
  then (single_digit_to_string n)
  else (nat_to_string_helper step' (n / 10)%nat ) 
       ++ (single_digit_to_string (n mod 10))
  end.

Definition nat_to_string (n : nat) : string := nat_to_string_helper 10 n.

Module TestNatToString.
Example test1 : nat_to_string 234 = "234".
Proof. reflexivity. Qed.
End TestNatToString.
