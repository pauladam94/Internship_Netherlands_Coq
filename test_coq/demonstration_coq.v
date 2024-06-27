



(* Coq *)

(*
   fonction f(x) : x + 1
   f 4 = 5
 *)





(*
expression = 4

expression = e1 + e2

   expression = 4 + e2
   expression = 4 + 4

expression = 3 + 2 + 3 + 4 

2 = Successeur Successeur 0

   3 + 2 + 4

Sum e 4

   Sum (Sum 3 2) 4 ~ Sum(Sum(3, 2),4)

   Sum A B ~ Sum(A, B)

*)

Inductive naturel : Type :=
  | Zero
  | Successeur (i : naturel).

Inductive expression : Type :=
  | Nat     (i : nat)
  | Sum     (e1 e2 : expression).

(* Some Notations *)
Coercion Nat : nat >-> expression.
Notation "e1 '+++' e2" := (Sum e1 e2) (at level 0).
(* 3 +++ 4 *)

Fixpoint compute (e : expression) : nat :=
  match e with
  | Nat i => i
  | Sum e1 e2 => (compute e1) + (compute e2)
  end.

(*  10 + 2  *)
Compute compute (10 +++ 2).
(*  10 * (2 + 3)  *)
Compute compute (2 +++ 3).

Compute compute (0 +++ 2 +++ 3).

Fixpoint optimisation (e : expression) : expression :=
  match e with
  | Nat i => Nat i
  | Sum (Nat 0) e2 => e2
  | Sum e1 e2 => Sum (optimisation e1) (optimisation e2)
  end.

(* (10 * 2) + 0 *)
Compute optimisation (0 +++ 10 +++ 5).
Compute optimisation (0 +++ 2).

Theorem optimisation_correct :
  forall (e : expression),
  compute (optimisation e) = compute e.





Proof. intros. induction e as [|e1 IHe1 e2 IHe2].
(* e = Nat i *)
- unfold optimisation. simpl. reflexivity.
(* e = Sum e1 e2 *)
- destruct e1 as [i1|i1] eqn:He1.
  (* e1 = Nat i1*)
  + destruct i1 eqn:I1.
    (* i1 = 0 *)
    * unfold optimisation. reflexivity.
    (* i1 = S n *)
    * simpl. rewrite IHe2. reflexivity.
  (* e1 = Sum .. .. *)
  + simpl. simpl in IHe1.
    rewrite IHe1.
    rewrite IHe2. reflexivity.
Qed.






