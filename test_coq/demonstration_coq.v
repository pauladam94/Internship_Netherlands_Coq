







Inductive expression : Type :=
  | Nat     (i : nat)
  | Sum     (e1 e2 : expression).

(* Some Notations *)
Coercion Nat : nat >-> expression.
Notation "e1 '+++' e2" := (Sum e1 e2) (at level 0).


Fixpoint compute (e : expression) : nat :=
  match e with
  | Nat i => i
  | Sum e1 e2 => (compute e1) + (compute e2)
  end.

(*  10 + 2  *)
Compute compute (10 +++ 2).
(*  10 * (2 + 3)  *)
Compute compute (2 +++ 3).

Fixpoint optimisation (e : expression) : expression :=
  match e with
  | Nat i => Nat i
  | Sum (Nat 0) e2 => e2
  | Sum e1 e2 => Sum (optimisation e1) (optimisation e2)
  end.

(* (10 * 2) + 0 *)
Compute optimisation (10 +++ 5 +++ 0).

Theorem optimisation_sound :
  forall (e : expression),
  compute (optimisation e) = compute e.
Proof. intros. induction e as [|e1 IHe1 e2 IHe2].
(* e = Nat i1 *)
- simpl. reflexivity.
(* e = Sum e1 e2 *)
- destruct e1 as [i1|i1] eqn:He1.
  (* e1 = Nat i1*)
  + destruct i1 eqn:I1.
    (* i1 = 0 *)
    * reflexivity.
    (* i1 = S n *)
    * simpl. rewrite IHe2. reflexivity.
  (* e1 = Sum .. .. *)
  + simpl. simpl in IHe1.
    rewrite IHe1.
    rewrite IHe2. reflexivity.
Qed.






