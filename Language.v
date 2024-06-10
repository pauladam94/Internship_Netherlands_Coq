Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module Lang1.

(* Type Definition *)
Definition variable : Type := string.
Definition function : Type := string.
Inductive type : Type :=
  | Bool
  | Int
  | String.
  (* | Fun (args : list type) (return_type : type). *)

(* Value Definition *)
Inductive value : Type :=
  | UnitValue
  | BoolValue (b : bool)
  | IntValue (i : nat).

(* Syntax Definition *)
Inductive expression : Type :=
  | Sequence (e1 e2 : expression)
  | Let (x : string) (e1 e2 : expression)
  | FunctionCall (f : function) (args : list expression)
  | Var (x : variable)
  | Assign (x : variable) (e : expression)
  | Value (v : value).

(* Parsing The Grammar *)

(* Coercion AId : string >-> aexp. *)
(* Coercion ANum : nat >-> aexp. *)

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.


Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.

Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
(* Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity). *)
(* Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity). *)
(* Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity). *)
(* Notation "'true'"  := true (at level 1). *)
(* Notation "'true'"  := BTrue (in custom com at level 0). *)
(* Notation "'false'" := false (at level 1). *)
(* Notation "'false'" := BFalse (in custom com at level 0). *)
(* Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity). *)
(* Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity). *)
(* Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity). *)
(* Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity). *)
(* Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity). *)
(* Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity). *)
(* Notation "'skip'"  := *)
(*          CSkip (in custom com at level 0) : com_scope. *)


Notation "()" := (Value UnitValue)(in custom com at level 0) : com_scope.
Notation "'let' x = e1 ; e2"  :=
         (Let x e1 e2)
            (in custom com at level 0, x constr at level 0,
             e1 at level 85, no associativity) : com_scope.
Notation "x = y"  :=
         (Assign x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (Sequence x y)
           (in custom com at level 90,
            right associativity) : com_scope.
(* Notation "'if' x 'then' y 'else' z 'end'" := *)
(*          (CIf x y z) *)
(*            (in custom com at level 89, x at level 99, *)
(*             y at level 99, z at level 99) : com_scope. *)
(* Notation "'while' x 'do' y 'end'" := *)
(*          (CWhile x y) *)
(*            (in custom com at level 89, x at level 99, *)
(*             y at level 99) : com_scope. *)

(* Notation "e1 ';' e2" := (Sequence e1 e2)(at level 60). *)
(* Notation "'let' x = e1 ; e2" := (Let x e1 e2)(at level 70). *)
(* (* Notation "f ( e1 ... e2 ") *) *)
(* Notation "x '=' e" := (Assign x e). *)

Open Scope com_scope.

(* Test Syntax Notation *)
Lemma test1 : forall (e1 e2 : expression),
  <{ e1 ; e2 }> = Sequence e1 e2.
Proof. reflexivity. Qed.
Lemma test2 : forall (e : expression) (x : variable),
  <{ x = e }> = Assign x e.
Proof. reflexivity. Qed.
Lemma test3 : forall (e : expression) (x : variable),
  <{ x = e ; Var x }> = Sequence (Assign x e) (Var x).
Proof. reflexivity. Qed.
Lemma test4 : forall (e : expression) (x : variable), 
  <{ let x = e ;  x = e }> = Let x e (Assign x e). 
Proof. reflexivity. Qed.
Lemma test5 : forall (e : expression) (x : variable), 
  <{ x = e ; let x = e ; () }> = Sequence (Assign x e) (Let x e (Value UnitValue)). 
Proof. reflexivity. Qed.
Lemma test6 : forall (e : expression) (x : variable), 
  <{ x = e }> = Assign x e.
Proof. reflexivity. Qed.
Lemma test7 : forall (e1 e2 : expression) (x y : variable), 
  <{
    let x = e1 ;
    let y = e2 ;
    ()
  }> = Let x e1 (Let y e2 (Value UnitValue)).
Proof. reflexivity. Qed.

(* Typing Relation Definition *)
Definition typingEnv : Type := list (variable * type).
(* Reserved Notation "Gamma '|-' x ':' tau" (at level 100). *)

Inductive type_of : typingEnv -> variable -> type -> Prop :=
  | Env_Empty (x : variable) (tau : type) :
      type_of [(x, tau)] x tau
  | Env_Rec (gamma : typingEnv) (x y : variable) (taux tauy : type) :
      x <> y
      -> type_of ((y, tauy)::gamma) x taux
      -> type_of gamma x taux.
        (* where "gamma '|-' x ':' tau" := (typing gamma x tau) : type_scope. *)

Lemma test50 : forall (x : variable) (tau : type),
  (type_of [(x, tau)] x tau).
Proof. apply Env_Empty. Qed.

Import StringSyntax.
Import Ascii.
Search "eqb".
(* Search "String.eqb". *)

Inductive result (A E: Type) : Type :=
| Ok (x : A)
| Error (error : E).

Arguments Ok [A E].
Arguments Error [A E].

Inductive customError : Type :=
  | TypeError
  | ExecutionError
  | NonTerminatingFixpoint
  | Todo
  | VariableNotTypable.

Fixpoint typing_var_exec
  (gamma : typingEnv) (x : variable) : (result type customError) :=
    match gamma with
    | [] => Error VariableNotTypable
    | (y , tau)::gamma' =>
        if (String.eqb x y)
        then Ok tau
        else (typing_var_exec gamma' x)
  end.

Lemma test100 : forall (x : variable),
  typing_var_exec [] x = Error VariableNotTypable.
Proof. reflexivity. Qed.
Lemma test101 : forall (x y : variable),
  String.eqb x y = true ->
  typing_var_exec [(y, Int)] x = Ok Int.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma test102 : forall (x : variable),
  typing_var_exec [] x = Error VariableNotTypable.
Proof. reflexivity. Qed.

Fixpoint typing_expr_exec
  (n : nat) (gamma : typingEnv) (e : expression)
  : (result (type * typingEnv) customError) :=
  match n with
  | 0 => Error NonTerminatingFixpoint
  | S i =>
      match e with
      | Sequence e1 e2 =>
          match typing_expr_exec i gamma e1 with
          | Error err => Error err
          | Ok (tau1, gamma1) =>
              match typing_expr_exec i gamma1 e2 with
              | Error err => Error err
              | Ok (gamma2, tau2) => Error Todo
              end
          end
      | _ => Error Todo
      end
  end.

End Lang1.



