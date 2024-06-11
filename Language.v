Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Import StringSyntax.
Import Ascii.

Module Lang1.

(* Type Definition *)
Definition variable : Type := string.
Definition function : Type := string.
Inductive type : Type :=
  | Unit
  | Bool
  | Int
  | String.
  (* | Fun (args : list type) (return_type : type). *)

Definition eqb (tau1 tau2 : type) : bool :=
  match (tau1, tau2) with
    | (Bool, Bool) | (Int, Int) | (String, String) => true
    | _ => false
  end.
Notation "tau1 =? tau2" := (eqb tau1 tau2).

(* Value Definition *)
Inductive value : Type :=
  | UnitValue
  | BoolValue (b : bool)
  | IntValue (i : nat)
  | StringValue (s : string).

Definition value_to_type (v : value) : type :=
  match v with
  | UnitValue => Unit
  | BoolValue _ => Bool
  | IntValue _ => Int
  | StringValue _ => String
  end.

(* Syntax Definition *)
Inductive expression : Type :=
  | Sequence (e1 e2 : expression)
  | Let (x : string) (e1 e2 : expression)
  | FunctionCall (f : function) (args : list expression)
  | Var (x : variable)
  | Assign (x : variable) (e : expression)
  | Value (v : value).

(* Parsing The Grammar *)
Coercion IntValue : nat >-> value.
Coercion StringValue : string >-> value.
Coercion Value : value >-> expression.

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y " := (.. (f x) .. y)
  (in custom com at level 0, only parsing,
  f constr at level 0, 
  x constr at level 10, (* level of x and y should be the same *)
  y constr at level 10) : com_scope.
Notation "()" := (Value UnitValue)(in custom com at level 0) : com_scope.
Notation "'let' x = e1 ; e2"  :=
  (Let x e1 e2)
  (in custom com at level 0,
  x constr at level 0,
  e1 constr at level 0,
  e2 at level 90,
  right associativity) : com_scope.
Notation "x = y"  :=
  (Assign x y)
  (in custom com at level 0,
  x constr at level 0,
  y at level 70,
  no associativity) : com_scope.
Notation "x ; y" :=
  (Sequence x y)
  (in custom com at level 80,
  right associativity) : com_scope.

Open Scope com_scope.

(* Test Syntax Notation *) (* Unset Printing Notations *)
Lemma test1 : forall (e1 e2 : expression), <{ e1 ; e2 }> = Sequence e1 e2.
Proof. reflexivity. Qed.
Lemma test2 : forall (e : expression) (x : variable), <{ x = e }> = Assign x e.
Proof. reflexivity. Qed.
Lemma test3 : forall (e : expression) (x : variable),
  <{ x = e ; Var x }> = Sequence (Assign x e) (Var x).
Proof. reflexivity. Qed.
Lemma test4 : forall (e : expression) (x : variable),
  <{ let x = e ;  x = e }> = Let x e (Assign x e).
Proof. reflexivity. Qed.
Lemma test5 : forall (e : expression) (x : variable),
  <{ x = e ; let x = e ; () }> 
    = Sequence (Assign x e) (Let x e (Value UnitValue)).
Proof. reflexivity. Qed.
Lemma test6 : forall (e : expression) (x : variable), 
  <{ x = e }> = Assign x e.
Proof. reflexivity. Qed.
Lemma test7 : forall (e1 e2 : expression) (x y : variable), 
  <{ let x = e1 ; let y = e2 ; () }> 
  = Let x e1 (Let y e2 (Value UnitValue)).
Proof. reflexivity. Qed.
Lemma test8 : forall (x : variable) (e : expression),
  <{ let x = 4 ; e }> = Let x 4 e.
Proof. reflexivity. Qed.
Lemma test9 : forall (e1 e2 e3 : expression),
  <{ e1; e2; e3 }> = Sequence e1 (Sequence e2 e3).
Proof. reflexivity. Qed.
Lemma test10 : forall (x y z : variable),
  <{let x = 2; let y = 3; let z = 4; ()}> = Let x 2 (Let y 3 (Let z 4 <{()}>)).
Proof. reflexivity. Qed.
Lemma test11 : forall (x y : variable) (e : expression),
  <{ x = 8; x ; let y = 4 ; x }> 
    = Sequence (Assign x 8) (Sequence x (Let y 4 x)).
Proof. reflexivity. Qed.
Lemma test12 : forall (x : variable) (e : expression),
  <{ let x = 4; x = 8; e }> = Let x 4 (Sequence (Assign x 8) e).
Proof. reflexivity. Qed.

(* Typing Relation Definition *)
Inductive refinement : Type := 
  | None
  | NotAccessible.
Definition refined_type : Type := refinement * type.
Definition typingEnv : Type := list (variable * refined_type).
(* Reserved Notation "Gamma '|-' x ':' tau" (at level 100). *)

Inductive type_expression : typingEnv -> variable -> type -> Prop :=
  | Env_Empty (x : variable) (tau : type) :
      type_expression [(x, (None, tau))] x tau
  | Env_Rec (gamma : typingEnv) (x y : variable) (taux tauy : type) :
      x <> y
      -> type_expression ((y, (None, tauy))::gamma) x taux
      -> type_expression gamma x taux.
(* where "gamma '|-' x ':' tau" := (typing gamma x tau) : type_scope. *)

Lemma test50 : forall (x : variable) (tau : type),
  (type_expression [(x, (None, tau))] x tau).
Proof. apply Env_Empty. Qed.

Inductive result (A E: Type) : Type :=
| Ok (x : A)
| Error (error : E).

Arguments Ok [A E].
Arguments Error [A E].

Inductive customError : Type :=
  | ExecutionError
  | NonTerminatingFunction
  | Todo
  | VariableNotTypable
  | TypeError (expected given : type).


(* Function Typing Variable *)
Fixpoint typing_var_exec
  (gamma : typingEnv) (x : variable) : (result (type * typingEnv) customError) :=
    match gamma with
    | [] => Error VariableNotTypable
    | (y , (_, tau))::gamma' =>
        if (String.eqb x y)
        then
          match tau with
          | Unit | Bool | Int => Ok (tau, gamma)
          | String => Ok (tau, (y, (NotAccessible, tau))::gamma')
          end
        else (typing_var_exec gamma' x)
  end.

Lemma test100 : forall (x : variable),
  typing_var_exec [] x = Error VariableNotTypable.
Proof. reflexivity. Qed.
Lemma test101 : forall (x y : variable),
  String.eqb x y = true ->
  typing_var_exec [(y, (None, Int))] x = Ok (Int, [(y, (None, Int))]).
Proof. intros. simpl. rewrite H. reflexivity. Qed.
Lemma test102 : forall (x : variable),
  typing_var_exec [] x = Error VariableNotTypable.
Proof. reflexivity. Qed.

(* Function Typing Expression *)
Fixpoint typing_expression_exec
  (n : nat) (gamma : typingEnv) (e : expression)
  : (result (type * typingEnv) customError) :=
  match n with
  | 0 => Error NonTerminatingFunction
  | S i =>
  match e with
  | <{ e1 ; e2 }> =>
      match typing_expression_exec i gamma e1 with
      | Error err => Error err
      | Ok (tau1, gamma1) =>
          match typing_expression_exec i gamma1 e2 with
          | Error err => Error err
          | Ok (tau2, gamma2) =>
              if (tau1 =? Unit)
              then Ok (tau2, gamma2)
              else Error (TypeError Unit tau1)
          end
      end
  | <{ let x = e1 ; e2 }> =>
      match typing_expression_exec i gamma e1 with
      | Ok (tau1, gamma1) =>
          typing_expression_exec i ((x, (None, tau1))::gamma1) e2
      | err => err
      end
  | Var x =>
    match typing_var_exec gamma x with
    | Error err => Error err
    | Ok (tau, gamma') => Ok (tau, gamma') (* TODO get different gamma borrow checking *)
    end
  | Value v => Ok (value_to_type v, gamma)
  | <{ x = e }> =>
    match typing_expression_exec i gamma e with
    | Error err => Error err
    | Ok (tau, gamma') => Error Todo
    end
  | _ => Error Todo
  end
  end.

(* BigInt use for making sure function terminates *)
Definition BigNat := 10000.
(* Check BigNat. *)

Lemma test150 : forall (x : variable),
  typing_expression_exec BigNat [] <{ 4128 }> = Ok (Int, []).
Proof. intros. simpl. reflexivity. Qed.
Lemma test151 : forall (x : variable),
  typing_expression_exec BigNat [] <{ let x = 4128 ; Var x }>
    = Ok (Int, [(x, (None, Int))]).
Proof. intros. simpl. rewrite String.eqb_refl. reflexivity. Qed.
Lemma test152 : forall (x : variable) (s : string),
  typing_expression_exec BigNat [] <{ let x = s ; Var x }> 
    = Ok (String, [(x, (NotAccessible, String))]).
Proof. intros. simpl. rewrite String.eqb_refl. reflexivity. Qed.

Fixpoint semantics_exec 
  (n : nat) (e : expression) : result value customError :=
  match n with
  | 0 => Error NonTerminatingFunction
  | S i => 
  match e with
  | _ => Error Todo
  end
  end
.


End Lang1.
