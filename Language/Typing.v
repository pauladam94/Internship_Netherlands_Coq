From Language Require Import Language.
From Language Require Import Parse.
From Language Require Import Error.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Require Import Integers.
Import ListNotations.

(****************************
   Relation Typing Expression
 *****************************)

Inductive type_expression : typingEnv -> expression -> type -> typingEnv 
  -> Prop :=
  | VarType (x : variable) (tau : type) :
    type_expression [(x, (None, tau))] (Var x) tau [(x, (None, tau))]
  | Env_Rec (gamma : typingEnv) (x y : variable) (taux tauy : type) :
      x <> y
      -> type_expression ((y, (None, tauy))::gamma) (Var x) taux
        ((y, (None, tauy))::gamma)
      -> type_expression gamma (Var x) taux gamma.
Example example100 : forall (x : variable) (tau : type),
  type_expression [(x, (None, tau))] (Var x) tau [(x, (None, tau))].
Proof. apply VarType. Qed.

(***************************
  Function Typing Variable
***************************)
Fixpoint type_var_exec
  (gamma : typingEnv) (x : variable) : (result (type * typingEnv)) :=
    match gamma with
    | [] => Error ("Variable " ++ x ++ " Not Typable")
    | (y , (_, tau))::gamma' =>
        if (String.eqb x y)
        then
          match tau with
          | UnitT | BoolT | IntT => Ok (tau, gamma)
          | StringT => Ok (tau, (y, (NotAccessible, tau))::gamma')
          end
        else (type_var_exec gamma' x)
  end.

Module TypingVarExample.
Compute type_var_exec [] "x".
(* Example example150 : forall (x : variable), *)
(*   type_var_exec [] x = Error "Variable NotTypable". *)
(* Proof. reflexivity. Qed. *)
(* Example example151 : forall (x y : variable), *)
(*   Nat.eqb x y = true -> *)
(*   type_var_exec [(y, (None, IntT))] x = Ok (IntT, [(y, (None, IntT))]). *)
(* Proof. intros. simpl. rewrite H. reflexivity. Qed. *)
(* Example example152 : forall (x : variable), *)
(*   type_var_exec [] x = Error VariableNotTypable. *)
(* Proof. reflexivity. Qed. *)
End TypingVarExample.

(*****************************
  Function Typing Expression
*****************************)
Fixpoint type_expression_exec
  (n : nat) (gamma : typingEnv) (e : expression)
  : result (type * typingEnv) :=
  match n with
  | 0 => Error "NonTerminatingFunction"
  | S i =>
  match e with
  | Sequence e1 e2 =>
    let+ (tau1, gamma1) = type_expression_exec i gamma e1;
    let+ (tau2, gamma2) = type_expression_exec i gamma1 e2;
    if (type_eqb tau1 UnitT)
    then Ok (tau2, gamma2)
    else Error ("Type expected 'unit' but got" ++ (type_to_string tau1))
  | Let x e1 e2 =>
      match type_expression_exec i gamma e1 with
      | Ok (tau1, gamma1) =>
          type_expression_exec i ((x, (None, tau1))::gamma1) e2
      | err => err
      end
  | Var x =>
    match type_var_exec gamma x with
    | Error err => Error err
    | Ok (tau, gamma') => Ok (tau, gamma') 
        (* TODO get different gamma borrow checking *)
    end
  | Value v => Ok (value_to_type v, gamma)
  | Assign x e =>
    match type_expression_exec i gamma e with
    | Error err => Error err
    | Ok (tau, gamma') => Error "Todo"
    end
  | _ => Error "Todo"
  end
  end.

Example example200 : forall (x : variable),
  type_expression_exec BigNat [] (Value (IntV 4128)) = Ok (IntT, []).
  (* 4128 : int *)
Proof. intros. reflexivity. Qed.
Example example201 : forall (x : variable),
  type_expression_exec BigNat []
  (Let x (Value (IntV 4128)) (Var x))
  (* let x = 4128; x : int *)
    = Ok (IntT, [(x, (None, IntT))]).
Proof. intros. simpl. Search "eqb_refl". rewrite String.eqb_refl. reflexivity. Qed.
Example example202 : forall (x : variable) (s : nat),
  type_expression_exec BigNat [] 
  (Let x (Value (StringV s)) (Var x))
  (* let x = s; x *)
    = Ok (StringT, [(x, (NotAccessible, StringT))]).
Proof. intros. simpl. rewrite String.eqb_refl. reflexivity. Qed.

Compute type_expression_exec BigNat [] 
  (Let "x" (Value (StringV 1)) (Var "x")).

