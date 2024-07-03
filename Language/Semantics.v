From Language Require Import Language.
From Language Require Import Parse.
From Language Require Import Error.
From Language Require Import Utils.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import Coq.Lists.List.
Require Import Integers.
Import ListNotations.

(* Memory Model Definition *)
Inductive semaphore : Type :=
  | Writing
  | Reading (n : nat).
Definition block : Type := nat.
Definition offset : Type := nat.
Inductive state : Type :=
  | Wait
  | Pos (b : block) (off : offset).
Inductive refinement_variable : Type :=
  | Owner
  | Borrower.
Inductive memory_value : Type :=
  | Poison
  | Integer (i : nat)
  | Ptr (b : block) (off : offset).
Definition memory : Type := list (block * list memory_value).
Definition symbol_table : Type := list (variable * state).
Definition execution_stack : Type := list (symbol_table * expression).
Definition execution_state : Type := (memory * execution_stack).

(****************
 Pretty Printing
 ****************)

Definition state_to_string (st : state) : string :=
  match st with
  | Wait => "Wait"
  | Pos b off => "(" ++ nat_to_string b ++ "," ++ nat_to_string off ++ ")"
  end.

Fixpoint memory_value_to_string (mv : memory_value) : string :=
  match mv with
  | Poison => "Poison"
  | Integer i => nat_to_string i
  | Ptr b off => "ptr (" ++ nat_to_string b ++ "," ++ nat_to_string off ++ ")"
  end.

Fixpoint memory_value_list_to_string (l : list memory_value) : string :=
  match l with
  | [] => ""
  | [h] => memory_value_to_string h
  | h::q => memory_value_to_string h ++ " | " ++ memory_value_list_to_string q
  end.

Fixpoint memory_to_string_helper (mem : memory) : string :=
  match mem with
  | [] => ""
  | (b, l)::q => "block " ++ nat_to_string b ++ new_line
      ++ memory_value_list_to_string l
      ++ memory_to_string_helper q
  end.

Definition memory_to_string (mem : memory) : string :=
  memory_to_string_helper mem.

Fixpoint execution_stack_to_string (exe_stack : execution_stack) : string :=
  match exe_stack with
  | [] => ""
  | (env, e)::q => expression_to_string e ++ new_line 
      ++ execution_stack_to_string q
  end.

Fixpoint execution_state_to_string (exe_state : execution_state) : string :=
  let (mem, exe_stack) := exe_state in
  "memory :" ++ new_line ++
  (memory_to_string mem) ++ new_line ++
  "execution stack:" ++ new_line ++
  (execution_stack_to_string exe_stack)
  .



Fixpoint wait_env (b : block) (env : symbol_table)
  : result symbol_table :=
  match env with
  | [] => Ok []
  | (x, st)::env' =>
      match st with
      | Wait =>
          Ok ((x, Pos b 0)::env')
      | Pos b off =>
          let+ env'' = wait_env b env';
            Ok ((x, st)::env'')
      end
  end.

Definition replace_next_wait (b : block) (ex_stack : execution_stack)
  : result execution_stack :=
match ex_stack with
| [] => Error "Nothing to replace, no more env"
| (env, e) :: ex_stack' =>
    let+ new_env = wait_env b env;
      Ok ((new_env, e) ::ex_stack')
        (* let+ new_stack = replace_next_wait ex_stack'; *)
        (* Ok ((env_stack, st) :: new_stack) *)
end.

Fixpoint get_block (x : variable) (env : symbol_table) : result block :=
  match env with
  | [] => Error ("Variable" ++ x ++ "Not found")
  | (y, st)::env' =>
      match st with
      | Wait => get_block x env'
      | Pos b off => if String.eqb x y then Ok b else get_block x env'
      end
  end.

Definition allocate (v: value) (mem : memory) : (memory * block) :=
  let b := List.length mem in
  match v with
  | IntV i => ((b, [Integer i])::mem, b)
  | PoisonV => ((b, [Poison])::mem, b)
  end.

(********************************
  Function Operational Semantics
*********************************)
Fixpoint semantics_expression_exec (step : nat) (ex_state : execution_state) 
  : result execution_state :=
  match step with
  | 0 => Error ("Too much step taken" ++ new_line 
      ++ execution_state_to_string ex_state)
  | S n =>
  let (mem, ex_stack) := ex_state in

  match ex_stack with
  | [] => Error "Todo empty stack"
  | (env, e)::ex_stack' =>
    match e with
    | Let x e1 e2 =>
      let new_ex_state := (mem,
        [(env, e1)] ++ [((x, Wait)::env, e2)] ++ ex_stack') in
      semantics_expression_exec n new_ex_state
    | FunctionCall f args => Error "Todo"
    | Assign x e => Error "Todo"
    | Var x =>
      let+ b = get_block x env;
      let+ new_ex_stack = replace_next_wait b ex_stack;
      Error "Todo"
    | Value v =>
      let (mem, b) := allocate v mem in
      let++ new_ex_stack = replace_next_wait b ex_stack'
        with "Error Replace Wait";
      semantics_expression_exec n (mem, new_ex_stack)
    | Product l => Error "Todo product"
    | Sequence e1 e2 => semantics_expression_exec n
                   (mem,
                   [(env, e1)] ++
                   [(env, e2)] ++ ex_stack')
    end
  end

  end.

Definition executeTest (code : string) : result value :=
  let++ ast = parse code with "Error in Parsing :";
  let default_state := ([], [([], ast)]) in 
  let++ exec_state = semantics_expression_exec BigNat default_state
  with "Error During Execution:";
  Error "Todo"
.


Module SemanticsTest.

Compute executeTest "let a = 4; 5".
End SemanticsTest.













(* Example example250 : forall (x : variable), *)
  (* semantics_expression_exec BigNat []. *)

(*********************************
   Relation Operational Semantics
**********************************)
Inductive semantics_expression : execution_state -> execution_state -> Prop :=
  | VarSem (ex1 ex2 : execution_state) : semantics_expression ex1 ex2.

Module SemanticsRelationTest.
(* Example example50 : forall (x : variable) (tau : type), *)
  (* (type_expression [(x, (None, tau))] x tau). *)
(* Proof. apply Env_Empty. Qed. *)
End SemanticsRelationTest.
