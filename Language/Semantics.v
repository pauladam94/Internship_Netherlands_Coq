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
(* Inductive memory_value : Type := *)
(*   | Poison *)
(*   | Integer (i : nat) *)
(*   | Ptr (b : block) (off : offset). *)
(* Todo block * semaphore * value *)
Definition memory : Type := list (block * list value).
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

Fixpoint symbol_table_to_string (env : symbol_table) : string :=
  match env with
  | [] => ""
  | [(x, st)] => x ++ state_to_string st
  | (x, st)::env => x ++ state_to_string st ++ "|" ++ symbol_table_to_string env
  end.

(* Definition memory_value_to_string (mv : memory_value) : string := *)
(*   match mv with *)
(*   | Poison => "Poison" *)
(*   | Integer i => nat_to_string i *)
(*   | Ptr b off => "ptr (" ++ nat_to_string b ++ "," ++ nat_to_string off ++ ")" *)
(*   end. *)

Fixpoint value_list_to_string (l : list value) : string :=
  match l with
  | [] => ""
  | [h] => value_to_string h
  | h::q => value_to_string h ++ " , " ++ value_list_to_string q
  end.

Fixpoint memory_to_string_helper (mem : memory) : string :=
  match mem with
  | [] => ""
  | (b, l)::q => "block " ++ nat_to_string b
      ++ ": [" ++ value_list_to_string l ++ "]" ++ nl
      ++ memory_to_string_helper q
  end.

Definition memory_to_string (mem : memory) : string :=
  memory_to_string_helper mem.

Fixpoint execution_stack_to_string (exe_stack : execution_stack) : string :=
  match exe_stack with
  | [] => ""
  | (env, e)::q => expression_to_string e ++ nl 
      ++ execution_stack_to_string q
  end.

Definition execution_state_to_string (exe_state : execution_state) : string :=
  let (mem, exe_stack) := exe_state in
  "memory :" ++ nl ++
  (memory_to_string mem) ++ nl ++
  "execution stack:" ++ nl ++
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
| [] => Ok []
| (env, e) :: ex_stack' =>
    let+ new_env = wait_env b env;
      Ok ((new_env, e) ::ex_stack')
end.

Fixpoint get_block (x : variable) (env : symbol_table) : result block :=
  match env with
  | [] => Error ("Variable " ++ x ++ " not found")
  | (y, st)::env' =>
      match st with
      | Wait => get_block x env'
      | Pos b off => if String.eqb x y then Ok b else get_block x env'
      end
  end.

Fixpoint get_block_offset (x : variable) (env : symbol_table)
  : result (block * offset) :=
  match env with
  | [] => Error ("Variable " ++ x ++ " not found")
  | (y, st)::env' =>
      match st with
      | Wait => get_block_offset x env'
      | Pos b off => if String.eqb x y
                     then Ok (b, off)
                     else get_block_offset x env'
      end
  end.

(* minimal_integer_not_present *)
Fixpoint max (l : list nat) : nat :=
  match l with
  | [] => 0
  | h::q =>
    let max_q := max q in if Nat.leb max_q h then h else max_q
  end.

Definition allocate (v: value) (mem : memory) : (memory * block) :=
  let b := max
    (map (fun (x : (block * list value)) => let (b, _):= x in b) mem) + 1 in
  match v with
  | Poison => ((b, [Poison])::mem, b)
  | Integer i => ((b, [Integer i])::mem, b)
  | Ptr b0 off => ((b, [Ptr b0 off])::mem, b)
  end.

Fixpoint get_state (x : variable) (env : symbol_table) : result state :=
  match env with
  | [] => Error ("Variable " ++ x ++ " not found in " 
      ++ symbol_table_to_string env)
  | (y, st)::env => if x =? y then Ok st else get_state x env
  end.

Fixpoint get_list_value (off : offset) (l : list value) : result value :=
  match off, l with
  | _, [] => Error "Out of bounds, offset too big for list"
  | 0, h::q => Ok h
  | S n, h::q => get_list_value n q
  end.

Fixpoint get_value (b : block) (off : offset) (mem : memory) : result value :=
  match mem with
  | [] => Error ("Nothing Found in Memory at position" ++ value_to_string (Ptr b off))
  | (b0, l)::mem =>
    if Nat.eqb b b0
    then get_list_value off l
    else get_value b off mem
  end.

Fixpoint change_list_value (off : offset) (v : value) (l : list value)
  : result (list value) :=
  match off, l with
  | _, [] => Error "Out of bounds, offset too big for list"
  | 0, h::q => Ok (v::q)
  | S n, h::q =>
    let+ new_list = change_list_value n v q;
      Ok (h::new_list)
  end.

Fixpoint change_memory (b  : block) (off : offset) (v : value) (m : memory)
  : result memory :=
  match m with
  | [] => Error "Todo"
  | (b0, l)::m0 =>
    if Nat.eqb b b0 then
      let++ l = change_list_value off v l
        with "Error changing the block " ++ nat_to_string b ++ "";
      Ok ((b0, l)::m0)
    else
      let+ new_memory = change_memory b off v m0;
      Ok ((b0, l)::new_memory)
  end.

(********************************
  Function Operational Semantics
*********************************)
Fixpoint semantics_expression_exec (step : nat) (ex_state : execution_state) 
  : result execution_state :=
  match step with
  | 0 => Error ("Too much step taken" ++ nl
      ++ execution_state_to_string ex_state)
  | S n =>
  let (mem, ex_stack) := ex_state in

  match ex_stack with
  | [] => Error "Execution stack should never be empty"
  | [(env, Value v)] => Ok (mem, [(env, Value v)])
  | (env, e)::ex_stack =>
    match e with
    | Let x e1 e2 =>
      let new_ex_state := (mem,
        [(env, e1)] ++ [((x, Wait)::env, e2)] ++ ex_stack) in
      semantics_expression_exec n new_ex_state

    | FunctionCall f args => Error "Todo Func Call"

    | Assign x y =>
      let++ (b_x, off_x) = get_block_offset x env
        with "Error getting block and offset Variable" ++ nl ++
          "In memory :" ++ nl ++ memory_to_string mem ++ nl ++
          "In env :" ++ nl ++ symbol_table_to_string env ++ nl ++
          "In expression :" ++ nl ++ expression_to_string e;

      let state_y := get_state y env in
      let++ (b_y, off_y) = get_block_offset y env
        with "Error getting block and offset Variable" ++ nl ++
          "In memory :" ++ nl ++ memory_to_string mem ++ nl ++
          "In env :" ++ nl ++ symbol_table_to_string env ++ nl ++
          "In expression :" ++ nl ++ expression_to_string e ;

      let++ v_y = get_value b_y 0 mem
        with "Error getting value for" ++ y ++
        "In memory :" ++ nl ++ memory_to_string mem;

      let+ mem = change_memory b_x off_x v_y mem;
      semantics_expression_exec n (mem, (env, Value Poison)::ex_stack)

    | Var x =>
      let++ (b, off) = get_block_offset x env
        with "Error getting block and offset Variable" ++ nl ++
          "In memory :" ++ nl ++ memory_to_string mem ++
          "In env :" ++ nl ++ symbol_table_to_string env ++ nl ++
          "In expression :" ++ nl ++ expression_to_string e;
      let++ v = get_value b 0 mem
        with "Error getting value for" ++ x ++
          "In memory :" ++ nl ++ memory_to_string mem;

      let+ new_ex_stack = replace_next_wait b ex_stack;
        (* Todo change env so that has been read *)
      semantics_expression_exec n (mem, (env, Value (Ptr b off))::ex_stack)

    | Value v =>
        let (mem, b) := allocate v mem in (* TODO Every time allocate ? *)
      let++ new_ex_stack = replace_next_wait b ex_stack
        with "Error Replace Wait:";
      semantics_expression_exec n (mem, new_ex_stack)

    | Product l =>
        (* let a = map ( *)
        (*   fun x => l  *)
        (* ) l  in *)
        Error "Todo Product"

    | Sequence e1 e2 => semantics_expression_exec n
                   (mem,
                   [(env, e1)] ++
                   [(env, e2)] ++ ex_stack)
    | Borrow x => Error "Todo borrow"
    | Deref x =>
      let++ (bx, offx) = get_block_offset x env
        with "Error getting block and offset Variable" ++ nl ++
        "In memory :" ++ nl ++ memory_to_string mem ++ nl ++
        "In env :" ++ nl ++ symbol_table_to_string env ++ nl ++
        "In expression :" ++ nl ++ expression_to_string e;

      let+ v_x = get_value bx offx mem; (* should no fail *)
        match v_x with
        | Poison => Error "Poison cannot be dereferenced"
        | Integer i => Error ("Integer " ++ nat_to_string i ++
          " cannot be dereferenced" ++ nl ++
          "In memory :" ++ nl ++ memory_to_string mem ++ nl ++
          "In env :" ++ nl ++ symbol_table_to_string env)

        | Ptr b off =>
          let+ v_deref_x = get_value b off mem;
          semantics_expression_exec n (mem, (env, Value v_deref_x)::ex_stack)

        end
    end
  end

  end.

Definition executeTest (code : string) : result value :=
  let++ ast = parse code with "Error in Parsing :";
  let default_state := ([], [([], ast)]) in
  let++ exec_state = semantics_expression_exec BigNat default_state
  with "Error During Execution:";
  match exec_state with
  | (_,  [(_, Value v)]) => Ok v
  | _ => Error ("Execution not finished" ++ nl ++
           "With this execution state :" ++ nl ++
             execution_state_to_string exec_state)
  end.

Compute parse "let a = 4; a = 12; let y = a; *y".

Module SemanticsTest.
Compute executeTest "4".
Compute executeTest "x = 3".
Compute executeTest "let a = 4; 5".
Compute executeTest "let a = 4; let y = a; y".
Compute executeTest "let a = 4; a = 12; let y = a; y".
Compute executeTest "let a = 4; a = 12; let y = a; *y".
Compute executeTest "let a = 4; a = 12; let y = a; y = 32; *y".
Compute executeTest "let a = 4; a = 12; let y = a; y = 32; y = 42; *y".
Compute executeTest "let a = 4; let y = a; *y".
Compute executeTest "let a = 4; let y = a; x".
Compute executeTest "let a = 4; x = 12; x".
Compute executeTest "let a = 4; a = 12; a".
Compute executeTest "let a = 4; a = 12; *a".
Compute executeTest "let a = {4}; a = 12; *a".
Compute executeTest "let a = 4; a = 12; *a".
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
