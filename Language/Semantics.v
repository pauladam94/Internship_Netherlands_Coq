Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Require Import Integers.
Import ListNotations.
From Language Require Import Utils.
From Language Require Import Error.
From Language Require Import Language.
From Language Require Import Expression.
From Language Require Import ParseExpression.
From Language Require Import Program.
From Language Require Import ParseProgram.

(* Memory Model Definition *)
Inductive semaphore : Type :=
  | Dropped (* TODO Delete completely that in favor of delete in the memory *)
  | Writing
  | Reading (n : nat).
Definition block : Type := nat.
Definition offset : Type := nat.
Inductive variable_state : Type :=
  | Wait
  | Block (b : block).
Inductive refinement_variable : Type :=
  | Owner
  | Borrower.

Inductive execution_order : Type :=
  | VariableOutOfScope (v : variable)
  | Expression (e : expression).

Definition memory : Type := list (block * semaphore * list value).
Definition symbol_table : Type := list (variable * variable_state).
Definition execution_stack : Type := list (symbol_table * execution_order).
Definition execution_state : Type := (memory * execution_stack).

Definition execution_order_to_string (exe_order : execution_order)
  : string :=
  match exe_order with
  | VariableOutOfScope x => "Variable Out of Scope" ++ x
  | Expression e => expression_to_string e
  end.

(****************
 Pretty Printing
 ****************)

Definition semaphore_to_string (s : semaphore) : string :=
  match s with
  | Dropped => "Dropped"
  | Writing => "W"
  | Reading n => "R" ++ nat_to_string n
  end.
Definition variable_state_to_string (st : variable_state) : string :=
  match st with
  | Wait => "Wait"
  | Block b => "B:" ++ nat_to_string b
  end.

Fixpoint symbol_table_to_string_helper (env : symbol_table) : string :=
  match env with
  | [] => ""
  | [(x, st)] => "{" ++ x ++ ", " ++ 
    variable_state_to_string st ++ "}"
  | (x, st)::env => "{" ++ x ++ ", " ++ variable_state_to_string st ++ "}" ++
      ", " ++ symbol_table_to_string_helper env
  end.

Definition symbol_table_to_string (env : symbol_table) : string :=
  "[" ++ symbol_table_to_string_helper env ++ "]".

Fixpoint value_list_to_string (l : list value) : string :=
  match l with
  | [] => ""
  | [h] => value_to_string h
  | h::q => value_to_string h ++ " , " ++ value_list_to_string q
  end.

Fixpoint memory_to_string (mem : memory) : string :=
  match mem with
  | [] => ""
  (* | [(b, s , l)] => "Block " ++ nat_to_string b ++ " " ++ semaphore_to_string s *)
  (*     ++ ": [" ++ value_list_to_string l ++ "]" ++ nl *)
  | (b, s , l)::q => "Block " ++ nat_to_string b ++ " " ++ semaphore_to_string s
      ++ ": [" ++ value_list_to_string l ++ "]" ++ nl
      ++ memory_to_string q
  end.

(*****************
  Execution Stack
******************)

Fixpoint execution_stack_only_var_out_of_scope (exe_stack : execution_stack)
  : bool :=
  match exe_stack with
  | [] => true
  | (_, VariableOutOfScope x)::q => execution_stack_only_var_out_of_scope q
  | (_, Expression e)::q => false
  end.

Fixpoint execution_stack_to_string (exe_stack : execution_stack) : string :=
  match exe_stack with
  | [] => ""
  | (env, Expression e)::q => symbol_table_to_string env
      ++ expression_to_string e ++ nl
      ++ execution_stack_to_string q
  | (env, VariableOutOfScope v)::q => "(" ++ symbol_table_to_string env
      ++ ", OutOfScope " ++ v ++ ")" ++ nl
      ++ execution_stack_to_string q
  end.

Definition execution_state_to_string (exe_state : execution_state) : string :=
  let (mem, exe_stack) := exe_state in
  "memory: " ++ nl ++
  (memory_to_string mem) ++
  "execution stack:" ++ nl ++
  (execution_stack_to_string exe_stack).

Fixpoint wait_env (b : block) (env : symbol_table)
  : result (symbol_table * bool) :=
  match env with
  | [] => Ok ([], false)
  | (x, st)::env =>
      match st with
      | Wait =>
          Ok ((x, Block b)::env, true)
      | Block b =>
          let+ (env, done) = wait_env b env;
          Ok ((x, st)::env, done)
      end
  end.

Fixpoint replace_n_next_wait (n : nat) (b : block)
  (exe_stack : execution_stack) : result execution_stack :=
  match (n, exe_stack) with
  | (0, _) => Ok exe_stack
  | (S n, []) => Error ("No Enough Wait to Change")
  | (S n, (env, e) :: exe_stack) =>
    let+ (env, done) = wait_env b env;
    if done then
      let+ exe_stack = replace_n_next_wait n b exe_stack;
      Ok ((env, e) :: exe_stack)
    else
      let+ exe_stack = replace_n_next_wait (S n) b exe_stack;
      Ok ((env, e) :: exe_stack)
  end.

Definition replace_2_next_wait (b : block) (exe_stack : execution_stack)
  : result execution_stack :=
  replace_n_next_wait 2 b exe_stack.

Fixpoint get_block (x : variable) (env : symbol_table)
  : result block :=
  match env with
  | [] => Error ("Error getting Block Offset, " ++ x ++
      " not found")
  | (y, st)::env' =>
      match st with
      | Wait => get_block x env'
      | Block b => if String.eqb x y then Ok b else get_block x env'
      end
  end.

(* minimal_integer_not_present *)
Fixpoint max (l : list nat) : nat :=
  match l with
  | [] => 0
  | h::q =>
    let max_q := max q in if Nat.leb max_q h then h else max_q
  end.

Definition allocate (l_v : list value) (mem : memory) : (memory * block) :=
  let b := max
    (map (
      fun (x : (block * semaphore * list value)) =>
        let (bs, _) := x in
        let (b, x) := bs in b
    ) mem) + 1 in
  (((b, Reading 0), l_v)::mem, b).

Fixpoint get_variable_state (x : variable) (env : symbol_table) : result variable_state :=
  match env with
  | [] => Error ("Get Variable State" ++ nl ++ x ++ " not found")
  | (y, st)::env => if x =? y then Ok st else get_variable_state x env
  end.

Fixpoint get_list_value (off : offset) (l : list value) : result value :=
  match off, l with
  | _, [] => Error "Out of bounds, offset too big for list"
  | 0, h::q => Ok h
  | S n, h::q => get_list_value n q
  end.

Fixpoint get_value (b : block) (off : offset) (mem : memory) : result value :=
  match mem with
  | [] => Error ("Nothing Found in Memory at position" ++ 
      value_to_string (Ptr b off))
  | ((b0, _), l)::mem =>
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
  | [] => Error "Memory is empty : cannot change"
  | ((b0, s), l)::m0 =>
    if Nat.eqb b b0 then
      let++ l = change_list_value off v l
        error "Error changing the block " ++ nat_to_string b ++ "";
      Ok (((b0,s), l)::m0)
    else
      let+ new_memory = change_memory b off v m0;
      Ok (((b0, s), l)::new_memory)
  end.

Fixpoint drop_memory (b : block) (m : memory) : result memory :=
  match m with
  | [] => Error ("Drop Memory" ++ nl ++ "Memory is empty")
  | ((b0, s), l)::m0 =>
    if Nat.eqb b b0 then
      Ok (((b0,Dropped), l)::m0)
    else
      let+ new_memory = drop_memory b m0;
      Ok (((b0, s), l)::new_memory)
  end.

Definition debug_print (mem : memory) (env : symbol_table) (e : expression)
  : string :=
  "In memory:" ++ nl ++ memory_to_string mem ++
  "In env:" ++ nl ++ symbol_table_to_string env ++ nl ++
  "In expression:" ++ nl ++ expression_to_string e ++ nl.

Fixpoint variable_list_to_value_list (l_v : list variable) (mem : memory)
  (env : symbol_table) : result (list value) :=
  match l_v with
  | [] => Ok []
  | x::l_v =>
    let+ l_x = variable_list_to_value_list l_v mem env;
    let+ b_x = get_block x env;
    let+ v_x = get_value b_x 0 mem;
     Ok (v_x::l_x)
  end.

Fixpoint args_definition_function_call (args : list variable)
  (l_v : list variable) : result (expression -> expression) :=
  match args, l_v with
  | [], [] => Ok (fun e => e)
  | x1::args, x2::l_v =>
    let+ e = args_definition_function_call args l_v;
    Ok (Let x1 (Var x2))
  | _, [] | [], _ => Error "Not the right number of arguments" 
  end.

Definition two_expression_style (e1 e2 : expression)
  (f : variable -> variable -> expression) : expression :=
  match e1, e2 with
  | Var x, Var y => f x y
  | Var x, _ => Let "phantom"%string e2 (f x "phantom"%string)
  | _, Var y => Let "phantom"%string e1 (f "phantom"%string y)
  | _, _ => Let "phantom1"%string e1 (Let "phantom2"%string e2 
    (f "phantom1"%string "phantom2"%string))
  end.

(********************************
  Function Operational Semantics
*********************************)
Fixpoint semantics_expression_exec (step : nat) (p : program)
  (ex_state : execution_state) : result execution_state :=
  match step with
  | 0 => Error ("Too much step taken" ++ nl
      ++ execution_state_to_string ex_state)
  | S n =>
  let (mem, exe_stack) := ex_state in

  match exe_stack with
  | [] => Ok (mem, [])
  (* Be careful with this error *)
  (* | [] => Error "Execution stack should never be empty" *)
  | (env, exe_order)::exe_stack =>

    match exe_order with
    | VariableOutOfScope x =>
      let++ b_x = get_block x env error
        (debug_print mem env (Var x)) ++ nl ++
        "In execution stack:" ++ nl ++ execution_stack_to_string exe_stack
        ++ "In variable out of scope of " ++ x;
      let++ v_x = get_value b_x 0 mem error
        (debug_print mem env (Var x)) ++ "In variable out of scope of " ++
        x;
      let+ mem = drop_memory b_x mem;
      let+ mem = drop_memory b_x mem;
      semantics_expression_exec n p (mem, exe_stack)
    | Expression e =>

    match e with
    | Let x e1 e2 =>
      let exe_stack :=
        [(env, Expression e1)] ++
        [((x, Wait)::env, Expression e2)] ++
        [((x, Wait)::env, VariableOutOfScope x)] ++
        exe_stack in
      semantics_expression_exec n p (mem, exe_stack)

    | FunctionCall f l_v =>
      match f with
      | "drop" =>
        match l_v with
        | [x] =>
          let++ b_x = get_block x env error (debug_print mem env e);
          let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
          match v_x with
          | Poison => Error (debug_print mem env e ++ "Drop of a poison Value"
            ++ nl ++ "Double free probably")
          | Integer i => (* Nothing happens but no error *)
            semantics_expression_exec n p
              (mem, (env, Expression (Value Poison))::exe_stack)
          | Ptr b off =>
            let+ mem = change_memory b off Poison mem;
            (* TODO DROP MORE *)
            semantics_expression_exec n p
              (mem, (env, Expression (Value Poison))::exe_stack)
          end
        | _ => Error (debug_print mem env e ++ "Drop only take one argument")
        end
      | _ =>
        (* Test if the function is drop *)
          let++ (args, e) = get_function_args_expression f p
            error (debug_print mem env e);
          let+ let_chain = args_definition_function_call args l_v;
          semantics_expression_exec n p
          (mem, (env, Expression (let_chain e))::exe_stack)
      end

    | DerefAssign x y =>
      let+ variable_state_x = get_variable_state x env;
      let++ b_x = get_block x env error debug_print mem env e;
      let++ v_x = get_value b_x 0 mem error debug_print mem env e
        ++ nl ++ "For" ++ x;
      let+ variable_state_y = get_variable_state y env;
      let++ b_y = get_block y env error (debug_print mem env e);
      let++ v_y = get_value b_y 0 mem error debug_print mem env e
        ++ nl ++ "For" ++ y;

      match v_x with
      | Ptr b off =>
        let+ mem = change_memory b off v_y mem;
        semantics_expression_exec n p
          (mem, (env, Expression (Value Poison))::exe_stack)
      | _ => Error (debug_print mem env e ++ nl ++ "In Deref Assign" ++ nl
          ++ "Value of " ++ x ++ " should be a pointer but is" 
          ++ value_to_string v_x)
      end

    | Assign x y =>
      let++ b_x = get_block x env error (debug_print mem env e);

      let variable_state_y := get_variable_state y env in
      let++ b_y = get_block y env error (debug_print mem env e);

      let++ v_y = get_value b_y 0 mem error (debug_print mem env e)
        ++ nl ++ "For" ++ y;

      let+ mem = change_memory b_x 0 v_y mem;
      semantics_expression_exec n p
        (mem, (env, Expression (Value Poison))::exe_stack)

    | Var x =>
      let++ b_x = get_block x env error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error (debug_print mem env e)
        ++ nl ++ "For" ++ x;

      match exe_stack with
      | [] => Ok (mem, [(env, Expression (Value v_x))])
      | _ =>
        if execution_stack_only_var_out_of_scope exe_stack then
          let+ (mem, exe_stack) =
            semantics_expression_exec n p (mem, exe_stack);
          Ok (mem, [(env, Expression (Value v_x))])
        else
          (* Todo change env so that x has been read *)
          semantics_expression_exec n p
            (mem, (env, Expression (Value v_x))::exe_stack)
      end

    | Value v =>
      match exe_stack with
      | [] => Ok (mem, [(env, Expression (Value v))])
      | _ =>
        if execution_stack_only_var_out_of_scope exe_stack then
          let+ (mem, exe_stack) =
            semantics_expression_exec n p (mem, exe_stack);
          Ok (mem, [(env, Expression (Value v))])
        else
          let (mem, b) := allocate [v] mem in
          let++ exe_stack = replace_2_next_wait b exe_stack
            error (debug_print mem env e);
          semantics_expression_exec n p (mem, exe_stack)
      end

    | Product l_x =>
      let+ l_v = variable_list_to_value_list l_x mem env;
      let (mem, b) := allocate l_v mem in
      semantics_expression_exec n p
        (mem, (env, Expression (Value (Ptr b 0)))::exe_stack)

    | Borrow x =>
      let++ b_x = get_block x env error (debug_print mem env e);
        semantics_expression_exec n p
          (mem, (env, Expression (Value (Ptr b_x 0)))::exe_stack)
    | Deref x =>
      let++ b_x = get_block x env error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
      match v_x with
      | Poison => Error "Poison cannot be dereferenced"
      | Integer i => Error ((debug_print mem env e) ++
        "Integer " ++ nat_to_string i ++ " cannot be dereferenced")
      | Ptr b off =>
        let+ v_deref_x = get_value b off mem;
        semantics_expression_exec n p
          (mem, (env, Expression (Value v_deref_x))::exe_stack)
      end
    | Op op x y =>
      let++ b_x = get_block x env error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
      let++ b_y = get_block y env error (debug_print mem env e);
      let++ v_y = get_value b_y 0 mem error (debug_print mem env e);
      match v_x, v_y with
      | Integer ix, Integer iy =>
        match op with
        | Add =>
          semantics_expression_exec n p
            (mem, (env, Expression (Value (Integer (ix + iy))))::exe_stack)
        | Sub =>
          semantics_expression_exec n p
            (mem, (env, Expression (Value (Integer (ix - iy))))::exe_stack)
        end
      | _, _ => Error (debug_print mem env e ++
        "Operation only on integers" ++ nl ++
        "Not the case for " ++ x ++ " " ++ y)
      end
    | IfEqual x y fst snd =>
      let++ b_x = get_block x env error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
      let++ b_y = get_block y env error (debug_print mem env e);
      let++ v_y = get_value b_y 0 mem error (debug_print mem env e);
      match v_x, v_y with
      | Integer i, Integer j =>
        if Nat.eqb i j then
          semantics_expression_exec n p (mem, (env, Expression fst)::exe_stack)
        else
          semantics_expression_exec n p (mem, (env, Expression snd)::exe_stack)
      | _, _ => Error (debug_print mem env e ++ 
        "The condition of an IF condition should evaluate to 0 or 1" ++
        "Here it evaluates to " ++ value_to_string v_x)
      end
    end
    end
  end
  end.

Definition executeTest (code : string) : result value :=
  let++ p = parse_program code error "Error in Parsing: ";
  let+ (args, main_expression) = get_function_args_expression "main" p;
  match args with
  | [] =>
    let default_state := ([], [([], Expression main_expression)]) in
    let++ exec_state = semantics_expression_exec BigNat p default_state
      error "Error During Execution" ++ nl ++
      "In this expression: " ++ nl ++ expression_to_string main_expression;
    match exec_state with
    | (mem, []) => Error ("exe_stack is empty at the end" ++ nl ++
             "With this execution state: " ++ nl ++
               execution_state_to_string exec_state)
    | (mem,  [(env, Expression (Value v))]) =>
        Error ("Execution Success" ++ nl ++
          (debug_print mem env main_expression) ++
          "Final Value => " ++ value_to_string v)
    (* | (_,  [(_, Expression (Value v))]) => Ok v *)
    | _ => Error ("Execution not finished" ++ nl ++
             "With this execution state: " ++ nl ++
               execution_state_to_string exec_state)
    end
  | _ => Error "main function should have no arguments"
  end.

Module SemanticsTest.
Compute executeTest "fn main() { }". (*Ok*)
Compute executeTest "fn main(){4}". (*Ok*)
Compute executeTest "fn main(){{3, 2}}". (*Ok*)
Compute executeTest "fn main(){x = 3}". (* Normal Error *)
Compute executeTest "fn main(){let a = 4; 5}". (*Ok*)
Compute executeTest "fn main(){let a = 4; a}". (*Ok*)
Compute executeTest "fn main(){let a = 4; *a}". (* Normal Error *)
Compute executeTest "fn main(){let a = 4; &a}". (*Ok*)
Compute executeTest "fn main(){let a = 4; a = 5}". (*Ok*)
Compute executeTest "fn main(){let a = 4; a = 12; *a}". (* Normal Error *)
Compute executeTest "fn main(){let a = 4; a = 12; a}". (*Ok*)
Compute executeTest "fn main(){let a = 4; let y = a; y}". (*Ok*)
Compute executeTest "fn main(){let a = 4; let y = a; a = 32; y}". (*Ok*)
Compute executeTest "fn main(){let a = 4; let y = a; *y}". (* Normal Error *)
Compute executeTest "fn main(){let a = 4; a = 12; let y = a; y}". (*Ok*)
Compute executeTest "fn main(){let a = 4; a = 12; let y = 4; y = a; y}". (*Ok*)
Compute executeTest "fn main(){let a = 4; a = 12; let y = a; a = 33; y}". (*Ok*)
Compute executeTest
  "fn main(){let a = 4; a = 12; let y = a; *y}". (* Normal Error *)
Compute executeTest
  "fn main(){let a = 4; a = 12; let y = a; y = 32; y = 42; y}". (*Ok*)
Compute executeTest "fn main(){let a = 4; let y = &a; a}". (*Ok*)
Compute executeTest "fn main(){let a = 4; a = 5; let y = &a; a}". (*OK*)
Compute executeTest "fn main(){let a = 4; let y = &a; *y = 12; a}". (*Ok*)
Compute executeTest "fn main(){let a = 4; let y = &a; y = 32; a}". (*Ok*)
Compute executeTest "fn main(){let a = 4; let y = &a; a = 32; *y}". (*Ok*)
Compute executeTest "fn main(){let x = 4; let y = 5; let a = {x, y}; a}". (*Ok*)
Compute executeTest "fn main(){let a = {4, 12}; 3}". (*Ok*)
Compute executeTest "fn main(){let a = {4, 12}; a}". (*Ok*)
Compute executeTest "fn main(){let a = 4; let b = a = 3; a}". (*Ok*)
Compute executeTest "fn main(){let a = 4; let b = a = 3; b}". (*Ok*)
Compute executeTest "
fn main() {
  let a = 4;
  let b = (3 + a);
  b
}
fn foo() {
  12
}
".
Compute executeTest "
fn main() {
  let a = 4;
  let b = a = 3;
  foo()
}
fn foo() {
  12
}
".
Compute executeTest "
fn main() {
  let a = 4;
  a = 12;
  let b = 42;
  foo(a)
}
fn foo(a) {
  (a + 2)
}
".
Compute executeTest "
fn main() {
  fib(4)
}
fn fib(n) {
  if n == 0 {
    1
  } else {
    (fib((n - 1)) + fib((n - 2)))
  }
}
".
Compute executeTest "
fn main() {
  fib(7)
}
fn fib(n) {
  if n == 0 {
    1
  } else { if n == 1 {
    1
  } else {
    (fib((n - 1)) + fib((n - 2)) )
  }}
}
".
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
