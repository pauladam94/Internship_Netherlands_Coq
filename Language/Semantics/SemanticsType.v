Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Require Import Integers.
Import ListNotations.
Require Import Utils.Utils.
Require Import Utils.Error.
Require Import Language.Language.
Require Import Expression.Expression.
Require Import Parser.ParserRustProgram.
Require Import Parser.ParserExpression.
Require Import Program.Program.

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

Inductive execution_order : Type :=
  | VariableOutOfScope (v : variable)
  | Expression (e : expression) (lang : lang_flag).

Definition memory : Type := list (block * lang_flag * semaphore * list value).
Definition symbol_table : Type := list (variable * variable_state).
Definition execution_stack : Type := list (symbol_table * execution_order).
Definition execution_state : Type := (memory * execution_stack).

(*****************
  Pretty Printing
******************)

Definition execution_order_to_string (exe_order : execution_order) : string :=
  match exe_order with
  | VariableOutOfScope x => "Variable Out of Scope" ++ x
  | Expression e flag => expression_to_string e
  end.

Definition semaphore_to_string (s : semaphore) : string :=
  match s with
  | Dropped => "Dropped"
  | Writing => "Writing"
  | Reading n => "Read " ++ nat_to_string n
  end.

Definition variable_state_to_string (var_st : variable_state) : string :=
  match var_st with
  | Wait => "Wait"
  | Block b => "B " ++ nat_to_string b
  end.

Fixpoint symbol_table_to_string_helper (env : symbol_table) : string :=
  match env with
  | [] => ""
  | [(x, st)] => "  '" ++ x ++ "': " ++
    variable_state_to_string st
  | (x, st)::env => "  '" ++ x ++ "': " ++ variable_state_to_string st ++ nl ++
       symbol_table_to_string_helper env
  end.

Definition symbol_table_to_string (env : symbol_table) : string :=
  symbol_table_to_string_helper env.

Fixpoint value_list_to_string (l : list value) : string :=
  match l with
  | [] => ""
  | [h] => value_to_string h
  | h::q => value_to_string h ++ " , " ++ value_list_to_string q
  end.

Fixpoint memory_to_string (mem : memory) : string :=
  match mem with
  | [] => ""
  | (b, flag, sema , l_v)::q => "  B " ++ nat_to_string b ++ "|"
      ++ semaphore_to_string sema
      ++ " [" ++ value_list_to_string l_v ++ "]" ++ nl
      ++ memory_to_string q
  end.

Fixpoint execution_stack_to_string (exe_stack : execution_stack) : string :=
  match exe_stack with
  | [] => ""
  | (env, Expression e lang)::q => symbol_table_to_string env
      ++ lang_flag_to_string lang ++ " expression:" ++ nl
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

(*****************
  Execution Stack
******************)

Fixpoint execution_stack_only_var_out_of_scope (exe_stack : execution_stack)
  : bool :=
  match exe_stack with
  | [] => true
  | (_, VariableOutOfScope _)::q => execution_stack_only_var_out_of_scope q
  | (_, Expression _ _)::q => false
  end.

Fixpoint wait_env (b : block) (env : symbol_table)
  : result (symbol_table * bool) :=
  match env with
  | [] => Ok ([], false)
  | (x, var_st)::env =>
      match var_st with
      | Wait =>
          Ok ((x, Block b)::env, true)
      | Block _ =>
          let+ (env, done) = wait_env b env;
          Ok ((x, var_st)::env, done)
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

Definition replace_2_next_wait (b : block)
  (exe_stack : execution_stack) : result execution_stack :=
  replace_n_next_wait 2 b exe_stack.

Fixpoint get_block (x : variable) (env : symbol_table)
  : result block :=
  match env with
  | [] => Error ("Error getting Block Offset, " ++ x ++ " not found")
  | (y, st)::env' =>
      match st with
      | Wait => get_block x env'
      | Block b =>
        if String.eqb x y
        then Ok b
        else get_block x env'
      end
  end.

Fixpoint max (l : list nat) : nat :=
  match l with
  | [] => 0
  | h::q =>
    let max_q := max q in if Nat.leb max_q h then h else max_q
  end.

Definition allocate (lang : lang_flag) (l_v : list value) (mem : memory)
  : (memory * block) :=
  let b := max
    (map (
    fun (x : (block * lang_flag * semaphore * list value)) =>
        let (b_sema, _) := x in
        let (b_flag, _) := b_sema in
        let (b, _) := b_flag in
        b
    ) mem) + 1 in
  ((((b, lang), Reading 0), l_v)::mem, b).

Fixpoint get_variable_state (x : variable) (env : symbol_table) : result variable_state :=
  match env with
  | [] => Error ("Get Variable State" ++ nl ++ x ++ " not found")
  | (y, st)::env => if x =? y then Ok st else get_variable_state x env
  end.

Fixpoint get_semaphore (b : block) (mem : memory)
  : result semaphore :=
  match mem with
  | [] => Error ("Nothing Found in Memory at position" ++ 
      value_to_string (Ptr b 0))
  | (((b0, _), sema), _)::mem => if Nat.eqb b b0 then Ok sema
    else get_semaphore b mem
  end.

Fixpoint get_list_value (b : block) (mem : memory)
  : result (list value) :=
  match mem with
  | [] => Error ("Nothing Found in Memory at position" ++ 
      value_to_string (Ptr b 0))
  | (((b0, _), _), l_v)::mem =>
    if Nat.eqb b b0
    then Ok l_v
    else get_list_value b mem
  end.

Fixpoint get_value_list_value (off : offset) (l : list value) : result value :=
  match off, l with
  | _, [] => Error "Out of bounds, offset too big for list"
  | 0, h::q => Ok h
  | S n, h::q => get_value_list_value n q
  end.

Fixpoint get_value (b : block) (off : offset) (mem : memory) : result value :=
  match mem with
  | [] => Error ("Nothing Found in Memory at position" ++ 
      value_to_string (Ptr b off))
  | (((b0, _), _), l)::mem =>
    if Nat.eqb b b0
    then get_value_list_value off l
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

Fixpoint change_semaphore (b  : block) (sema : semaphore) (m : memory)
  : result memory :=
  match m with
  | [] => Error "Memory is empty : cannot change"
  | (((b0, lang), s), l)::m0 =>
    if Nat.eqb b b0 then
      Ok ((((b0, lang), sema), l)::m0)
    else
      let+ new_memory = change_semaphore b sema m0;
      Ok ((((b0, lang), s), l)::new_memory)
  end.

Fixpoint change_value_memory (b  : block) (off : offset) (v : value)
  (m : memory) : result memory :=
  match m with
  | [] => Error "Memory is empty : cannot change"
  | (((b0, lang), s), l)::m0 =>
    if Nat.eqb b b0 then
      let++ l = change_list_value off v l
        error "Error changing the block " ++ nat_to_string b ++ "";
      Ok ((((b0, lang), s), l)::m0)
    else
      let+ new_memory = change_value_memory b off v m0;
      Ok ((((b0, lang), s), l)::new_memory)
  end.


(* todo really do it *)
Fixpoint free_memory (b : block) (m : memory) : result memory :=
  match m with
  | [] => Error ("Drop Memory but Memory is empty")
  | (((b0, lang), s), l_v)::m0 =>
    if Nat.eqb b b0 then
      match l_v with
      | [Ptr b off] =>
        match s with
        | Dropped => Error "free memory that is free or passed ownership"
        | Writing => Error "free a variable mutably borrowed"
        | Reading 0 => Ok ((((b0, lang), Dropped), l_v)::m0)
        | Reading i => Ok ((((b0, lang), Reading (i - 1)), l_v)::m0)
        end
      | _ => Ok ((((b0, lang), Dropped), l_v)::m0)
      end
    else
      let+ new_memory = free_memory b m0;
      Ok ((((b0, lang), s), l_v)::new_memory)
  end.

Fixpoint free_stack_memory (b : block) (m : memory) : result memory :=
  match m with
  | [] => Error ("Drop Memory but Memory is empty")
  | (((b0, lang), s), l_v)::m0 =>
    if Nat.eqb b b0 then
      match l_v with
      | [Ptr b off] =>
        match s with
        | Dropped => Error "free memory that is free or passed ownership"
        | Writing => Error "free a variable mutably borrowed"
        | Reading 0 => Ok ((((b0, lang), Dropped), l_v)::m0)
        | Reading i => Ok ((((b0, lang), Reading (i - 1)), l_v)::m0)
        end
      | _ => Ok ((((b0, lang), Dropped), l_v)::m0)
      end
    else
      let+ new_memory = free_stack_memory b m0;
      Ok ((((b0, lang), s), l_v)::new_memory)
  end.

(* Fixpoint drop_memory_helper (n : nat) (b : block) (m : memory) *)
(*   : result memory := *)
(*   match n with *)
(*   | 0 => Error "Too much step taken" *)
(*   | S n => *)
(**)
(*   match m with *)
(*   | [] => Error ("Drop Memory" ++ nl ++ "Memory is empty") *)
(*   | (((b0, lang), s), l)::m0 => *)
(*     if Nat.eqb b b0 then *)
(*       drop_list_value_memory n l ((((b0, lang), Dropped), l)::m0) *)
(*     else *)
(*       let+ new_memory = drop_memory_helper n b m0; *)
(*       Ok ((((b0, lang), s), l)::new_memory) *)
(*   end *)
(**)
(*   end *)

(* with drop_list_value_memory (n : nat) (l_v : list value) (mem : memory) *)
(* : result memory := *)
(*   match n with *)
(*   | 0 => Error "Too much step taken" *)
(*   | S n => *)
(**)
(*   match l_v with *)
(*   | [] => Error "trying to drop empty block" *)
(*   | v::l_v => *)
(*     match v with *)
(*     | Poison => Error "Trying to drop a poison value" *)
(*     | Integer _ => Ok mem *)
(*     | Ptr b off => *)
(*       let+ l_v_2 =  *)
(*       drop_list_value_memory n (get_list_value b mem) mem *)
(*     end *)
(*   end *)
(**)
(*   end. *)
(**)
(* (* block should be a block of a variable *) *)
(* Definition drop_memory (b : block) (m : memory) : result memory := *)
(*   drop_memory_helper BigNat b m. *)




(* Previous implem *)
(* Fixpoint drop_memory (b : block) (m : memory) : result memory := *)
(*   match m with *)
(*   | [] => Error ("Drop Memory" ++ nl ++ "Memory is empty") *)
(*   | (((b0, lang), s), l)::m0 => *)
(*     if Nat.eqb b b0 then *)
(*       Ok ((((b0, lang), Dropped), l)::m0) *)
(*     else *)
(*       let+ new_memory = drop_memory b m0; *)
(*       Ok ((((b0, lang), s), l)::new_memory) *)
(*   end. *)

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
