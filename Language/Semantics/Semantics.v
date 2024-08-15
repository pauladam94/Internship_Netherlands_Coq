Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Utils.Utils.
Require Import Utils.Error.
Require Import Language.Language.
Require Import Expression.Expression.
Require Import Parser.ParserRustProgram.
Require Import Program.Program.
Require Import Semantics.SemanticsType.

Fixpoint list_poison_value (n: nat) : list value :=
  match n with
  | 0 => []
  | S n => Poison::(list_poison_value n)
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
  | (env, exe_order)::exe_stack =>

    match exe_order with
    | VariableOutOfScope x => (* Clean of the stack -- change of semaphore *)
      let++ b_x = get_block x env error
        (debug_print mem env (Var x)) ++ nl ++
        "In execution stack:" ++ nl ++ execution_stack_to_string exe_stack
        ++ "In variable out of scope of " ++ x;
      let++ mem = free_stack_memory b_x mem error debug_print mem env (Var x);
      semantics_expression_exec n p (mem, exe_stack)
    | Expression e lang =>


    match lang with
    (***************************)
    (***** RUST EXPRESSION *****)
    (***************************)
    | Rust =>

    match e with
    | Let x e1 e2 =>
      let exe_stack :=
        [(env, Expression e1 lang)] ++
        [((x, Wait)::env, Expression e2 Rust)] ++
        [((x, Wait)::env, VariableOutOfScope x)] ++
        exe_stack in
      semantics_expression_exec n p (mem, exe_stack)

    | FunctionCall f l_v =>
      match f with
      | "drop" =>
        match l_v with
        | [x] =>
          let++ b_x = get_block x env error (debug_print mem env e);
          (* let++ v_x = get_value b_x 0 mem error debug_print mem env e; *)
          (* let++ mem = drop_memory b_x mem error debug_print mem env e; *)
          (* semantics_expression_exec n p (mem, exe_stack *)
          Error "todo drop"
        | _ => Error ("Drop only takes one argument" ++ debug_print mem env e)
        end
      | "castref" =>
        match l_v with
        | [x] =>
          let++ b_x = get_block x env error (debug_print mem env e);
          let++ v_x = get_value b_x 0 mem error debug_print mem env e;
          let++ (b, off) =
            match v_x with
            | Poison => Error "cannot cast ref poison"
            | NullPtr => Error "cannot cast ref a null ptr"
            | Integer _ => Error "cannot cast ref integer"
            | Ptr b off => Ok (b, off)
            end error debug_print mem env e;
          let++ sema = get_semaphore b mem error debug_print mem env e;
          let++ mem =
          match sema with
          | Reading i =>
              let+ mem = change_semaphore b (Reading (i + 1)) mem;
              Ok mem
          | Writing => Error "cannot cast ref on ref mut"
          | Dropped => Error ""
          end error debug_print mem env e;
          semantics_expression_exec n p
            (mem, (env, Expression (Value (Ptr b off)) Rust)::exe_stack)
        | _ => Error ("Cast ref takes one argument" ++ debug_print mem env e)
        end
      | "castrefmut" =>
        match l_v with
        | [x] =>
          let++ b_x = get_block x env error (debug_print mem env e);
          let++ v_x = get_value b_x 0 mem error debug_print mem env e;
          let++ (b, off) =
            match v_x with
            | Poison => Error "cannot cast ref poison"
            | NullPtr => Error "cannot cast ref a null ptr"
            | Integer _ => Error "cannot cast ref integer"
            | Ptr b off => Ok (b, off)
            end error debug_print mem env e;
          let++ sema = get_semaphore b mem error debug_print mem env e;
          let++ mem =
          match sema with
          | Reading 0 =>
              let+ mem = change_semaphore b Writing mem;
              Ok mem
          | Reading _ => Error "cannot cast ref mut on ref"
          | Writing => Error "cannot cast ref mut on ref mut"
          | Dropped => Error "cannot cast ref mut on dropped"
          end error debug_print mem env e;
          semantics_expression_exec n p
            (mem, (env, Expression (Value (Ptr b off)) Rust)::exe_stack)
        | _ => Error ("Cast ref mut takes one argument" ++ debug_print mem env e)
        end
      | _ =>
          let++ (args_expr, lang) = get_function_args_expression f p
            error (debug_print mem env e);
          let (args, e) := args_expr in
          let+ let_chain = args_definition_function_call args l_v;
          semantics_expression_exec n p
          (mem, (env, Expression (let_chain e) lang)::exe_stack)
      end

    | DerefAssign x y =>
      let++ b_x = get_block x env error debug_print mem env e;
      let++ v_x = get_value b_x 0 mem error debug_print mem env e
        ++ nl ++ "For" ++ x;

      let++ b_y = get_block y env
        error (debug_print mem env e);
      let++ v_y = get_value b_y 0 mem error debug_print mem env e
        ++ nl ++ "For" ++ y;

      let++ sema = get_semaphore b_x mem error debug_print mem env e;
      match sema with
      | Reading 0 =>
        match v_x with
        | Ptr b off =>
          let+ sema = get_semaphore b mem;
          match sema with
          | Writing | Reading 0 =>
            let+ mem = change_value_memory b off v_y mem;
            semantics_expression_exec n p
              (mem, (env, Expression (Value Poison) lang)::exe_stack)
          | _ => Error ("Variable '" ++ x ++ "' not mutable reference or owner")
          end
        | _ => Error (debug_print mem env e ++ nl ++ "In Deref Assign" ++ nl
          ++ "Value of " ++ x ++ " should be a pointer but is" 
          ++ value_to_string v_x)
        end

      | Writing => Error (debug_print mem env e ++
          "Cannot mutation while being mut borrow")
      | Reading _ => Error (debug_print mem env e ++
          "Cannot mutate while being borrow")
      | Dropped => Error (debug_print mem env e ++
          "Cannot mutate while being dropped")
      end

    | Assign x y =>
        (* TODO check if x is owned or borrowed mutably *)
        (* TODO check if y is owned *)
      let++ b_x = get_block x env
        error (debug_print mem env e);

      let variable_state_y := get_variable_state y env in
      let++ b_y = get_block y env
        error (debug_print mem env e);

      let++ v_y = get_value b_y 0 mem error (debug_print mem env e)
        ++ nl ++ "For " ++ y;

      let+ mem = change_value_memory b_x 0 v_y mem;
      semantics_expression_exec n p
        (mem, (env, Expression (Value Poison) lang)::exe_stack)

    | Var x =>
      let++ b_x = get_block x env
        error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error debug_print mem env e;
      let++ sema_x = get_semaphore b_x mem error debug_print mem env e;
      let++ mem =
        match sema_x with
        | Dropped => Error ("Variable '" ++ x ++
          "' passed ownership or has been dropped")
        | Writing => Error ("Variable '" ++ x ++
            "' mut borrowed by someone else")
        | Reading 0 =>
          change_semaphore b_x Dropped mem
        | Reading _ => Error ("Variable '" ++ x ++
          "' immut borrowed by someone else")
        end error debug_print mem env e;
      semantics_expression_exec n p
        (mem, (env, Expression (Value v_x) lang)::exe_stack)

    | Value v =>
      match exe_stack with
      | [] => Ok (mem, [(env, Expression (Value v) lang)])
      | _ =>
        if execution_stack_only_var_out_of_scope exe_stack then
          let+ (mem, exe_stack) =
            semantics_expression_exec n p (mem, exe_stack);
          Ok (mem, [(env, Expression (Value v) lang)])
        else
          let (mem, b) := allocate Rust [v] mem in
          let++ exe_stack = replace_2_next_wait b exe_stack
            error (debug_print mem env e);
          semantics_expression_exec n p (mem, exe_stack)
      end

    | Product l_x =>
      let+ l_v = variable_list_to_value_list l_x mem env;
      let (mem, b) := allocate Rust l_v mem in
      semantics_expression_exec n p
        (mem, (env, Expression (Value (Ptr b 0)) lang)::exe_stack)

    | Borrow x =>
      let++ b_x = get_block x env
        error (debug_print mem env e);
        let++ sema_x = get_semaphore b_x mem error debug_print mem env e;
        let++ mem =
        match sema_x with
        | Dropped => Error ("Immut Borrow of dropped variable " ++ x ++ nl ++
            (debug_print mem env e))
        | Writing => Error ("Immut Borrow of a variable already BorrowMut "
            ++ x ++ nl ++ (debug_print mem env e))
        | Reading i =>
            change_semaphore b_x (Reading (i + 1)) mem
        end error debug_print mem env e;
        semantics_expression_exec n p
          (mem, (env, Expression (Value (Ptr b_x 0)) Rust)::exe_stack)

    | BorrowMut x =>
      let++ b_x = get_block x env
        error (debug_print mem env e);
      let++ sema_x = get_semaphore b_x mem error (debug_print mem env e);
      let++ mem = match sema_x with
        | Dropped => Error ("BorrowMut of a dropped variable " ++ x ++ nl ++
            (debug_print mem env e))
        | Writing => Error ("BorrowMut of a variable already BorrowMut "
            ++ x ++ nl ++ (debug_print mem env e))
        | Reading 0 =>
          change_semaphore b_x Writing mem
        | Reading _ => Error ("BorrowMut of a variable already Borrow"
            ++ x ++ nl ++ (debug_print mem env e))
        end error debug_print mem env e;
        semantics_expression_exec n p
          (mem, (env, Expression (Value (Ptr b_x 0)) lang)::exe_stack)

    | Deref x =>
         (* Be more restritive here not every var can be deref *)
      let++ b_x = get_block x env
        error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
      let++ (b, off) =
        match v_x with
        | NullPtr => Error "dereferencing a null ptr"
        | Poison => Error "Poison cannot be dereferenced"
        | Integer i => Error ((debug_print mem env e) ++
          "Integer " ++ nat_to_string i ++ " cannot be dereferenced")
        | Ptr b off => Ok (b,  off)
        end error debug_print mem env e;
      let+ v_deref_x = get_value b off mem;
        semantics_expression_exec n p
          (mem, (env, Expression (Value v_deref_x) Rust)::exe_stack)
    | Op op x y =>
      let++ b_x = get_block x env
        error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
      let++ b_y = get_block y env
        error (debug_print mem env e);
      let++ v_y = get_value b_y 0 mem error (debug_print mem env e);
      let++ v = match v_x, v_y with
      | Integer ix, Integer iy => match op with
                                  | Add => Ok (Integer(ix + iy))
                                  | Sub => Ok (Integer(ix - iy)) end
      | Ptr b off, Integer i => match op with
                                | Add => Ok (Ptr b (off + i))
                                | Sub => Ok (Ptr b (off - i)) end
      | Integer i, Ptr b off => match op with
                                | Add => Ok (Ptr b (i + off))
                                | Sub => Ok (Ptr b (i - off)) end
      | _, _ => Error ("Operation only on integers" ++ nl ++
        "Not the case for '" ++ x ++ "' or '" ++ y ++ "'")
      end error debug_print mem env e;
        semantics_expression_exec n p
          (mem, (env, Expression (Value v) lang)::exe_stack)
    | IfEqual x y fst snd =>
      let++ b_x = get_block x env
        error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
      let++ b_y = get_block y env
        error (debug_print mem env e);
      let++ v_y = get_value b_y 0 mem error (debug_print mem env e);
      match v_x, v_y with
      | Integer i, Integer j =>
        if Nat.eqb i j then
          semantics_expression_exec n p
            (mem, (env, Expression fst lang)::exe_stack)
        else
          semantics_expression_exec n p
            (mem, (env, Expression snd lang)::exe_stack)
      | _, _ => Error (debug_print mem env e ++
        "The condition of an IF condition should evaluate to 0 or 1" ++
        "Here it evaluates to " ++ value_to_string v_x)
      end
    end

    (************************)
    (***** C EXPRESSION *****)
    (************************)

    | C =>

    match e with
    | Let x e1 e2 =>
      let exe_stack :=
        [(env, Expression e1 C)] ++
        [((x, Wait)::env, Expression e2 C)] ++
        [((x, Wait)::env, VariableOutOfScope x)] ++
        exe_stack in
      semantics_expression_exec n p (mem, exe_stack)

    | FunctionCall f l_v =>
      match f with
      | "free" =>
        match l_v with
        | [x] =>
          let++ b_x = get_block x env
            error (debug_print mem env e);
          let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
          match v_x with
          | NullPtr => Error "a"
          | Poison => Error (debug_print mem env e ++ "free of a poison Value"
            ++ nl ++ "Double free probably")
          | Integer i => (* Nothing happens but no error *)
            semantics_expression_exec n p
              (mem, (env, Expression (Value Poison) lang)::exe_stack)
          | Ptr b off =>
            let+ mem = change_value_memory b off Poison mem;
              (* TODO free all Ptr(b, [0...]) *)
            semantics_expression_exec n p
              (mem, (env, Expression (Value Poison) lang)::exe_stack)
          end
        | _ => Error ("free only takes one argument" ++ debug_print mem env e)
        end
      | "malloc" =>
        match l_v with
        | [x] =>
          let++ b_x = get_block x env
            error (debug_print mem env e);
          let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
          match v_x with
          | NullPtr => Error ""
          | Poison => Error "malloc takes only integer here got Poison"
          | Ptr b off => Error "malloc only takes integer here got pointer"
          | Integer i =>
            let (mem, b) := allocate C (list_poison_value i) mem in
            semantics_expression_exec n p
              (mem, (env, Expression (Value (Ptr b 0)) C)::exe_stack)
          end

        | _ => Error (debug_print mem env e ++ "malloc take one argument")
        end
      | _ =>
          let++ (args_expr, lang) = get_function_args_expression f p
            error (debug_print mem env e);
          let (args, e) := args_expr in
          let+ let_chain = args_definition_function_call args l_v;
          semantics_expression_exec n p
            (mem, (env, Expression (let_chain e) lang)::exe_stack)
      end

    | DerefAssign x y =>
      let+ variable_state_x = get_variable_state x env;
      (* TODO check if the variable is mutably borrowed or owned *)
      let++ b_x = get_block x env
        error debug_print mem env e;
      let++ v_x = get_value b_x 0 mem error debug_print mem env e
        ++ nl ++ "For" ++ x;
      let+ variable_state_y = get_variable_state y env;
      let++ b_y = get_block y env
        error (debug_print mem env e);
      let++ v_y = get_value b_y 0 mem error debug_print mem env e
        ++ nl ++ "For" ++ y;

      match v_x with
      | Ptr b off =>
        let+ sema = get_semaphore b mem;
        match sema with
        | Writing | Reading 0 =>
          let+ mem = change_value_memory b off v_y mem;
          semantics_expression_exec n p
            (mem, (env, Expression (Value Poison) lang)::exe_stack)
        | _ => Error ("Variable '" ++ x ++ "' not mutable reference or owner")
        end
      | _ => Error (debug_print mem env e ++ nl ++ "In Deref Assign" ++ nl
          ++ "Value of " ++ x ++ " should be a pointer but is" 
          ++ value_to_string v_x)
      end

    | Assign x y =>
        (* TODO check if x is owned or borrowed mutably *)
        (* TODO check if y is owned *)
      let++ b_x = get_block x env
        error (debug_print mem env e);

      let variable_state_y := get_variable_state y env in
      let++ b_y = get_block y env
        error (debug_print mem env e);

      let++ v_y = get_value b_y 0 mem error (debug_print mem env e)
        ++ nl ++ "For " ++ y;

      let+ mem = change_value_memory b_x 0 v_y mem;
      semantics_expression_exec n p
        (mem, (env, Expression (Value Poison) lang)::exe_stack)

    | Var x =>
      let++ b_x = get_block x env
        error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error debug_print mem env e;
      semantics_expression_exec n p
        (mem, (env, Expression (Value v_x) lang)::exe_stack)

    | Value v =>
      match exe_stack with
      | [] => Ok (mem, [(env, Expression (Value v) lang)])
      | _ =>
        if execution_stack_only_var_out_of_scope exe_stack then
          let+ (mem, exe_stack) =
            semantics_expression_exec n p (mem, exe_stack);
          Ok (mem, [(env, Expression (Value v) lang)])
        else
          let (mem, b) := allocate C [v] mem in
          let++ exe_stack = replace_2_next_wait b exe_stack
            error (debug_print mem env e);
          semantics_expression_exec n p (mem, exe_stack)
      end

    | Product l_x =>
      let+ l_v = variable_list_to_value_list l_x mem env;
      let (mem, b) := allocate C l_v mem in
      semantics_expression_exec n p
        (mem, (env, Expression (Value (Ptr b 0)) C)::exe_stack)

    | Borrow x =>
      let++ b_x = get_block x env
        error (debug_print mem env e);
        semantics_expression_exec n p
          (mem, (env, Expression (Value (Ptr b_x 0)) lang)::exe_stack)

    | BorrowMut x =>
      let++ b_x = get_block x env
        error (debug_print mem env e);
        semantics_expression_exec n p
          (mem, (env, Expression (Value (Ptr b_x 0)) lang)::exe_stack)

    | Deref x =>
      let++ b_x = get_block x env
        error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
      let++ (b, off) =
        match v_x with
        | NullPtr => Error "dereferencing a null ptr"
        | Poison => Error "Poison cannot be dereferenced"
        | Integer i => Error ((debug_print mem env e) ++
          "Integer " ++ nat_to_string i ++ " cannot be dereferenced")
        | Ptr b off => Ok (b,  off)
        end error debug_print mem env e;
      let+ v_deref_x = get_value b off mem;
        semantics_expression_exec n p
          (mem, (env, Expression (Value v_deref_x) Rust)::exe_stack)

    | Op op x y =>
      let++ b_x = get_block x env
        error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
      let++ b_y = get_block y env
        error (debug_print mem env e);
      let++ v_y = get_value b_y 0 mem error (debug_print mem env e);
      let++ v = match v_x, v_y with
      | Integer ix, Integer iy => match op with
                                  | Add => Ok (Integer(ix + iy))
                                  | Sub => Ok (Integer(ix - iy)) end
      | Ptr b off, Integer i => match op with
                                | Add => Ok (Ptr b (off + i))
                                | Sub => Ok (Ptr b (off - i)) end
      | Integer i, Ptr b off => match op with
                                | Add => Ok (Ptr b (i + off))
                                | Sub => Ok (Ptr b (i - off)) end
      | _, _ => Error ("Operation only on integers" ++ nl ++
        "Not the case for '" ++ x ++ "' or '" ++ y ++ "'")
      end error debug_print mem env e;
        semantics_expression_exec n p
          (mem, (env, Expression (Value v) lang)::exe_stack)
    | IfEqual x y fst snd =>
      let++ b_x = get_block x env
        error (debug_print mem env e);
      let++ v_x = get_value b_x 0 mem error (debug_print mem env e);
      let++ b_y = get_block y env
        error (debug_print mem env e);
      let++ v_y = get_value b_y 0 mem error (debug_print mem env e);
      match v_x, v_y with
      | Integer i, Integer j =>
        if Nat.eqb i j then
          semantics_expression_exec n p
            (mem, (env, Expression fst lang)::exe_stack)
        else
          semantics_expression_exec n p
            (mem, (env, Expression snd lang)::exe_stack)
      | _, _ => Error (debug_print mem env e ++
        "The condition of an IF condition should evaluate to 0 or 1" ++
        "Here it evaluates to " ++ value_to_string v_x)
      end
    end

    end
    end
  end
  end.

Definition executeTest (code : string) : result value :=
  let++ p = parse_program code error "Error in Parsing: ";
  let+ (args, main_expression, lang) = get_function_args_expression "main" p;
  match args with
  | [] =>
    (* Here is defined what language is the main function *)
    let default_state := ([], [([], Expression main_expression C)]) in
    let++ exec_state = semantics_expression_exec BigNat p default_state
      error "Error During Execution" ++ nl ++
      "In this expression: " ++ nl ++ expression_to_string main_expression;
    match exec_state with
    | (mem, []) => Error ("exe_stack is empty at the end" ++ nl ++
             "With this execution state: " ++ nl ++
               execution_state_to_string exec_state)
    | (mem,  [(env, Expression (Value v) lang)]) =>
        Error ("Execution Success" ++ nl ++
          (debug_print mem env main_expression) ++
          "Final Value => " ++ value_to_string v)
      (* | (_,  [(_, Expression (Value v))]) => Ok v // Real line after debug *)
    | _ => Error ("Execution not finished" ++ nl ++
             "With this execution state: " ++ nl ++
               execution_state_to_string exec_state)
    end
  | _ => Error "main function should have no arguments"
  end.

Module SemanticsTest.
Compute executeTest "fnR main() {}". (* Error parsing *)
Compute executeTest "fnC main() {4}". (* Error parsing *)
Compute executeTest "fnR main(){4}". (*Ok*)
Compute executeTest "fnR main(){{3, 2}}". (*Ok*)
Compute executeTest "fnR main(){x = 3}". (* Normal Error *)
Compute executeTest "fnR main(){let a = 4; 5}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; a}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; *a}". (* Normal Error *)
Compute executeTest "fnR main(){let a = 4; &a}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; a = 5}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; a = 12; *a}". (* Normal Error *)
Compute executeTest "fnR main(){let a = 4; a = 12; a}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; let y = a; y}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; let y = a; a = 32; y}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; let y = a; *y}". (* Normal Error *)
Compute executeTest "fnR main(){let a = 4; a = 12; let y = a; y}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; a = 12; let y = 4; y = a; y}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; a = 12; let y = a; a = 33; y}". (*Ok*)
Compute executeTest
  "fn main(){let a = 4; a = 12; let y = a; *y}". (* Normal Error *)
Compute executeTest
  "fn main(){let a = 4; a = 12; let y = a; y = 32; y = 42; y}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; let y = &a; a}". (*Error*)
Compute executeTest "fnR main(){let a = 4; a = 5; let y = &a; *y}". (*OK*)
Compute executeTest "fnR main(){let a = 4; let y = &a; *y = 12}". (*Error*)
Compute executeTest "fnR main(){let a = 4; let y = &mut a; *y = 12}". (*Ok--*)
Compute executeTest "fnR main(){let a = 4; let y = &mut a; y}". (*Ok--*)
Compute executeTest "fnR main(){let a = 4; let y = &mut a; *y = 12; y}". (*Ok--*)
Compute executeTest "fnR main(){let a = 4; let y = &a; *y = 12; y}". (*Error*)
Compute executeTest "fnR main(){let a = 4; let y = &a; y = 32; a}". (*Error*)
Compute executeTest "fnR main(){let a = 4; let y = &a; a = 32; *y}". (*Ok*)
Compute executeTest "fnR main(){let x = 10; let y = 5; let a = {x, y}; a}". (*Ok*)
Compute executeTest "fnR main(){let a = {4, 12}; 3}". (*Ok*)
Compute executeTest "fnR main(){let a = {4, 12}; a}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; let b = a = 3; a}". (*Ok*)
Compute executeTest "fnR main(){let a = 4; let b = a = 3; b}". (*Ok*)
Compute executeTest "
fnR main() {
  let a = foo();
  let b = 3 + a;
  b
}
fnR foo() {
  12
}
". (* Ok 15 *)
Compute executeTest "
fnR main() {
  let a = 4;
  let b = a = 3;
  foo()
}
fnR foo() {
  42
}
". (* Ok 42 *)
Compute executeTest "
fnR main() {
  let a = 4;
  a = 12;
  let b = 42;
  foo(a)
}
fnR foo(a) {
  a + 2
}
". (* Ok 14 *)
Compute executeTest "
fnR main() {
  fib(6)
}
fnR fib(n) {
  if n == 0 {
    1
  } else {
    if n == 1 {
      1
    } else {
      fib(n - 1) + fib(n - 2)
    }
  }
}
". (* should output 13 *)
Compute executeTest "
fnC main() {
  fib(6)
}
fnR fib(n) {
  if n == 0 {
    1
  } else {
    if n == 1 {
      1
    } else {
      fib(n - 1) + fib(n - 2)
    }
  }
}
". (* should output 13 *)
Compute executeTest "
fnR main() {
  let a = {1, 2};
  let b = &a;
  foo(a)
}
fnR foo(a) {
  *a + 1
}
". (* Error a immut borrowed *)
Compute executeTest "
fnR main() {
  let a = {1, 2};
  let b = a;
  foo(a)
}
fnR foo(a) {
  *a + 1
}
". (* Error a been dropped *)
Compute executeTest "
fnR main() {
  let a = {1, 2};
  foo(&a);
  let b = a;
}
fnR foo(a) {
  *a + 1
}
".
Compute executeTest "
fnR main() {
  let a = {1, 2};
  foo(&a);

}
fnR foo(a) {
  *a + 1
}
".

Compute executeTest "
fnC main() {
  let a = {1, 2};
  foo(&a);
}
fnR foo(a) {
  *a + 1
}
".

Compute executeTest "
fnC main() {
  let c = 11;
  let a = &c;
  let b = &c;
  foo(a, b);
  c
}
fnR foo(a, b) {
  let aref = castref(a);
  let bref = castrefmut(b);
  *aref = *aref + *b;
  *a = *a + *b;
}
". (* cannot cast ref mut on ref *)

Compute executeTest "
fnC main() {
  let c = 11;
  let a = &c;
  let b = &c;
  foo(a, b);
  c
}
fnR foo(a, b) {
  let aref = castref(a);
  let bref = castrefmut(b);
  *aref = *aref + *b;
  *a = *a + *b;
}
". (* cannot cast ref mut on ref *)


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
End SemanticsRelationTest.
