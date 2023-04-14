open MicroCamlTypes
open Utils

exception TypeError of string
exception DeclareError of string
exception DivByZeroError 

(* Provided functions - DO NOT MODIFY *)

(* Adds mapping [x:v] to environment [env] *)
let extend env x v = (x, ref v)::env

(* Returns [v] if [x:v] is a mapping in [env]; uses the
   most recent if multiple mappings for [x] are present *)
let rec lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then !value else lookup t x

(* Creates a placeholder mapping for [x] in [env]; needed
   for handling recursive definitions *)
let extend_tmp env x = (x, ref (Int 0))::env

(* Updates the (most recent) mapping in [env] for [x] to [v] *)
let rec update env x v =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then (value := v) else update t x v
        
(* Part 1: Evaluating expressions *)

(* Evaluates MicroCaml expression [e] in environment [env],
   returning a value, or throwing an exception on error *)
let rec eval_expr env e = 

  match e with
  | Value value -> value
  | Binop (_, _, _) -> eval_binop env e
  | Not not -> eval_not env e 
  | ID id -> eval_id env e
  | If (_,_,_) -> eval_if env e
  | Let(_,_,_,_) -> eval_let env e
  | Fun(id, expr) -> eval_fun env e
  | FunctionCall(expr1, expr2) -> eval_function_call env e

(* Handle expressions of type ID *)
and eval_id env e = 

  match e with
  | ID id -> lookup env id
  | _ -> raise (TypeError("Expected e to be of type ID"))


and eval_not env e = 

  match e with
  | Not expr ->
    (
    match expr with
    | Not expr2 -> if eval_not env expr = (Bool true) then (Bool false) else (Bool true)
    | ID id -> 
      let bool = lookup env id in
      (
      match bool with
      | Bool bool -> if bool = true then (Bool false) else (Bool true)
      | _ -> raise (TypeError("Expected type Bool"))
      )
    | _ -> raise (TypeError("Expected expr to be of type Not or ID"))
    )
  | _ -> raise (TypeError("Expected e to be of type Not or ID"))
(*
There are five sorts of binary operator: Those carrying out integer arithmetic;
those carrying out integer ordering comparisons; one carrying out string concatenation; 
and one carrying out equality (and inequality) comparisons; and those implementing boolean logic.
*)
and eval_binop env e =
 match e with
  | Binop(Add, expr1, expr2) -> 
    let val1 = eval_expr env expr1 in
    let val2 = eval_expr env expr2 in
    
    (
    match val1 with
    | Int int1 -> 
      (
      match val2 with
      | Int int2 -> Int (int1 + int2)
      | _ -> raise (TypeError ("Expected val2 to be of type Int"))  
      )
    | _ -> raise (TypeError ("Expected val1 to be of type Int"))
    ) 
    
  | Binop(Sub, expr1, expr2) -> 
    let val1 = eval_expr env expr1 in
    let val2 = eval_expr env expr2 in
    
    (
    match val1 with
    | Int int1 -> 
      (
      match val2 with
      | Int int2 -> Int (int1 - int2)
      | _ -> raise (TypeError ("Expected val2 to be of type Int")) 
      ) 
    | _ -> raise (TypeError ("Expected val1 to be of type Int"))
    ) 

  | Binop(Mult, expr1, expr2) ->
    let val1 = eval_expr env expr1 in
    let val2 = eval_expr env expr2 in
    
    (
    match val1 with
    | Int int1 ->
      ( 
      match val2 with
      | Int int2 -> Int (int1 * int2)
      | _ -> raise (TypeError ("Expected val2 to be of type Int"))  
      )
    | _ -> raise (TypeError ("Expected val1 to be of type Int")) 
    )
  | Binop(Div, expr1, expr2) -> 
    let val1 = eval_expr env expr1 in
    let val2 = eval_expr env expr2 in
    
    (
    match val1 with
    | Int int1 -> 
      (
      match val2 with
      | Int int2 -> if int2 = 0 then raise (DivByZeroError) else Int (int1 / int2)
      | _ -> raise (TypeError ("Expected val2 to be of type Int"))  
      )
    | _ -> raise (TypeError ("Expected val1 to be of type Int")) 
    )
  | Binop(Less, expr1, expr2) ->
    let val1 = eval_expr env expr1 in
    let val2 = eval_expr env expr2 in
     
    (
    match val1 with
    | Int int1 ->
      ( 
      match val2 with
      | Int int2 -> if int1 < int2 then (Bool true) else (Bool false)
      | _ -> raise (TypeError ("Expected val2 to be of type Int"))  
      )
    | _ -> raise (TypeError ("Expected val1 to be of type Int")) 
    )

  | Binop(LessEqual, expr1, expr2) -> 
    let val1 = eval_expr env expr1 in
    let val2 = eval_expr env expr2 in
    
    (
    match val1 with
    | Int int1 -> 
      (
      match val2 with
      | Int int2 -> if int1 < int2 || int1 == int2 then (Bool true) else (Bool false)
      | _ -> raise (TypeError ("Expected val2 to be of type Int"))  
      )
    | _ -> raise (TypeError ("Expected val1 to be of type Int")) 
    )
  | Binop(Greater, expr1, expr2) -> 
    let val1 = eval_expr env expr1 in
    let val2 = eval_expr env expr2 in
    
    (
    match val1 with
    | Int int1 -> 
      (
      match val2 with
      | Int int2 -> if int1 > int2 then (Bool true) else (Bool false)
      | _ -> raise (TypeError ("Expected val2 to be of type Int"))  
      )
    | _ -> raise (TypeError ("Expected val1 to be of type Int")) 
    )
  | Binop(GreaterEqual, expr1, expr2) ->
    let val1 = eval_expr env expr1 in
    let val2 = eval_expr env expr2 in
    
    (
    match val1 with
    | Int int1 -> 
      (
      match val2 with
      | Int int2 -> if int1 > int2 || int1 == int2 then (Bool true) else (Bool false)
      | _ -> raise (TypeError ("Expected val2 to be of type Int"))  
      )
    | _ -> raise (TypeError ("Expected val1 to be of type Int")) 
    )
  | Binop(Concat, expr1, expr2) ->
    let val1 = eval_expr env expr1 in
    let val2 = eval_expr env expr2 in
    
    (
    match val1 with
    | String string1 -> 
      (
      match val2 with
      | String string2 -> String (string1 ^ string2)
      | _ -> raise (TypeError ("Expected val2 to be of type String"))  
      )
    | _ -> raise (TypeError ("Expected val1 to be of type String")) 
    )

  | Binop(Equal, expr1, expr2) -> 
    let left_side = eval_expr env expr1 in
    let right_side = eval_expr env expr2 in

    (* Check that the two sides are the same type *)
    (
    match left_side with
    | Int int1 ->
      (
        match right_side with
        | Int int2 -> if int1 = int2 then (Bool true) else (Bool false)
        | _ -> raise (TypeError("If left_side is of type Int then right side should also be of type Int"))
      )
    | Bool bool1 ->
      (
        match right_side with
        | Bool bool2 -> if bool1 = bool2 then (Bool true) else (Bool false)
        | _ -> raise (TypeError("If left_side is of type Bool then right side should also be of type Bool"))
      )
    | String string1 ->
      (
        match right_side with
        | String string2 -> if string1 = string2 then (Bool true) else (Bool false)
        | _ -> raise (TypeError("If left_side is of type String then right side should also be of type String"))
      )
    | Closure (_,_,_) -> raise (TypeError("Equal cannot be called on a closure"))
    )

    
  | Binop(NotEqual, expr1, expr2) -> 
    let left_side = eval_expr env expr1 in
    let right_side = eval_expr env expr2 in
    (
    match left_side with
    | Int int1 ->
      (
        match right_side with
        | Int int2 -> if int1 = int2 then (Bool false) else (Bool true)
        | _ -> raise (TypeError("If left_side is of type Int then right side should also be of type Int"))
      )
    | Bool bool1 ->
      (
        match right_side with
        | Bool bool2 -> if bool1 = bool2 then (Bool false) else (Bool true)
        | _ -> raise (TypeError("If left_side is of type Bool then right side should also be of type Bool"))
      )
    | String string1 ->
      (
        match right_side with
        | String string2 -> if string1 = string2 then (Bool false) else (Bool true)
        | _ -> raise (TypeError("If left_side is of type String then right side should also be of type String"))
      )
    | Closure (_,_,_) -> raise (TypeError("Equal cannot be called on a closure"))
    )
    
  | Binop(Or, expr1, expr2) -> 
    (
    match expr1 with
    | Value (Bool bool1) ->
      (
      match expr2 with
      | Value (Bool bool2) -> if bool1 || bool2 then (Bool true) else (Bool false)
      | Binop (_,_,_) -> 
        let val2 = eval_binop env expr2 in
        (
        match val2 with
        | Bool bool2 -> if bool1 || bool2 then (Bool true) else (Bool false)
        | _ -> raise (TypeError ("Expected val2 to be of type Bool"))
        )
      | _ -> raise (TypeError ("Expected expr2 to be of type Value or Binop"))
      )
    | Binop (_,_,_) -> 
      let val1 = eval_binop env expr1 in
      (
      match val1 with
        | Bool bool1 ->
          (
          match expr2 with
          | Value (Bool bool2) -> if bool1 || bool2 then (Bool true) else (Bool false)
          | Binop (_,_,_) -> 
            let val2 = eval_binop env expr2 in
            (
            match val2 with
            | Bool bool2 -> if bool1 || bool2 then (Bool true) else (Bool false)
            | _ -> raise (TypeError ("Expected val2 to be of type Bool"))
            )
          | _ -> raise (TypeError ("Expected expr2 to be of type Bool or Binop"))
          )
        | _ -> raise (TypeError ("Expected val1 to be of type Bool"))
      )
    | _ -> raise (TypeError ("Expected expr1 to be of type Value or Binop")) 
    )
    

  | Binop(And, expr1, expr2) -> 
    (
    match expr1 with
    | Value (Bool bool1) ->
      (
      match expr2 with
      | Value (Bool bool2) -> if bool1 && bool2 then (Bool true) else (Bool false)
      | Binop (_,_,_) -> 
        let val2 = eval_binop env expr2 in
        (
        match val2 with
        | Bool bool2 -> if bool1 && bool2 then (Bool true) else (Bool false)
        | _ -> raise (TypeError ("Expected val2 to be of type Bool"))
        )
      | _ -> raise (TypeError ("Expected expr2 to be of type Value or Binop"))
      )
    | Binop (_,_,_) -> 
      let val1 = eval_binop env expr1 in
      (
      match val1 with
        | Bool bool1 ->
          (
          match expr2 with
          | Value (Bool bool2) -> if bool1 && bool2 then (Bool true) else (Bool false)
          | Binop (_,_,_) -> 
            let val2 = eval_binop env expr2 in
            (
            match val2 with
            | Bool bool2 -> if bool1 && bool2 then (Bool true) else (Bool false)
            | _ -> raise (TypeError ("Expected val2 to be of type Bool"))
            )
          | _ -> raise (TypeError ("Expected expr2 to be of type Bool or Binop"))
          )
        | _ -> raise (TypeError ("Expected val1 to be of type Bool"))
      )
    | _ -> raise (TypeError ("Expected expr1 to be of type Value or Binop")) 
    )

  | _ -> raise (TypeError (Printf.sprintf "Expected %s to be of type Binop"
        (string_of_expr e)))

  and eval_if env e =
  
    match e with
    | If (guard, t_branch, f_branch) ->
      let guard_value = eval_expr env guard in
      (
      match guard_value with
      | (Bool true) -> eval_expr env t_branch
      | (Bool false) -> eval_expr env f_branch
      | _ -> raise (TypeError ("Expected guard value to evaluate to a boolean")) 
      )
    | _ -> raise (TypeError ("Expected e to be of type if"))

 and eval_let env e = 

  match e with
  | Let (name, rec_bool, init_expr, body_expr) ->
    (
    match rec_bool with
    | false ->
      let v = eval_expr env init_expr in
      let new_env = extend env name v in
      eval_expr new_env body_expr
    | true ->
     let temp_env = extend_tmp env name in
      let v = eval_expr temp_env init_expr in
      update temp_env name v;
      eval_expr temp_env body_expr
    )
  | _ -> raise (TypeError ("Expected e to be of type Let"))


and eval_fun env e = 

    match e with
    | Fun (id, expr) -> Closure (env, id, expr)
    | _ -> raise (TypeError ("Expected e to be of type Fun"))


  and eval_function_call env e = 

    match e with
    | FunctionCall(expr1, expr2) ->
      let expected_closure = eval_expr env expr1 in
      (
      match expected_closure with
      | Closure (closure_env, id, expr) ->
        let v = eval_expr env expr2 in
        let new_env = extend closure_env id v in
        eval_expr new_env expr
      | _ -> raise (TypeError ("Expected expected_closure to be of type Closure"))
      )
    | _ -> raise (TypeError ("Expected e to be of type FunctionCall"))

  
(* Part 2: Evaluating mutop directive *)

(* Evaluates MicroCaml mutop directive [m] in environment [env],
   returning a possibly updated environment paired with
   a value option; throws an exception on error *)
(*type mutop =
  | Def of var * expr
  | Expr of expr
  | NoOp *)
let eval_mutop env m = 

  match m with
  | Def (var, expr) -> 
  (* Def
  For a Def, we evaluate its expr in the given environment, but with a placeholder set for var 
  (see the discussion of recursive Let, above, for more about environment placeholders), producing value v. 
  We then update the binding for var to be v and return the extended environment, along with the value itself. *)
    let temp_env = extend_tmp env var in
    let v = eval_expr temp_env expr in
    update temp_env var v;
    (temp_env, Some v)
  | Expr expr -> 
    let eval = eval_expr env expr in
    (env, Some eval)
  | NoOp -> (env, None)
