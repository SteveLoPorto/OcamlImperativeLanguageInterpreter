open Ast
exception TypeError
exception UndefinedVar
exception DivByZeroError

(* Remove shadowed bindings *)
let prune_env (env : environment) : environment =
  let binds = List.sort_uniq compare (List.map (fun (id, _) -> id) env) in
  List.map (fun e -> (e, List.assoc e env)) binds

(* Env print function to stdout *)
let print_env_std (env : environment): unit =
  List.fold_left (fun _ (var, value) ->
      match value with
        | Int_Val i -> Printf.printf "- %s => %s\n" var (string_of_int i)
        | Bool_Val b -> Printf.printf "- %s => %s\n" var (string_of_bool b)
        | Closure _ -> ()) () (prune_env env)

(* Env print function to string *)
let print_env_str (env : environment): string =
  List.fold_left (fun acc (var, value) ->
      match value with
        | Int_Val i -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_int i))
        | Bool_Val b -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_bool b))
        | Closure _ -> acc
      ) "" (prune_env env)


(***********************)
(****** Your Code ******)
(***********************)


(*Looks up most recent occurance of variable in the Enviornment *)
let rec lookup env x= 
match env with
|[] -> raise (UndefinedVar)
|(l, v)::envT -> if x = l then v else lookup envT x
;;


let extend env x v = (x,v)::env;;

(* evaluate an arithmetic expression in an environment *)
let rec eval_expr (e : exp) (env : environment) : value =
  match (e) with


  | Var x -> lookup env (x)

  | Number n -> Int_Val n

  |Plus (e1, e2) ->
      (match eval_expr e1 env, eval_expr e2 env with
	   Int_Val n1, Int_Val n2 -> Int_Val (n1 + n2)
	 | (_, _ )-> raise (TypeError))

  
  | Minus (e1,e2) ->
   (match eval_expr e1 env, eval_expr e2 env with
	  |Int_Val n1, Int_Val n2 -> Int_Val (n1 - n2)
	 | (_, _) -> raise (TypeError))

  | Times (e1,e2) -> 
      (match eval_expr e1 env, eval_expr e2 env with
	   Int_Val n1, Int_Val n2 -> Int_Val (n1 * n2)
	 | (_, _ )-> raise (TypeError))

  | Div (e1,e2)->
      (match eval_expr e1 env, eval_expr e2 env with
	   Int_Val n1, Int_Val n2 -> if (n2 = 0) then raise (DivByZeroError) else Int_Val (n1 / n2)
	 | (_, _ )-> raise (TypeError))

  | Mod (e1,e2)->
      (match eval_expr e1 env, eval_expr e2 env with
	   Int_Val n1, Int_Val n2 -> if (n2 = 0) then raise (DivByZeroError) else Int_Val (n1 mod n2)
	 | (_, _ )-> raise (TypeError))

  | Eq (e1,e2)->
      (match eval_expr e1 env, eval_expr e2 env with
	   Int_Val n1, Int_Val n2 -> if (n1 != n2) then Bool_Val false else Bool_Val true
	 | (_, _ )-> raise (TypeError))

  | Leq (e1,e2)->
      (match eval_expr e1 env, eval_expr e2 env with
	   Int_Val n1, Int_Val n2 -> if (n1 <= n2) then Bool_Val true else Bool_Val false
	 | (_, _ )-> raise (TypeError))

  | Lt (e1,e2)->
      (match eval_expr e1 env, eval_expr e2 env with
	   Int_Val n1, Int_Val n2 -> if (n1 < n2) then Bool_Val true else Bool_Val false
	 | (_, _ )-> raise (TypeError))

  | Not (e1)-> 
      (match eval_expr e1 env with
	   Bool_Val n1 -> Bool_Val (not n1)
	 | (_ )-> raise (TypeError))

  | And (e1,e2)->
      (match eval_expr e1 env, eval_expr e2 env with
	   Bool_Val n1, Bool_Val n2 -> if(n1 = true) then (if(n2 = true) then Bool_Val true else Bool_Val false) else Bool_Val false
	 | (_, _ )-> raise (TypeError))

  | Or (e1,e2)->
    (match eval_expr e1 env, eval_expr e2 env with
	   Bool_Val n1, Bool_Val n2 -> if(n1 = true) then Bool_Val true else (if(n2 = true) then Bool_Val true else Bool_Val false)
	 | (_, _ )-> raise (TypeError))

  | True -> Bool_Val true

  | False -> Bool_Val false

  | App (e1,e2) -> 
    (match eval_expr e1 env with
    |Closure(env', x, e) -> eval_expr e ((x, (eval_expr e2 env))::env') 
    |(_) -> raise (TypeError))
    (**eval_expr e ((x, eval_expr e2 env)::env') *)

  | Fun (x, e1) ->  Closure(env, x, e1);;
  

    




(* evaluate a command in an environment *)
let rec eval_command (c : com) (env : environment) : environment =
 
  match c with 
  (** Is there going to be duplicate declarations ?*)
  | Declare (t1, x) -> 
    (match t1 with
      |Int_Type -> extend env x (Int_Val 0)
      |Bool_Type -> extend env x (Bool_Val false)
      |Lambda_Type -> extend env x (Closure ([], "x", Var "x"))
    )
  | Assg (x, e1) ->
    let v1 = eval_expr e1 env in 
    let dictValue = lookup env x in 
      (match dictValue with 
      |Bool_Val z  -> (match v1 with 
                      |Bool_Val a -> extend env x v1
                      |_ -> raise (TypeError))
      |Int_Val z -> (match v1 with 
                      |Int_Val a -> extend env x v1
                      |_ -> raise (TypeError))
      |Closure (a, b, c) -> (match v1 with 
                      |Closure(_, _, _) -> extend env x v1
                      |_ -> raise (TypeError))
      )
   
  | Comp (c1, c2)-> 
    let newEnv = eval_command c1 env in
    let env2 = eval_command c2 newEnv in env2

  | Cond (e1, c1, c2)->  
    (match eval_expr e1 env with
	   |Bool_Val x -> if (x=true) then (eval_command c1 env) else (eval_command c2 env) 
	   | (_ )-> raise (TypeError))

  | While (e1, c1)-> 
    (match eval_expr e1 env with
    |Bool_Val x ->  (if (x = true) then ( let newEnv = eval_command c1 env in (eval_command (While(e1, c1)) newEnv) )
    else(env))
    |(_) -> raise (TypeError)
    )

  (** Does n have to be implemented in enviornment?*)
  | For (e1, c1)-> raise (TypeError)



  | Skip ->raise (TypeError)
;;