type bop = Add | Sub | Mult | Div | And | Or 

type expr = 
  | Int of int
  | Bool of bool
  | Var of string
  | Binop of bop * expr * expr
  | IfThenElse of expr * expr * expr
  | Tuple of expr * expr
  | Let of expr * expr * expr

let rec is_value expr = 
  match expr with
  | Int _ | Bool _ -> true
  | Tuple (l, r) as t -> is_tuple_value t
  | Binop _ | IfThenElse _ | Var _ | Let _ -> false

and is_tuple_value tuple = 
  match tuple with
  | Tuple (e1 , e2) -> 
    if is_value e1 && is_value e2 then true
    else false
  | _ -> failwith "Precondition violated: Must be tuple"

let is_var v = 
  match v with
  | Var _ -> true
  | _ -> false

let same_type e1 e2 = 
  match e1, e2 with
  | Int i1, Int i2 -> true
  | Bool b1, Bool b2 -> true
  | Tuple (l1, r1), Tuple (l2, r2) -> true
  | _ -> false

(** Requires: [expr] is not a value. *)
let rec step expr = 
  match expr with
  | Int _  | Bool _ -> failwith "Precondition violated: cannot step value"
  | Var s -> failwith ("Unbound variable " ^ s)
  | Binop (bop, e1, e2) when is_value e1 && is_value e2 ->
    step_bop bop e1 e2
  | Binop (bop, e1, e2) when is_value e1 ->
    Binop (bop, e1, step e2)
  | Binop (bop, e1, e2) -> 
    Binop (bop, step e1, e2)
  | IfThenElse (e1, e2, e3) when not (is_value e1) ->
    IfThenElse (step e1, e2, e3)
  | IfThenElse (e1, e2, e3) when not (is_value e2) ->
    IfThenElse (e1, step e2, e3)
  | IfThenElse (e1, e2, e3) when not (is_value e3) ->
    IfThenElse (e1, e2, step e3)
  | IfThenElse (e1, e2, e3) ->
    step_if_then_else e1 e2 e3
  | Tuple (e1, e2) when is_value e1 && is_value e2 ->
    failwith "Precondition violated: cannot step value"
  | Tuple (e1, e2) when is_value e1 ->
    Tuple (e1, step e2)
  | Tuple (e1, e2) -> 
    Tuple (step e1, e2)
  | Let (e1, e2, e3) when is_value e2 && is_value e3 ->
    step_let e1 e2 e3
  | Let (e1, e2, e3) when is_value e2 ->
    Let (e1, e2, step e3) 
  | Let (e1, e2, e3) ->
    Let (e1, step e2, e3)

and step_bop bop e1 e2 = 
  match bop, e1, e2 with
  | Add, Int v1, Int v2 -> Int (v1 + v2)
  | Mult, Int v1, Int v2 -> Int (v1 * v2)
  | Sub, Int v1, Int v2 -> Int (v1 - v2)
  | Div, Int v1, Int v2 -> 
    if v2 = 0 then failwith "Division by 0 error"
    else Int (v1 / v2)
  | And, Bool b1, Bool b2 -> Bool (b1 && b2)
  | Or, Bool b1, Bool b2 -> Bool (b1 || b2)
  | _ -> failwith "operator value mismatch"

and step_if_then_else e1 e2 e3 = 
  match e1 with
  | Bool true -> 
    if same_type e2 e3 then e2 
    else failwith "If statement branches must have same type"
  | Bool false ->
    if same_type e2 e3 then e3
    else failwith "If statement branches must have same type"
  | Int _ | Binop _ | Tuple _-> failwith "Guard of if statement must be boolean"
  | Var s -> failwith ("Unbound variable " ^ s)
  | IfThenElse _ | Let _ -> failwith "Precondition Violation: e1 must be a value"

and step_let e1 e2 e3 = 
  failwith "Unimplemented"

let rec eval expr = 
  if is_value expr then expr 
  else expr |> step |> eval

let parse s = 
  failwith "Unimplemented"

(* need the Lexer module and the Parser module by YACC *)
  (*
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast
  *)

let rec string_of_tuple t = 
  match t with
  | Int _ | Bool _ | Binop _ | IfThenElse _ | Let _->
    failwith "Precondition violated: t must be a tuple. "
  | Var s -> failwith ("Unbound variable " ^ s)
  | Tuple (l, r) -> 
    match l, r with 
    | Int i1, Int i2 -> 
      "(" ^ string_of_int i1 ^ " , " ^ string_of_int i2 ^ ")"
    | Int i, Bool b ->
      "(" ^ string_of_int i ^ " , " ^ string_of_bool b ^ ")"
    | Bool b, Int i ->
      "(" ^ string_of_bool b ^ " , " ^ string_of_int i ^ ")"
    | Bool b1, Bool b2 ->
      "(" ^ string_of_bool b1 ^ " , " ^ string_of_bool b2 ^ ")"
    | Int i, Tuple (li, ri) ->
      "(" ^ string_of_int i ^ " , " ^ string_of_tuple (Tuple (li, ri))  ^ ")"
    | Tuple (li, ri), Int i ->
      "(" ^ string_of_tuple (Tuple (li, ri))  ^ " , " ^ string_of_int i ^ ")"
    | Bool b, Tuple (li, ri) ->
      "(" ^ string_of_bool b ^ " , " ^ string_of_tuple (Tuple (li, ri))  ^ ")"
    | Tuple (li, ri), Bool b ->
      "(" ^ string_of_tuple (Tuple (li, ri))  ^ " , " ^ string_of_bool b ^ ")"
    | Tuple (l1, r1), Tuple (l2, r2) ->
      "(" ^ string_of_tuple (Tuple (l1, r1))  ^ 
      " , " ^ string_of_tuple (Tuple (l2, r2)) ^ ")"
    | _ -> failwith "Precondition violated: Tuples must contain values inside"

let string_of_val e = 
  match e with
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
  | Tuple (l, r) as t -> string_of_tuple t
  | Binop _  | IfThenElse _ | Let _-> failwith "Incorrect evaluation"
  | Var s -> failwith ("Unbound variable " ^ s)

let interpret s = 
  s |> parse |> eval |> string_of_val