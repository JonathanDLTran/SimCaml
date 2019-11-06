type bop = Add | Sub | Mult | Div | And | Or | GT | LT | GEQ | LEQ | EQ

type tuple_direction = 
  | Left
  | Right

type expr = 
  | Int of int
  | Bool of bool
  | Var of string
  | Binop of bop * expr * expr
  | IfThenElse of expr * expr * expr
  | Tuple of expr * expr
  | Fst of expr
  | Snd of expr
  | Let of expr * expr * expr
  | Left of expr
  | Right of expr

(* TODO : Match statements on variant left/right *)
(* TODO : Anonymous functions *)

let rec is_value expr = 
  match expr with
  | Int _ | Bool _ -> true
  | Tuple (l, r) as t -> is_tuple_value t
  | Left e  | Right e -> is_value e
  | Binop _ | IfThenElse _ | Var _ | Let _ | Fst _ | Snd _ -> false

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

let get_var v = 
  match v with
  | Var str -> str
  | _ -> failwith "Precondition violated: v must be a variable"


(* substitution pattern should follow the basic rules: 
   let x = e1 in e2
   Eval e1 to v1 through big step
   Now bind x to v1
   Following that we can substitute v1 for all instances
   of x in e2 via the substition rule e2{v1/x}


                                          In general, substittion follows:
                                          x -> v1
                                          binop a, b -> binop a{v1/x} b{v1/x}
                                          tuple a b -> tuple a{v1/x} b{v1/x}
                                          ifthenelse a b c a{v1/x} b{v1/x} c{v1/x}
                                          and:
                                          let y (or any variable not x) = e3 in e4 - > let y = e3{v1/x} e4{v1/x}

                                          Now wheres the exception: For substititon
                                          We when e2 is itself a let expression, and 
                                          we have let x (x shadows original x) = e3 in e4 - > let x = e3{v1/x} e4 (no substitition on e4 to maintain correct shadow pattern)

                                        *)
let rec substitute v x e = 
  match e with
  | Int _ | Bool _ -> failwith "e must have a variable binding in it. "
  | Var name -> 
    if name = x then v 
    else Var name (* This case is probably not right *)
  | Binop (bop, e1, e2) -> 
    Binop (bop, substitute v x e1, substitute v x e2)
  | Tuple (e1, e2) ->
    Tuple (substitute v x e1, substitute v x e2)
  | Fst e1 -> Fst (substitute v x e1)
  | Snd e1 -> Snd (substitute v x e1)
  | IfThenElse (e1, e2, e3) ->
    IfThenElse (substitute v x e1, substitute v x e2, substitute v x e3)
  | Let (var, e1, e2) ->
    if is_var var then 
      let var_name = get_var v in 
      if var_name = x then Let (var, substitute v x e1, e2) (* shadowing case *)
      else Let (var, substitute v x e1, substitute v x e2)
    else failwith "Var is not a variable and so substition cannot occur"
  | Left e1 -> Left (substitute v x e1)
  | Right e1 -> Right (substitute v x e1)

let same_type e1 e2 = 
  match e1, e2 with
  | Int i1, Int i2 -> true
  | Bool b1, Bool b2 -> true
  | Tuple (l1, r1), Tuple (l2, r2) -> true
  | Left v1, Left v2 -> true
  | Right v1, Right v2 -> true
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
  | Fst e1 when is_value e1 -> 
    step_fst e1
  | Fst e1 -> Fst (step e1)
  | Snd e1 when is_value e1 ->
    step_snd e1
  | Snd e1 -> Snd (step e1)
  | Let (e1, e2, e3) when not (is_var e1) ->
    failwith "Let expressions must contain a variable binding. "
  | Let (e1, e2, e3) when is_value e2 && is_value e3 ->
    step_let e1 e2 e3
  | Let (e1, e2, e3) when is_value e2 ->
    Let (e1, e2, step e3) 
  | Let (e1, e2, e3) ->
    Let (e1, step e2, e3)
  | Left e1 when is_value e1 ->
    failwith "Precondition violated: cannot step value"
  | Left e1 -> Left (step e1)
  | Right e1 when is_value e1 ->
    failwith "Precondition violated: cannot step value"
  | Right e1 -> Right (step e1)

and step_bop bop e1 e2 = 
  match bop, e1, e2 with
  | Add, Int v1, Int v2 -> Int (v1 + v2)
  | Mult, Int v1, Int v2 -> Int (v1 * v2)
  | Sub, Int v1, Int v2 -> Int (v1 - v2)
  | Div, Int v1, Int v2 -> 
    if v2 = 0 then failwith "Division by 0 error"
    else Int (v1 / v2)
  | EQ, Int v1, Int v2 -> Bool (v1 = v2)
  | EQ, Bool b1, Bool b2 -> Bool (b1 = b2)
  | LEQ, Int v1, Int v2 -> Bool (v1 <= v2)
  | GEQ, Int v1, Int v2 -> Bool (v1 >= v2)
  | LT, Int v1, Int v2 -> Bool (v1 < v2)
  | GT, Int v1, Int v2 -> Bool (v1 > v2)
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
  | Int _ | Binop _ | Tuple _ | Left _ | Right _-> failwith "Guard of if statement must be boolean"
  | Var s -> failwith ("Unbound variable " ^ s)
  | IfThenElse _ | Let _ | Fst _ | Snd _  -> failwith "Precondition Violation: e1 must be a value"

and step_let e1 e2 e3 = 
  if is_var e1 then substitute e2 (get_var e1) e3
  else failwith "Var is not a variable and so substition cannot occur"

and step_fst e1 = 
  match e1 with
  | Tuple (l, r) -> l
  | _ -> failwith "Precondition violated: expression must a tuple value"

and step_snd e1 = 
  match e1 with
  | Tuple (l, r) -> r
  | _ -> failwith "Precondition violated: expression must a tuple value"

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
  | Int _ | Bool _ | Binop _ | IfThenElse _ | Let _ | Fst _ | Snd _ | Right _  | Left _->
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

let rec string_of_val e = 
  match e with
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
  | Tuple (l, r) as t -> string_of_tuple t
  | Left v -> "left of " ^ string_of_val v
  | Right v -> "left of " ^ string_of_val v
  | Binop _  | IfThenElse _ | Let _ | Fst _ | Snd _-> failwith "Incorrect evaluation"
  | Var s -> failwith ("Unbound variable " ^ s)

let interpret s = 
  s |> parse |> eval |> string_of_val