(* This work is based fully and primarily on the textbook developed
   by Professor Michael Clarkson at Cornell University. It was not an
   assignment and was done for fun. *)

type bop = Add | Sub | Mult | Div | And | Or | GT | LT | GEQ | LEQ | EQ | Mod | Exp | Rem 

type unop = Neg | Pos | Abs | Not | Incr | Decr | Int_to_Bool | Bool_to_Int | Rand_Int | Ignore

type expr = 
  | Unit of unit
  | Int of int
  | Bool of bool
  | Var of string
  | Unop of unop * expr
  | Binop of bop * expr * expr
  | IfThenElse of expr * expr * expr
  | Tuple of expr * expr
  | Fst of expr
  | Snd of expr
  | Let of expr * expr * expr
  | Left of expr
  | Right of expr
  | MatchWith of expr * expr * expr * expr * expr
  | Fun of expr * expr
  | Apply of expr * expr

let gensym =
  let counter = ref 0 in
  fun () -> incr counter; "$x" ^ string_of_int !counter

(* [exp a b acc] is [a^b] , or exponentiation. In SimCaml, exponentiation
   is treated as a basic operation that a CPU can do, even though
   exponentiation is not a basic ALU process. 
   Tail recursive.
   Not optimized to work in logarithmic time. *)
let rec exp a b acc = 
  match b with
  | 0 -> a
  | n when n < 0 -> 0 (* integer raised to one over power or higher is 0 in integer *)
  | n ->
    exp a (b - 1) (acc * a)

(* [rem a b] is the remainder when [b] is divided by [a]. *)
let rem a b = 
  b - a * (b mod a)

let rec is_value expr = 
  match expr with
  | Int _ | Bool _  | Fun _ | Unit _-> true
  | Tuple (l, r) as t -> is_tuple_value t
  | Left e  | Right e -> is_value e
  | Binop _ | Unop _ | IfThenElse _ | Var _ | Let _ | Fst _ | Snd _  | MatchWith _ | Apply _-> false

and is_tuple_value tuple = 
  match tuple with
  | Tuple (e1 , e2) -> 
    if is_value e1 && is_value e2 then true
    else false
  | _ -> failwith "Precondition Violation : Must be tuple"

let is_var v = 
  match v with
  | Var _ -> true
  | _ -> false

let get_var_name v = 
  match v with
  | Var s -> s
  | _ -> failwith "v was not a variable."

let rec replace var expr = 
  match expr with
  | Var _ -> var
  | Unit _ | Int _ | Bool _ -> expr
  | Unop (unop, e) -> Unop (unop, replace var e)
  | Binop (bop, e1, e2) -> Binop (bop, replace var e1, replace var e2)
  | IfThenElse (e1, e2, e3) -> IfThenElse (replace var e1, replace var e2, replace var e3)
  | Tuple (e1, e2) -> Tuple (replace var e1, replace var e2)
  | Fst e1 -> Fst (replace var e1)
  | Snd e1 -> Snd (replace var e1)
  | Let (e1, e2, e3) -> Let (replace var e1, replace var e2, replace var e3)
  | Left e1 -> Left (replace var e1)
  | Right e1 -> Right (replace var e1)
  | MatchWith (e1, s1, e2, s2, e3) -> MatchWith (replace var e1, replace var s1, replace var e2, replace var s2, replace var e3)
  | Fun (e1, e2) -> Fun (replace var e1, replace var e2)
  | Apply (e1, e2) -> Apply (replace var e1, replace var e2)

let rec free_variables expr = 
  match expr with 
  | Unit u -> []
  | Int i -> []
  | Bool b -> []
  | Var x -> [x]
  | Binop (binop, e1, e2) ->
    free_variables e1 @ free_variables e2
  | Unop (unop, e1) ->
    free_variables e1
  | Tuple (e1, e2) ->
    free_variables e1 @ free_variables e2
  | Fst e1 -> free_variables e1
  | Snd e1 -> free_variables e1
  | Left e1 -> free_variables e1
  | Right e1 -> free_variables e1
  | MatchWith (e1, s1, e2, s2, e3) ->
    free_variables e1 @ 
    List.filter (fun elt -> elt <> get_var_name s1) (free_variables e2) @
    List.filter (fun elt -> elt <> get_var_name s2) (free_variables e3)
  | Apply (e1, e2) -> 
    free_variables e1 @ free_variables e2
  | Fun (x, e) -> 
    let arg = (match x with
        | Var s -> s
        | _ -> failwith "function argument must be string") in
    List.filter (fun elt -> elt <> arg) (free_variables e)
  | IfThenElse (e1, e2, e3) ->
    free_variables e1 @ free_variables e2 @ free_variables e3
  | Let (var, e1, e2) ->
    free_variables e1 @ 
    List.filter (fun elt -> elt <> get_var_name var) (free_variables e2)

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
  | Int _ | Bool _ | Unit _-> failwith "e must have a variable binding in it. "
  | Var name as n -> 
    if n = x then v 
    else n (* This case is probably not right *)
  | Binop (bop, e1, e2) -> 
    Binop (bop, substitute v x e1, substitute v x e2)
  | Unop (unop, e1) ->
    Unop (unop, substitute v x e1)
  | Tuple (e1, e2) ->
    Tuple (substitute v x e1, substitute v x e2)
  | Fst e1 -> Fst (substitute v x e1)
  | Snd e1 -> Snd (substitute v x e1)
  | IfThenElse (e1, e2, e3) ->
    IfThenElse (substitute v x e1, substitute v x e2, substitute v x e3)
  | Let (var, e1, e2) ->
    if is_var var then 
      if var = x then Let (var, substitute v x e1, e2)
      else Let (var, substitute v x e1, substitute v x e2)
    else failwith "Precondition Violation : var must be a variable."
  | Left e1 -> Left (substitute v x e1)
  | Right e1 -> Right (substitute v x e1)
  | MatchWith (e1, s1, e2, s2, e3) ->
    let var_set = [get_var_name s1] @ [get_var_name s2] in 
    let free_vars = free_variables v in
    if List.for_all (fun elt -> List.mem elt free_vars) var_set then MatchWith (substitute v x e1, s1, substitute v x e2, s2, substitute v x e3)
    else if List.mem (get_var_name s2) free_vars then MatchWith (substitute v x e1, s1, e2, s2, substitute v x e3)
    else if List.mem (get_var_name s1) free_vars then MatchWith (substitute v x e1, s1, substitute v x e2, s2, e3)
    else MatchWith (substitute v x e1, s1, e2, s2, e3)
  | Fun (var, e') ->
    if x = var then Fun (var, e')
    else 
      let string_var = (match x with
          | Var s -> s
          | _ -> failwith "function argument must be string") in
      if not (List.mem string_var (free_variables e')) then Fun (var, substitute v x e')
      else let new_var = Var (gensym ()) in 
        Fun (new_var, substitute v x (replace new_var e') )
  | Apply (e1, e2) ->
    Apply (substitute v x e1, substitute v x e2)

(* same type can be relagated to a type checker to do instead *)
(*
let rec same_type e1 e2 = 
  match e1, e2 with
  | Int i1, Int i2 -> true
  | Bool b1, Bool b2 -> true
  | Tuple (l1, r1), Tuple (l2, r2) -> true
  | Left v1, Left v2 -> same_type v1 v2
  | Right v1, Right v2 -> same_type v1 v2
  | Right v1, Left v2 -> same_type v1 v2
  | Left v1, Right v2 -> same_type v1 v2
  | _ -> false
*)

(** Requires: [expr] is not a value. *)
let rec step expr = 
  match expr with
  | Int _  | Bool _ | Unit _ | Fun _-> failwith "Precondition violated: cannot step value"
  | Var s -> failwith ("Unbound variable " ^ s)
  | Binop (bop, e1, e2) when is_value e1 && is_value e2 ->
    step_bop bop e1 e2
  | Binop (bop, e1, e2) when is_value e1 ->
    Binop (bop, e1, step e2)
  | Binop (bop, e1, e2) -> 
    Binop (bop, step e1, e2)
  | Unop (unop, e1) when is_value e1 ->
    step_unop unop e1
  | Unop (unop, e1) ->
    Unop (unop, step e1)
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
  | MatchWith (e1, s1, e2, s2, e3) when not (is_value e1) ->
    MatchWith (step e1, s1, e2, s2, e3)
  | MatchWith (e1, s1, e2, s2, e3) ->
    step_match_with e1 s1 e2 s2 e3
  | Apply (e1, e2) when not (is_value e1)->
    Apply (step e1, e2)
  | Apply (e1, e2) when not (is_value e2) ->
    Apply (e1, step e2)
  | Apply (e1, e2) ->
    step_apply e1 e2

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
  | Mod, Int v1, Int v2 -> Int (v1 mod v2)
  | Exp, Int v1, Int v2 -> Int (exp v1 v2 1)
  | Rem, Int v1, Int v2 -> Int (rem v1 v2)
  | _ -> failwith "operator value mismatch"

and step_unop unop e1 = 
  match unop, e1 with
  | Neg, Int i -> Int (~- i)
  | Pos, Int i | Abs, Int i -> Int (~+ i)
  | Not, Bool b -> Bool (not b)
  | Incr, Int i -> Int (i + 1)
  | Decr, Int i -> Int (i - 1)
  | Int_to_Bool, Int i -> 
    if i <= 0 then Bool false else Bool true
  | Bool_to_Int, Bool b ->
    if b = true then Int 1 else Int 0
  | Rand_Int, Unit _ -> 
    Int (Random.int 10000000000)
  | Ignore, _ -> Unit ()
  | _ -> failwith "Operator value mismatch"

and step_if_then_else e1 e2 e3 = 
  match e1 with
  | Bool true -> e2
  (*
    if same_type e2 e3 then e2 
    else failwith "If statement branches must have same type" *)
  (* I push back type checking into its own module, to parse the ast before interpreation*)
  | Bool false -> e3
    (*
    if same_type e2 e3 then e3
      else failwith "If statement branches must have same type"*)
  (* I push back type checking into its own module, to parse the ast before interpreation*)
  | Int _ | Tuple _ | Left _ | Right _ | Fun _ | Unit _-> 
    failwith "Type Error : Guard of if statement must be boolean"
  | Var s -> failwith ("Unbound variable " ^ s)
  | Binop _| Unop _ | IfThenElse _ | Let _ | Fst _ | Snd _  | MatchWith _ | Apply _ ->
    failwith "Precondition Violation : e1 must be a value"

and step_let e1 e2 e3 = 
  if is_var e1 then substitute e2 e1 e3
  else failwith "Precondition Violation : e1 must be a variable."

and step_fst e1 = 
  match e1 with
  | Tuple (l, r) -> l
  | _ -> failwith "Precondition Violation: expression must a tuple value"

and step_snd e1 = 
  match e1 with
  | Tuple (l, r) -> r
  | _ -> failwith "Precondition Violation: expression must a tuple value"

and step_match_with e1 s1 e2 s2 e3 = 
  match e1 with
  | Left v -> substitute v s1 e2
  | Right v -> substitute v s2 e3
  | _ -> 
    failwith "Match error: Match with can only match on left and right constructors. "

and step_apply e1 e2 = 
  match e1, e2 with
  | Fun (arg, e), v2 -> substitute v2 arg e
  | _ -> failwith "Application Error : Only functions can be applied to values. "

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

let rec string_of_val e = 
  match e with
  | Unit u -> "()"
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
  | Tuple (l, r) -> "(" ^ string_of_val l ^ " , " ^ string_of_val r ^ ")"
  | Left v -> "Left of (" ^ string_of_val v ^ ")"
  | Right v -> "Right of (" ^ string_of_val v ^ ")"
  | Fun (var, expr) -> "<SimCaml function>"
  | Binop _ | Unop _ | IfThenElse _ | Let _ | Fst _ | Snd _ | MatchWith _ | Apply _-> 
    failwith "Precondition Violation : Incorrect evaluation"
  | Var s -> failwith ("Unbound variable " ^ s)

let interpret s = 
  s |> parse |> eval |> string_of_val