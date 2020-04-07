(* ####### CITATION ####### *)

(* @author Jonathan Tran 
   @date Monday April 6th 2020

   The below implementation in OCaml is completely my own work. 
   It is inspired by notes for CS 3110 that are online. *)

(* ############# PURPOSE ########## *)

(* We learned about type checking last semester in CS 3110, 
   but never got a chance to implement the full type checker. 
   For my own understanding, and to waste some time, here is the type 
   checker in its full glory *)

(* ####### TYPE CHECKING BACKGROUND AND DEFINITIONS ######## *)

(* We use the ideas presented in Professor Michael Clarkson's gitbook,chaper 9. *)

(* for example, consider ctx |- e :t , which means that ctx proves e has type t. *)
(* also, ctx[x -> t] binds x to t in ctx *)
(* We further stipulate that in any context, a variable x can only be bound inside once.  *)
(* Then expression e is well typed if there exists type t such that ctx |- e : t *)
(* Unique and existent type *)

(* ############ SimPL LANGUAGE ########### *)
(* e ::= x | i | b | e1 bop e2                
    | if e1 then e2 else e3
    | let x = e1 in e2     

   bop ::= + | * | <= *)

(* t ::= int | bool | tuple (t1, t2)*)

(*  ########## INFERENCE RULES IN SIMPL ############ *)

(* Base cases *)
(* All ints are ints, all bools are bools and if x is bound to t already, it is t
   ctx |- i : int  
   ctx |- b : bool
   {x : t, ...} |- x : t *)

(* Inductive cases (to expand language)  - hopefully self consistent *)
(* ctx |- e1 bop e2 : int iff
    bop is + or * and 
    ctx |- e1 : int and 
    ctx |- e2 : int  

    ctx |- e1 bop e2 : bool iff 
      bop is <= and 
      ctx |- e1 : int and  
      ctx |- e2 : int *)

(* ctx |- if e1 then e2 else e3 : t iff 
    ctx |- e1 : bool and 
    ctx |- e2 : t and 
    ctx |- e3 : t *)

(* ctx |- let e1 in e2 : t iff 
    ctx |- e1 : t1 and 
    ctx[e1 : t1] |- e2 : t *)

(* ctx |- (e1, e2) : t1 * t2 iff 
    ctx |- e1 : t1 *)

(* ctx |- Fst e : t1 iff 
    ctx |- e : t1 * t2 *)

(* ctx |- Snd e : t2 iff 
    ctx |- e : t1 * t2 and 
    ctx |- e2 : t2 *)

(* ctx |- match e with Left x1 -> e1 | Right x2 -> e2  : t2 iff 
    ctx |- e : Left t1 and 
    ctx[x1 : t1] |- e1 : t2 *)

(* ctx |- match e with Left x1 -> e1 | Right x2 -> e2  : t2 iff 
    ctx |- e : Right t1 and 
    ctx[x2 : t1] |- e1 : t2 *)

(* ctx |- fun x : t -> e : t1 iff 
    ctx[x : t] |- e : t1 *)

(* ctx |- e1 e2 : t2 iff 
    ctx |- e1 : t1 -> t2 and 
    ctx |- e2 : t1 *)

(* ######### IMPLEMENTATION ############ *)

type bop = 
  | Add 
  | Sub
  | Mult
  | Div
  | LT
  | GT 
  | EQ
  | LTE 
  | GTE

type typ = 
  | Integer 
  | Boolean
  | Tuple of typ * typ
  | Left of typ
  | Right of typ
  | Function of typ * typ 

type simpl = 
  | Int of int
  | Bool of bool
  | Var of string
  | Bop of bop * simpl * simpl
  | IfThenElse of simpl * simpl * simpl
  | Let of simpl * simpl * simpl
  | Tup of simpl * simpl
  | Fst of simpl
  | Snd of simpl
  | Lft of simpl 
  | Rght of simpl
  | MatchWith of simpl * simpl * simpl * simpl * simpl (* match e with Left x1 -> e1 | Right x2 -> e2 *)
  | Fun of simpl * typ * simpl (* fun x : t -> e *)
  | App of simpl * simpl

(** [check_var var_str ctx] is type t iff 
    [var_str] is bound to t in [ctx]. 

    Raises: ["Type Exception"] if [var_str] is not bound under[ctx]. *)
let check_var var_str ctx = 
  match List.assoc_opt var_str ctx with 
  | Some type_name -> type_name
  | None -> failwith "Type Exception"

(** [eval_type expr ctx] is type t iff
    [expr] is well-typed under [ctx] in SimPL under the type inferences
    rules we stated above. 

    Raises: ["Type Exception"] if [expr] is not well typed under [ctx]
    and the inferences rules. *)
let rec eval_type expr ctx = 
  match expr with 
  | Int _ -> Integer
  | Bool _ -> Boolean
  | Var v -> check_var expr ctx
  | Bop (bop, e1, e2) -> eval_bop bop e1 e2 ctx 
  | IfThenElse (e1, e2, e3) -> eval_if e1 e2 e3 ctx
  | Let (var, e1, e2) -> eval_let var e1 e2 ctx
  | Tup (e1, e2) -> eval_tuple e1 e2 ctx
  | Fst (e) -> eval_fst e ctx
  | Snd (e) -> eval_snd e ctx
  | Lft (e) -> Left (eval_type e ctx)
  | Rght (e) -> Right (eval_type e ctx)
  | MatchWith (e, v1, e1, v2, e2) -> eval_match e v1 e1 v2 e2 ctx
  | Fun (x, t, e) -> eval_fun x t e ctx
  | App (e1, e2) -> eval_app e1 e2 ctx

(** [eval_bop bop e1 e2 ctx] is is type t iff
    [e1 bop e2] is well-typed under [ctx] in SimPL under the type inferences
    rules we stated above. 

    Raises: ["Type Exception"] if [expr] is not well typed under [ctx]
    and the inferences rules. *)
and eval_bop bop e1 e2 ctx = 
  match bop with 
  | Add | Sub | Mult | Div -> begin
      let t1 = eval_type e1 ctx in 
      let t2 = eval_type e2 ctx in 
      if t1 = Integer && t2 = Integer then Integer 
      else failwith "Type Exception"
    end
  | LT | GT | LTE | GTE | EQ-> begin 
      let t1 = eval_type e1 ctx in 
      let t2 = eval_type e2 ctx in 
      if t1 = Integer && t2 = Integer then Boolean 
      else failwith "Type Exception" 
    end

(** [eval_if e1 e2 e3 ctx] is is type t iff
    [if e1 then e2 else e3] is well-typed under [ctx] in SimPL under the type inferences
    rules we stated above. 

    Raises: ["Type Exception"] if [expr] is not well typed under [ctx]
    and the inferences rules. *)
and eval_if e1 e2 e3 ctx = 
  let t1 = eval_type e1 ctx in 
  if t1 <> Boolean then failwith "Type Exception" 
  else begin
    let t2 = eval_type e2 ctx in  
    let t3 = eval_type e3 ctx in 
    if t2 <> t3 then failwith "Type Exception" 
    else t2
  end

(** [eval_let var e1 e2 ctx] is is type t iff
    [let var = e1 in e2] is well-typed under [ctx] in SimPL under the type inferences
    rules we stated above. 

    Raises: ["Type Exception"] if [expr] is not well typed under [ctx]
    and the inferences rules. *)
and eval_let var e1 e2 ctx = 
  let t1 = eval_type e1 ctx in 
  let ctx' = (var, t1) :: ctx in
  eval_type e2 ctx'

(** [eval_tuple e1 e2 ctx] is is type t1 * t2 iff
    [Tuple(e1, e2)] is well-typed under [ctx] in SimPL under the type inferences
    rules we stated above. 

    Raises: ["Type Exception"] if [expr] is not well typed under [ctx]
    and the inferences rules. *)
and eval_tuple e1 e2 ctx = 
  let t1 = eval_type e1 ctx in 
  let t2 = eval_type e2 ctx in  
  Tuple (t1, t2)

(** [eval_fst e ctx] is is type t1 iff
    [Fst Tuple(e1, e2)] is well-typed under [ctx] in SimPL under the type inferences
    rules we stated above. 

    Raises: ["Type Exception"] if [expr] is not well typed under [ctx]
    and the inferences rules. *)
and eval_fst e ctx = 
  match eval_type e ctx with 
  | Tuple (t1, t2) -> t1
  | _ -> failwith "Type Exception"

(** [eval_snd e ctx] is is type t1 iff
    [Snd Tuple(e1, e2)] is well-typed under [ctx] in SimPL under the type inferences
    rules we stated above. 

    Raises: ["Type Exception"] if [expr] is not well typed under [ctx]
    and the inferences rules. *)
and eval_snd e ctx = 
  match eval_type e ctx with 
  | Tuple (t1, t2) -> t2
  | _ -> failwith "Type Exception"

(** [eval_match e v1 e1 v2 e2 ctx] is is type t1 iff
    [match e with Left v1 -> e1 | Right v2 -> e2] is well-typed under [ctx] in SimPL under the type inferences
    rules we stated above. 

    Raises: ["Type Exception"] if [expr] is not well typed under [ctx]
    and the inferences rules. *)
and eval_match e v1 e1 v2 e2 ctx = 
  match eval_type e ctx with 
  | Left t1 -> eval_type e1 ((v1, t1) :: ctx)
  | Right t2 -> eval_type e2 ((v2, t2) :: ctx)
  | _ -> failwith "Type Exception"

(** [eval_fun x t e ctx ] is is type t1 iff
    [fun x : t -> e] is well-typed under [ctx] in SimPL under the type inferences
    rules we stated above. 

    Raises: ["Type Exception"] if [expr] is not well typed under [ctx]
    and the inferences rules. *)
and eval_fun x t e ctx = 
  Function(t, eval_type e ((x, t) :: ctx))

(** [eval_app e1 e2 ctx] is is type t1 iff
    [e1 e2] is well-typed under [ctx] in SimPL under the type inferences
    rules we stated above. 

    Raises: ["Type Exception"] if [expr] is not well typed under [ctx]
    and the inferences rules. *)
and eval_app e1 e2 ctx = 
  match eval_type e1 ctx with 
  | Function (t1, t2) -> begin
      match eval_type e2 ctx with 
      | t3 -> begin 
          if t3 = t1 then t2
          else failwith "Type Exception"
        end
    end 
  | _ -> failwith "Type Exception"

(** [check_type e] is [true] iff [e] is well typed under the empty context
    for SimPL.  *)
let check_type e = 
  match eval_type e [] with 
  | exception ex -> false
  | _ -> true