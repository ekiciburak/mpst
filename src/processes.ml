open Printf
open Expressions

type participant = string 

let printParticipant(p: participant): unit =
  printf "%s\n" p

type label = string

(*
type process = 
  | PVar       : string                                  -> process
  | Inaction   : process
  | Send       : (participant*label*expression*process)  -> process
  | Receive    : (participant*procList)                  -> process
  | Conditional: (expression*process*process)            -> process
  | Recursion  : (string*process)                        -> process
and procList = (label*string*process) list

let rec process2String(p: process): string =
  match p with
  | Inaction             -> "0"
  | PVar s               -> s
  | Send(par,l,e,p1)     -> par ^ "!" ^ l ^ "<" ^ expression2String e ^ ">." ^ process2String p1
  | Receive(par,l)       -> par ^ "?[" ^ procList2String l ^ "]"
  | Conditional(e,p1,p2) -> "if " ^ expression2String e ^ " then " ^ process2String p1 ^ " else " ^ process2String p2
  | Recursion(s,p1)      -> "µ" ^ s ^ "." ^ process2String p1
and procList2String l =
  match l with
  | []           -> ""
  | [(l,x,y)]   -> l ^ "(" ^ x ^ ")." ^  process2String y
  | (l,x,y)::xs -> l ^ "(" ^ x ^ ")." ^  process2String y ^ procList2String xs

let printProcess(p: process): unit =
  printf "%s\n" (process2String p)

type session =
  | Par : (participant*process) -> session 
  | Comp: (session*session)     -> session

let rec session2String(s: session): string =
  match s with
  | Par(par,p)  -> par ^ "::" ^ process2String p
  | Comp(s1,s2) -> session2String s1 ^ " | " ^ session2String s2

let printSession(s: session): unit =
  printf "%s\n" (session2String s)
*)

type process = 
  | PVar       : string                              -> process
  | Inaction   : process
  | Send       : (participant*expression*process)    -> process
  | Receive    : (participant*expression*process)    -> process
  | Branch     : (participant*procList)              -> process
  | Selection  : (participant*label*process)         -> process
  | Conditional: (expression*process*process)        -> process
  | Recursion  : (string*process)                    -> process
and procList = (label*process) list

let rec process2String(p: process): string =
  match p with
  | Inaction             -> "O"
  | PVar s               -> s
  | Send(par,e,p1)       -> par ^ "'<" ^ expression2String e ^ ">." ^ process2String p1
  | Receive(par,e,p1)    -> par ^ "("  ^ expression2String e ^ ")." ^ process2String p1
  | Branch(par,l)        -> par ^ " -> \n{\n " ^ procList2String l ^ "\n}"
  | Selection(par,s,p1)  -> par ^ " <- " ^ s ^ "." ^ process2String p1
  | Conditional(e,p1,p2) -> "if " ^ expression2String e ^ " then " ^ process2String p1 ^ " else " ^ process2String p2
  | Recursion(s,p1)      -> "µ" ^ s ^ "." ^ process2String p1
and procList2String l =
  match l with
  | []        -> ""
  | [(x,y)]   -> "  " ^ x ^ ": " ^  process2String y
  | (x,y)::xs -> "  " ^ x ^ ": " ^  process2String y ^ ";\n " ^ procList2String xs

let printProcess(p: process): unit =
  printf "%s\n" (process2String p)

type session =
  | Par : (participant*process) -> session 
  | Comp: (session*session)     -> session

let rec session2String(s: session): string =
  match s with
  | Par(par,p)  -> par ^ "::" ^ process2String p
  | Comp(s1,s2) -> session2String s1 ^ " |\n" ^ session2String s2

let printSession(s: session): unit =
  printf "%s\n" (session2String s)