open Printf
open Expressions
open Processes
open Subst
open Congruence
open Beta

type sort = 
  | I: sort
  | N: sort
  | B: sort
  | S: sort

let rec sort2String(s: sort): string =
  match s with
  | I -> "int"
  | N -> "nat"
  | B -> "bool"
  | S -> "string"

let printSort(s: sort): unit =
  printf "%s\n" (sort2String s)

type globalType =
  | GEnd      : globalType
  | GMessage  : (participant*participant*sort*globalType) -> globalType
  | GBranching: (participant*participant*labelGT)         -> globalType
  | GRecursive: (string*globalType)                       -> globalType
  | GVar      : string                                    -> globalType
and labelGT = (label*globalType) list   

let rec globalType2String(g: globalType): string =
  match g with
  | GEnd                 -> "g_end"
  | GMessage(p1,p2,s,g1) -> p1 ^ " -> " ^ p2 ^ ": [" ^sort2String s ^ "];"  ^ globalType2String g1
  | GBranching(p1,p2,l)  -> p1 ^ " -> " ^ p2 ^ "\n{\n  " ^ labelGT2String l ^ "\n}"
  | GRecursive(s,g1)     -> "µ" ^ s ^ "." ^ globalType2String g1
  | GVar s               -> s
and labelGT2String l =
  match l with
  | []             -> ""
  | [(lbl,g1)]   -> lbl ^ ":" ^ globalType2String g1 
  | (lbl,g1)::xs -> lbl ^ ":" ^ globalType2String g1 ^ "\n  " ^ labelGT2String xs

let printGlobalType(g: globalType): unit =
  printf "%s\n" (globalType2String g)

type localType =
  | LEnd      : localType
  | LSend     : (participant*sort*localType) -> localType
  | LReceive  : (participant*sort*localType) -> localType
  | LSelection: (participant*labelLT)        -> localType
  | LBranch   : (participant*labelLT)        -> localType
  | LVar      : label                        -> localType
  | LRecursion: (label*localType)            -> localType
and labelLT = (label*localType) list

let rec localType2String(t: localType): string =
  match t with
  | LEnd               -> "l_end"
  | LSend(par,s,t1)    -> par ^ "![" ^ sort2String s ^ "];" ^ localType2String t1
  | LReceive(par,s,t1) -> par ^ "?[" ^ sort2String s ^ "];" ^ localType2String t1
  | LSelection(par,l)  -> par ^ "⨁\n{\n" ^ labelLT2String l ^ "\n}"
  | LBranch(par,l)     -> par ^ "&\n{\n" ^ labelLT2String l ^ "\n}"
  | LVar s             -> s
  | LRecursion(s,t1)   -> "µ" ^ s ^ "." ^ localType2String t1
and labelLT2String l =
  match l with
  | []        -> ""
  | [(x,y)]   -> "  " ^ x ^ ": " ^  localType2String y
  | (x,y)::xs -> "  " ^ x ^ ": " ^  localType2String y ^ "\n" ^ labelLT2String xs

let printLocalType(s: localType): unit =
  printf "%s\n" (localType2String s)

(**)

let rec find(y: participant) (l: participant list): bool =
  match l with
  | []    -> false
  | x::xs -> if x = y then true else find y xs

let rec uniqueH(l: participant list) (acc: participant list): participant list =
  match l with
  | []    -> acc
  | x::xs -> if find x acc then uniqueH xs acc else uniqueH xs (acc @ [x])

let unique(l: participant list): participant list =
  uniqueH l []

let rec globalParticipantList2String(l: participant list): participant =
  match l with
  | []    -> ""
  | [x]   -> x
  | x::xs -> x ^ "," ^ globalParticipantList2String xs

let printGlobalParticipantList(l: participant list): unit =
  printf("[%s]\n") (globalParticipantList2String l)
    
let rec participantsGTH(g: globalType) (acc: participant list) : participant list =
  match g with
  | GEnd                 -> acc
  | GVar s               -> acc
  | GMessage(p1,p2,s,g1) -> unique(participantsGTH g1 (p1::p2::acc))
  | GBranching(p1,p2,l)  -> unique(p1::p2::labelGP l acc)
  | GRecursive(s,g1)     -> unique(participantsGTH g1 acc)
and labelGP l acc =
  match l with
  | []            -> acc
  | (lbl,g1):: xs -> (participantsGTH g1 acc) @ (labelGP xs acc)
  
let participantsGT(g: globalType): participant list =
  participantsGTH g []

(**)
let rec isLocalsSameH(l: labelLT) (m: (label*localType)): bool =
  match (l,m) with
  | ([],_)                    -> true
  | ((lbl1,l1)::xs,(mlbl,ml)) -> if l1 = ml then isLocalsSameH xs m else false

let rec isLocalsSame(l: labelLT): bool =
  match l with
  | []           -> true
  | (lbl,l1)::xs -> isLocalsSameH xs (lbl,l1) 

let rec projection(g: globalType) (r: participant): localType =
  match g with
  | GEnd                 -> LEnd
  | GVar s               -> LVar s
  | GMessage(p1,p2,s,g1) -> if p1 = r then LSend(p2,s,projection g1 r)
                            else if p2 = r then LReceive(p1,s,projection g1 r)
                            else projection g1 r
  | GBranching(p1,p2,l)  -> if p1 = r then LSelection(p2,labelLT l r)
                            else if p2 = r then LBranch(p1,labelLT l r)
                            else if p1 != r && p2 != r && isLocalsSame (labelLT l r)
                            then woLabelLT l r
                            else failwith "undefined -- branching proj 1"
  | GRecursive(s,g1)     -> if find r (participantsGT g1) = false (* && fv g = [] *)
                            then LEnd
                            else LRecursion(s,projection g1 r)
and labelLT l r =
  match l with
  | []           -> []
  | (lbl,g1)::xs -> (lbl,projection g1 r) :: labelLT xs r
and woLabelLT l r =
  match l with
  | []           -> failwith "undefined -- branching proj 2"
  | (lbl,g1)::xs -> projection g1 r 