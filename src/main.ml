open Printf
open Expressions
open Processes
open Subst
open Congruence
open Beta
open Types
open Typechecking

let main: unit =
  (*
  let pCustomer =
    Send("Agency","Hawaii",Val(Bool true),
         Receive("Agency", [("quote","x",
                             Conditional(Gt(EVar "x", Val(Int 1000)),
                                         Send("Agency","reject",Val(Bool true),Inaction),
                                         Send("Agency","accept",Val(Bool true),Send("Agency","address",Val(Int 42),Receive("Agency",[("date","y",Inaction)]))))
                            )
                           ]
                )  
       )
  in 
  printProcess pCustomer;
  *)
  (*1-a*)
  let pAlice = Send("C",Val(Str "France"),
                    Receive("C",EVar "x",
                            Send("B",Val(Int 58),
                                 Branch("B",[("reject",Send("C",Val(Bool true), Inaction));
                                             ("accept",Receive("B",EVar "y",Send("C",Val(Bool false),Inaction)))])
                                ) 
                        )
                  )
  in printProcess pAlice; 
  let pBob = Receive("C",EVar "x",
                     Receive("A",EVar "y",
                             Conditional(Lt(Minus(EVar "x",EVar "y"),EVar "y"),
                                         Selection("A","accept",Send("A",Minus(EVar "x",EVar "y"),Inaction)),
                                         Selection("A","reject",Inaction)
                                        )
                            )
                    )
  in printProcess pBob;
  let pCarol = Receive("A",EVar "z",Send("A",Val(Int 100),Send("B",Val(Int 100),Receive("A",EVar "t",Inaction)))) 
  in printProcess pCarol;
  printf"-----\n";
  let s = Comp(Comp(Par("A",pAlice),Par("B",pBob)),Par("C",pCarol))
  in printSession s;
  printf"-----\n";
  let s = beta s 
  in printSession s;
  printf"-----\n";
  let s = beta s 
  in printSession s;
  printf"-----\n";
  let s = beta s 
  in printSession s;
  printf"-----\n";
  let s = beta s 
  in printSession s;
  printf"-----\n";
  let s = beta s 
  in printSession s;
  printf"-----\n";
  let s = beta s 
  in printSession s;
  printf"-----\n";
  let s = beta s 
  in printSession s;
  printf"-----\n";
  let s = beta s 
  in printSession s;
  printf"-----\n";
  let s = beta s 
  in printSession s;
  printf"-----\n";
  printf"-----\n";
  (*1-b -- skipped; easy*)
  let pAliceob = Send("Bob",Val(Int 42),Inaction) in
  printProcess pAliceob;
  printf"-----\n";
  let pBobob = Receive("Alice",EVar "x",Inaction) in
  printProcess pBobob;
  printf"-----\n";
  let pCarolob = Send("David",Val(Str "hello"),Inaction) in
  printProcess pCarolob;
  printf"-----\n";
  let pDavidob = Receive("Carol",EVar "y",Inaction) in
  printProcess pDavidob;
  printf"-----\n";
  (*1-c -- incorrect*)
  let pAlice = Send("Bob",Val(Int 42),Recursion("X",Receive("Carol",EVar "x",Send("Bob",Plus(EVar "x",Val(Int 1)),PVar "X")))) in
  printProcess pAlice;
  let pBob = Receive("Alice",EVar "x",Recursion("X",Send("Carol",Plus(EVar "x",Val(Int 1)),Receive("Alice", EVar "x",PVar "X")))) in
  printProcess pBob;
  let pCarol = Recursion("X",Receive("Bob",EVar "x",Send("Alice",Plus(EVar "x", Val(Int 1)),PVar "X"))) in
  printProcess pCarol;
  printf"-----\n";
  let s = Comp(Comp(Par("Alice",pAlice),Par("Bob",pBob)),Par("Carol",pCarol)) in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  printf"-----\n";
  (*1-d*)
  let pAlice = Send("Bob",Val(Int 42),Send("Bob",Val(Int 22),Selection("Bob","addition",Receive("Bob",EVar "x",Inaction)))) in
  printProcess pAlice;
  let pBob = Receive("Alice",EVar "x",Receive("Alice",EVar "y",Branch("Alice",[("addition",Send("Alice",Plus(EVar "x",EVar "y"),Send("Carol",Plus(EVar "x", EVar "y"),Inaction)));("subtraction",Send("Alice",Minus(EVar "x",EVar "y"),Send("Carol",Minus(EVar "x",EVar "y"),Inaction)))]))) in
  printProcess pBob;
  let pCarol = Receive("Bob",EVar "x", Inaction) in
  printProcess pCarol;
  printf"-----\n";
  let s = Comp(Comp(Par("Alice",pAlice),Par("Bob",pBob)),Par("Carol",pCarol)) in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  printf"-----\n";
  (*1-e*)
  let pAlice = Send("Bob",Val(Str "joke"),Inaction) in
  printProcess pAlice;
  let pBob = Receive("Alice",EVar "x",Selection("Carol","funny",Send("Carol",EVar "x",Inaction))) in
  printProcess pBob;
  let pCarol = Branch("Bob",[("funny",Receive("Bob",EVar "x",Inaction));("notfunny",Inaction)]) in
  printProcess pCarol;
  printf"-----\n";
  let s = Comp(Comp(Par("Alice",pAlice),Par("Bob",pBob)),Par("Carol",pCarol)) in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  printf"-----\n";
  (*2*)
  let twoa = GMessage("Alice","Bob",I,GMessage("Carol","David",S,GEnd)) in
  printGlobalType twoa;
  printf"-----\n";
  let twob = GRecursive("t",GMessage("Alice","Bob",I,GMessage("Bob","Carol",I,GMessage("Carol","Alice",I, GVar "t")))) in
  printGlobalType twob;
  printf"-----\n";   
  let twoc = GMessage("Alice","Bob",I,GMessage("Alice","Bob",I,GBranching("Alice","Bob",[("addition",GMessage("Bob","Alice",I,GMessage("Bob","Carol",I,GEnd)));("subtraction",GMessage("Bob","Alice",I,GMessage("Bob","Carol",I,GEnd)))]))) in
  printGlobalType twoc;
  printf"-----\n";   
  let twod = GMessage("Alice","Bob",S,GBranching("Bob","Carol",[("funny",GMessage("Bob","Carol",S,GEnd));("notfunny",GEnd)])) in
  printGlobalType twod;
  printf"-----\n";  
  printf"-----\n";  
  (*3-a-i*)
  let twoaa = projection twoa "Alice" in
  printLocalType twoaa;
  printf"-----\n";  
  let twoab = projection twoa "Bob" in
  printLocalType twoab;
  printf"-----\n"; 
  let twoac = projection twoa "Carol" in
  printLocalType twoac;
  printf"-----\n"; 
  let twoad = projection twoa "David" in
  printLocalType twoad;
  printf"-----\n"; 
  printf"-----\n"; 
  (*3-a-ii*)
  let twoba = projection twob "Alice" in
  printLocalType twoba;
  printf"-----\n";  
  let twobb = projection twob "Bob" in
  printLocalType twobb;
  printf"-----\n";  
  let twobc = projection twob "Carol" in
  printLocalType twobc;
  printf"-----\n";  
  printf"-----\n"; 
  (*3-a-iii*)
  let twoca = projection twoc "Alice" in
  printLocalType twoca;
  printf"-----\n"; 
  let twocb = projection twoc "Bob" in
  printLocalType twocb;
  printf"-----\n"; 
  let twocc = projection twoc "Carol" in
  printLocalType twocc;
  printf"-----\n"; 
  printf"-----\n"; 
  (*3-a-iv*)
  let twoda = projection twod "Alice" in
  printLocalType twoda;
  printf"-----\n"; 
  let twodb = projection twod "Bob" in
  printLocalType twodb;
  printf"-----\n"; 
  let twodc = projection twod "Carol" in
  printLocalType twodc;
  printf"-----\n"; 
  printf"-----\n"; 
  (*3-b*)
  let threeb = GBranching("A","B",[("apples",GMessage("B","C",I,GMessage("C","A",S,GEnd)));("pears",GMessage("B","C",S,GMessage("C","A",I,GEnd)))]) in
  printGlobalType threeb;
  let threeba = projection threeb "A" in
  printLocalType threeba;
  printf"-----\n";
  let threebb = projection threeb "B" in
  printLocalType threebb;
  printf"-----\n";  
  (*undefined failure works here*)
  (*
  let threebc = projection threeb "C" in
  printLocalType threebc;
  printf"-----\n"; 
  *)
  printf"-----\n"; 
  let threec = GBranching("A","B",[("apples",GMessage("B","C",I,GMessage("C","A",S,GEnd)));("pears",GMessage("C","A",S,GMessage("B","C",I,GEnd)))]) in
  printGlobalType threec;
  let threeca = projection threec "A" in
  printLocalType threeca;
  printf"-----\n";
  let threecb = projection threec "B" in
  printLocalType threecb;
  printf"-----\n"; 
  (*undefined failure works here*)
  (*
  let threecc = projection threec "C" in
  printLocalType threecc;
  printf"-----\n"; 
  *) 
  printf"-----\n"; 
  let threed = GBranching("A","B",[("apples",GMessage("B","D",I,GMessage("C","A",S,GEnd)));("pears",GMessage("C","A",S,GMessage("B","D",I,GEnd)))]) in
  printGlobalType threed;
  let threeda = projection threed "A" in
  printLocalType threeda;
  printf"-----\n";
  let threedb = projection threed "B" in
  printLocalType threedb;
  printf"-----\n";   
  let threedc = projection threed "C" in
  printLocalType threedc;
  printf"-----\n"; 
  let threedd = projection threed "D" in
  printLocalType threedd;
  printf"-----\n";     
  printf"-----\n"; 
  let threee = GMessage("A","B",I,GRecursive("t",GBranching("B","C",[("retry",GVar "t");("finish",GEnd)]))) in
  printGlobalType threee;
  printf"-----\n"; 
  let threeea = projection threee "A" in
  printLocalType threeea;
  printf"-----\n";
  let threeeb = projection threee "B" in
  printLocalType threeeb;
  printf"-----\n";
  let threeec = projection threee "C" in
  printLocalType threeec;
  printf"-----\n";
  printf"-----\n";
  (*4+1-b*)
  let ta = typecheck Nil pAliceob in
  (
    match ta with
    | Yes ta' -> printLocalType ta'
    | No s    -> failwith s
  );
  let ta = projection twoa "Alice" in
  printLocalType ta;
  printf"-----\n";
  let tb = typecheck (ConsS("x",I,Nil)) pBobob in
  (
    match tb with
    | Yes tb' -> printLocalType tb'
    | No s    -> failwith s
  );
  let tb = projection twoa "Bob" in
  printLocalType tb;
  printf"-----\n"; 
  let tc = typecheck (ConsS("y",S,Nil)) pCarolob in
  (
    match tc with
    | Yes tc' -> printLocalType tc'
    | No s    -> failwith s
  );
  let tc = projection twoa "Carol" in
  printLocalType tc;
  printf"-----\n"; 
  let td = typecheck (ConsS("y",S,Nil)) pDavidob in
  (
    match td with
    | Yes td' -> printLocalType td'
    | No s    -> failwith s
  );
  let td = projection twoa "David" in
  printLocalType td;
  printf"-----\n"; 
  printf"-----\n"; 

  (*
  let g1 = GBranching("q","r",[("l3",GMessage("q","r",I,GEnd));("l4",GMessage("q","r",N,GEnd))]) in
  printGlobalType g1;
  printf"-----\n";
  let g  = GBranching("p","q",[("l1",GMessage("p","q",N,g1));("l2",GMessage("p","q",B,g1))]) in
  printGlobalType g;
  printf"-----\n";
  let pgp = projection g "p" in
  printLocalType pgp;
  printf"-----\n";
  let pgq = projection g "q" in
  printLocalType pgq;
  printf"-----\n";
  let pgr = projection g "r" in
  printLocalType pgr;
  printf"-----\n";
  printf"-----\n";
 
  let gt = GBranching("p","q",
                      [("yes",GMessage("q","p",I,GMessage("p","r",I,GEnd)));
                       ("no", GMessage("q","p",S,GMessage("p","r",I,GEnd))) 
                      ]
                     )
  in printGlobalType gt;
  let l = participantsGT gt in
  printGlobalParticipantList l;
  let t = GMessage("Alice",
                   "Bob",
                   I,
                   GMessage("Bob","Alice",B,GEnd) 
                  )
  in printGlobalType t;
  let lt1 = projection t "Alice" in
  printLocalType lt1;
  let ta =
    GMessage("Alice","Bob",S,
             GMessage("Bob","Alice",I,
                      GBranching("Alice","Bob",
                                 [
                                  ("accept",GMessage("Alice","Bob",S,
                                                     GMessage("Bob","Alice",S,GEnd) 
                                                    )
                                  );
                                  ("reject",GEnd)
                                 ]
                                )
                     )
            )
  in printGlobalType ta;
  let lBob = projection ta "Bob" in
  printLocalType lBob;
  let lAlice = projection ta "Alice" in
  printLocalType lAlice;
  let tab =
    GMessage("Alice","Carol",S,
             GMessage("Carol","Alice",I,
                      GMessage("Carol","Bob",I,
                               GMessage("Alice","Bob",I,
                                        GBranching("Bob","Alice",
                                                   [
                                                     ("accept",GMessage("Bob","Alice",I,GMessage("Alice","Carol",B,GEnd)));
                                                     ("reject",GMessage("Alice","Carol",B,GEnd))
                                                   ]
                                                  )
                                       )
                              )
                     )
            )
  in printGlobalType tab;
  let lAlice = projection tab "Alice" in
  printLocalType lAlice;
  let lBob = projection tab "Bob" in
  printLocalType lBob;
  let lCarol = projection tab "Carol" in
  printLocalType lCarol;
  *)
  (*
  (*4 = 1b*)
  let gt = GMessage("Alice","Bob",I,
                    GMessage("Carol","David",S,GEnd)
                   ) in
  printGlobalType gt;
  let pAlice = Send("Bob",Val(Int 42),Inaction) in
  printProcess pAlice;
  let tpAlice = typecheck (ConsS("x",I,Nil)) pAlice in
  (
    match tpAlice with
    | Yes t' -> printLocalType t'
    | No s   -> failwith s
  );
  let tpAlice = projection gt "Alice" in
  printLocalType tpAlice;
  let pBob = Receive("Alice",EVar "x",Inaction) in
  printProcess pBob;
  let tpBob = typecheck (ConsS("x",I,Nil)) pBob in
  (
    match tpBob with
    | Yes t' -> printLocalType t'
    | No s   -> failwith s
  );
  let tpBob = projection gt "Bob" in
  printLocalType tpBob;
  let pCarol = Send("David",Val(Str "hello"),Inaction) in
  printProcess pCarol;
  let tpCarol = typecheck (ConsS("x",I,Nil)) pCarol in
  (
    match tpCarol with
    | Yes t' -> printLocalType t'
    | No s   -> failwith s
  );
  let tpCarol = projection gt "Carol" in
  printLocalType tpCarol;
  let pDavid = Receive("Carol",EVar "y",Inaction) in
  printProcess pDavid;
  let tpDavid = typecheck (ConsS("x",I,ConsS("y",S,Nil))) pDavid in
  (
    match tpDavid with
    | Yes t' -> printLocalType t'
    | No s   -> failwith s
  );
  let tpDavid = projection gt "David" in
  printLocalType tpDavid;
  (*4+1e*)
  let gt = GMessage("Alice","Bob",S,
                    GBranching("Bob","Carol",
                               [
                                ("funny",GMessage("Bob","Carol",S,GEnd));
                                ("notfunny",GEnd)
                               ]
                              )
                   ) in
  printGlobalType gt;
  let pAlice = Send("Bob",Val(Str "joke"),Inaction) in
  printProcess pAlice;
  let pBob = Receive("Alice",EVar "x",
                     Selection("Carol","funny",
                               Send("Carol",EVar "x",Inaction)
                              )
                    ) in
  printProcess pBob;
  let tpBob = typecheck (ConsS("x",S,Nil)) pBob in
  (
    match tpBob with
    | Yes t' -> printLocalType t'
    | No s   -> failwith s
  );
  let tpBob = projection gt "Bob" in
  printLocalType tpBob;
  let pCarol = Branch("Bob",
                      [
                        ("funny",Receive("Bob",EVar "x",Inaction));
                        ("notfunny",Inaction)
                      ]
                     ) in
  printProcess pCarol;
  let tpCarol = typecheck (ConsS("x",S,Nil)) pCarol in
  (
    match tpCarol with
    | Yes t' -> printLocalType t'
    | No s   -> failwith s
  );
  let tpCarol = projection gt "Carol" in
  printLocalType tpCarol;
  printf"-----\n";
  printf"-----\n";
  let procAlice = Send("Bob",Val(Int 50),Receive("Carol",EVar "x",Inaction)) in
  printProcess procAlice;
  let procBob = Branch("Bob",[("l1",Receive("Alice",EVar "x",Send("Carol",Val(Int 100),Inaction)));
                              ("l2",Receive("Alice",EVar "x",Send("Carol",Val(Int 2),Inaction)))
                             ]
                      ) in
  printProcess procBob;
  let procCarol = Receive("Bob",EVar "x",Send("Alice",Plus(EVar "x",Val(Int 1)),Inaction)) in
  printProcess procCarol;
  printf"-----\n";
  let tA = typecheck (ConsS("x",I,Nil)) procAlice in
  (
    match tA with
    | Yes tA' -> printLocalType tA'
    | No s    -> failwith s
  );
  *)
  (*
  let s = Comp(Comp(Par("Alice",procAlice),Par("Bob",procBob)),Par("Carol",procCarol))
  in printSession s;
  printf"-----\n";
  let s = beta s 
  in printSession s;
  printf"-----\n";
  *)
  (*
  let r = Recursion("X",Send("Carol",
                             Plus(EVar "x", Val(Int 1)),
                             Receive("Alice",EVar "x", PVar "X")
                            )
                    ) in
  printProcess r;
  let ss = Comp(Par("Bob",r),Par("Alice",PVar "y")) in
  printSession ss;
  let ss = beta ss in
  printSession ss;
  *)


