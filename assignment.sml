(* F29FA - Foundations 1
   Class Assignment 2016
   Author: Ronan Smith
*)

(* Datatype definitions for IEXP and LEXP. *)
datatype IEXP = APPL of IEXP * IEXP | ABS of string * IEXP | VAR of string;
datatype LEXP =  APP of LEXP * LEXP | LAM of string *  LEXP |  ID of string;


(* From data-files.sml *)
(* checks whether a variable is free in a term *)

fun free id1 (ID id2) = if (id1 = id2) then true else false|
    free id1 (APP(e1,e2))= (free id1 e1) orelse (free id1 e2) |
    free id1 (LAM(id2, e1)) = if (id1 = id2) then false else (free id1 e1);

(* finds new variables which are fresh  in l and different from id*)

fun findme id l = (let val id1 = id^"1"  in if not (List.exists (fn x => id1 = x) l) then id1 else (findme id1 l) end);


(* finds the list of free variables in a term *)

fun freeVars (ID id2)       = [id2]
  | freeVars (APP(e1,e2))   = freeVars e1 @ freeVars e2
  | freeVars (LAM(id2, e1)) = List.filter (fn x => not (x = id2)) (freeVars e1);


(*does substitution avoiding the capture of free variables*)

fun subs e id (ID id1) =  if id = id1 then e else (ID id1) |
    subs e id (APP(e1,e2)) = APP(subs e id e1, subs e id e2)|
    subs e id (LAM(id1,e1)) = (if id = id1 then LAM(id1,e1) else
                                   if (not (free id e1) orelse not (free id1 e))
				                                then LAM(id1,subs e id e1)
                                   else (let val id2 = (findme id ([id1]@ (freeVars e) @ (freeVars e1)))
					 in LAM(id2, subs e id (subs (ID id2) id1 e1)) end));





(*Prints a term*)
fun printLEXP (ID v) =
    (print v;
     print " ")
  | printLEXP (LAM (v,e)) =
    (print "(\\";
     print v;
     print ".";
     printLEXP e;
     print ")")
  | printLEXP (APP(e1,e2)) =
    (print "(";
     printLEXP e1;
     print " ";
     printLEXP e2;
     print ")");

(*Finds a beta redex*)
fun is_redex (APP(LAM(_,_),_)) =
      true
  | is_redex _ =
      false;

fun is_var (ID id) =  true |
    is_var _ = false;


(*the function below adds lambda id to a list of terms *)
fun addlam id [] = [] |
    addlam id (e::l) = (LAM(id,e))::(addlam id l);

(*similar to above but adds app backward *)
fun addbackapp [] e2 = []|
    addbackapp (e1::l) e2 = (APP(e1,e2)):: (addbackapp l e2);

(*similar to above but adds app forward *)
fun addfrontapp e1 [] = []|
    addfrontapp e1  (e2::l) = (APP(e1,e2)):: (addfrontapp e1 l);

(*prints elements from a list putting an arrow in between*)
fun printlistreduce [] = ()|
    printlistreduce (e::[]) = (printLEXP e) |
    printlistreduce (e::l) = (printLEXP e; print "-->\n" ; (printlistreduce l));

fun debuglist n l = (print n; print ": "; printlistreduce l; print "\n");

(*beta-reduces a redex*)

fun red (APP(LAM(id,e1),e2)) = subs e2 id e1;

(*reduces a term to normal form using the m-strategy in which the contracted redex is:
 m(AB) = m(A) if m(A) is defined
 m(AB) = m(B) if m(A) undefined and m(B) defined
 m(AB) = AB if m(A) undefined and m(B) undefined and AB redex
 m(AB) = undefined
 m(\v.A) = m(A)
 m(v) = undefined *)
fun mreduce (ID id) =  [(ID id)] |
    mreduce (LAM(id,e)) = (addlam id (mreduce e)) |
    mreduce (APP(e1,e2)) = (let val l1 = (mreduce e1)
				val l2 = (mreduce e2)
				val l3 = (addbackapp l1 e2)
				val l4 = (addfrontapp (List.last l1) l2)
				val l5 = (List.last l4)
				val l6 =  if (is_redex l5) then (mreduce (red l5)) else [l5]
			    in l3 @ l4 @ l6
			    end);


(*printmreduce first m-reduces the term giving the list of all intermediary
terms and then prints this list separating intermediary terms with -->*)
fun printmreduce e = (let val tmp =  (mreduce e)
          		          in printlistreduce tmp end);

fun has_redex (ID id) = false |
    has_redex (LAM(id,e)) = has_redex e|
    has_redex (APP(e1,e2)) = if (is_redex  (APP(e1,e2))) then true else
                              ((has_redex e1) orelse (has_redex e2));

fun one_rireduce (ID id) = (ID id)|
    one_rireduce (LAM(id,e)) = LAM(id, (one_rireduce e))|
    one_rireduce (APP(e1,e2)) = if (has_redex e2) then (APP(e1, (one_rireduce e2))) else
                                if (is_redex (APP(e1,e2))) then (red (APP(e1,e2))) else
                                          if (has_redex e1) then (APP((one_rireduce e1), e2)) else
                                              (APP(e1,e2));



fun rireduce (ID id) =  [(ID id)] |
    rireduce (LAM(id,e)) = (addlam id (rireduce e)) |
    rireduce (APP(e1,e2)) = (let  val l1 = (rireduce e2)
				                          val e3 = (List.last l1)
                                  val l2 = (addfrontapp e1 l1)
				                          val e4 = (APP(e1,e3))
                                  val l3 =  if (is_redex e4) then (rireduce (red e4)) else
					                            if is_var(e1) then [e4] else
					                                 (rireduce (APP(one_rireduce e1, e3)))
			                                        in l2 @ l3
                                                end);


fun printrireduce e = (let val tmp =  (rireduce e)
		      in printlistreduce tmp end);

fun one_loreduce (ID id) = (ID id)|
    one_loreduce (LAM(id,e)) = LAM(id, (one_loreduce e))|
    one_loreduce (APP(e1,e2)) = if (is_redex (APP(e1,e2))) then (red (APP(e1,e2))) else
                                 if (has_redex e1) then APP(one_loreduce e1, e2) else
                                 if (has_redex e2) then APP(e1, (one_loreduce e2)) else (APP(e1,e2));


fun loreduce (ID id) =  [(ID id)] |
    loreduce (LAM(id,e)) = (addlam id (loreduce e)) |
    loreduce (APP(e1,e2)) = (let val l1 = if (is_redex (APP(e1,e2))) then  (loreduce (red (APP(e1,e2)))) else
				 if (has_redex e1) then (loreduce (APP(one_loreduce e1, e2))) else
				 if (has_redex e2) then  (loreduce (APP(e1, (one_loreduce e2)))) else []
				 in [APP(e1,e2)]@l1
			      end);


fun printloreduce e = (let val tmp =  (loreduce e)
		      in printlistreduce tmp end);

findme  "x" ["x", "x1", "x11", "x111"];
(* ----------------------------------------------------------------------------*)

(* My IEXP Functions *)
(* Ifree - Checks whether a variable is free in a term *)
fun Ifree var1 (VAR var2) = if (var1 = var2) then true else false
  | Ifree var1 (APPL(left,right)) = (Ifree var1 left) orelse (Ifree var1 right)
  | Ifree var1 (ABS(var2,body)) = if (var1 = var2) then false else (Ifree var1 body);

(* Finds new variables which are fresh in l and different from var *)
fun Ifindme var l = (let val var1 = var^"1"  in if not (List.exists (fn x => var1 = x) l) then var1 else (Ifindme var1 l) end);

(* Find the list of free variables in an IEXP term. *)
fun IfreeVars (VAR var2) = [var2]
  | IfreeVars (APPL(e1,e2)) = IfreeVars e1 @ IfreeVars e2
  | IfreeVars (ABS(var2,e1)) = List.filter (fn x => not (x = var2)) (IfreeVars e1);

(* Does substitution avoiding the capture of free variables. *)

fun Isubs e var (VAR var1)       = if var = var1 then e else (VAR var1)
  | Isubs e var (APPL(e1,e2))    = APPL(Isubs e var e1, Isubs e var e2)
  | Isubs e var (ABS(var1, e1))  = (if var = var1 then ABS(var1,e1) else
                                    if(not (Ifree var e1) orelse not (Ifree var1 e))
                                      then ABS(var1, Isubs e var e1)
                                        else (let val var2 = (Ifindme var ([var1] @ (IfreeVars e) @ (IfreeVars e1)))
                                          in ABS(var2, Isubs e var (Isubs (VAR var2) var1 e1)) end));

(* Adds lambda (abstraction - ABS) id to a list of terms *)
fun Iaddlam id [] = []
  | Iaddlam id (e::l) = (ABS(id,e))::(Iaddlam id l);

(* Adds an application (APPL) backward. *)
fun Iaddbackapp [] e2 = []
  | Iaddbackapp (e1::l) e2 = (APPL(e1,e2)) :: (Iaddbackapp l e2);


(* Adds an application (APPL) forward. *)
fun Iaddfrontapp e1 [] = []
  | Iaddfrontapp e1  (e2::l) = (APPL(e1,e2)):: (Iaddfrontapp e1 l);

(* Task 2. Translate an expression from the type LEXP to the type IEXP.
    Change name to fun ClassicalItem. *)
fun ClassicalItem (ID v) = (VAR v)
 |  ClassicalItem (APP(e1, e2)) = (APPL(ClassicalItem e1, ClassicalItem e2))
 |  ClassicalItem (LAM(id, e)) = (ABS(id, ClassicalItem e));


(* Task 3. Translate a term from the type IEXP to LEXP.
    Change name to fun ItemClassical. *)
fun ItemClassical (VAR v) = (ID v)
  | ItemClassical (APPL(e1, e2)) = (APP(ItemClassical e1, ItemClassical e2))
  | ItemClassical (ABS(id, e)) = (LAM(id, ItemClassical e));

(* Prints an IEXP term in the form M'. *)
fun printIEXP (VAR v) =
    ( print "";
      print v;
      print "" )
  | printIEXP (ABS (v,a)) =
    ( print "[";
      print v;
      print "]";
      printIEXP a )
  | printIEXP (APPL(a, b)) =
    ( print "<";
      printIEXP b;
      print ">";
      print "";
      printIEXP a;
      print "");

(* Prints elements from a list with an arrow in between (IEXP). *)
fun Iprintlistreduce [] = ()
  | Iprintlistreduce (e::[]) = (printIEXP e)
  | Iprintlistreduce (e::l)  = (printIEXP e; print "-->\n" ; (Iprintlistreduce l));

(*prints elements from a list putting an arrow in between (LEXP). *)
fun printlistreduce [] = ()|
    printlistreduce (e::[]) = (printLEXP e) |
    printlistreduce (e::l) = (printLEXP e; print "-->\n" ; (printlistreduce l));

fun debuglist n l = (print n; print ": "; Iprintlistreduce l; print "\n");

fun Ired (APPL(ABS(id,e1),e2)) = Isubs e2 id e1;

(*Finds a beta redex*)
fun Iis_redex (APPL(ABS(_,_),_)) =
    true
  | Iis_redex _ =
    false;

(* Is the value a variable? *)
fun Iis_var (VAR v) =  true |
    Iis_var _ = false;

(* Does the expression have a Beta-redex? *)
fun Ihas_redex (VAR v) = false
  | Ihas_redex (ABS(id, e)) = Ihas_redex e
  | Ihas_redex (APPL(e1,e2)) = if (Iis_redex(APPL(e1,e2)))
      then true else
        ((Ihas_redex e1) orelse (Ihas_redex e2));


(* Reduces a term to normal form, without repeated lines.
   To solve this problem I used the code from Lecture 5 as reference. *)
fun Imreduce (VAR v)        = [(VAR v)]
  | Imreduce (ABS(id,e))    = (Iaddlam id (Imreduce e))
  | Imreduce (APPL(e1,e2))  = (let val l1 = if(Ihas_redex e1) then (Imreduce e1) else [e1]
                                   val e3 = (List.last l1)
                                   val l2 = if(Ihas_redex e2) then (Imreduce e2) else [e2]
                                   val e4 = (List.last l2)
                                   val l3 = (Iaddfrontapp e3 l2)
                                   val l4 = (Iaddbackapp l1 e2)
                                   val l5 = l4 @ (List.tl l3)
                                    in if (Iis_redex (APPL(e3,e4))) then
                                    l5 @ (Imreduce(Ired(APPL(e3,e4)))) else l5 end);

fun Iprintmreduce e = (let val tmp =  (Imreduce e)
            in Iprintlistreduce tmp end);


fun Ione_rireduce (VAR v)       = (VAR v)
  | Ione_rireduce (ABS(id,e))   = ABS(id, (Ione_rireduce e))
  | Ione_rireduce (APPL(e1,e2)) = if (Ihas_redex e2) then (Ired(APPL(e1,e2))) else
                                    if (Iis_redex (APPL(e1,e2))) then (Ired (APPL(e1,e2))) else
                                      if (Ihas_redex e1) then (APPL((Ione_rireduce e1), e2)) else
                                        (APPL(e1,e2));

fun Irireduce (VAR v)          = [(VAR v)]
  | Irireduce (ABS(id,e))      = (Iaddlam id (Irireduce e))
  | Irireduce (APPL(e1,e2))    = (let val l1 = (Irireduce e2)
                                      val e3 = (List.last l1)
                                      val l2 = (Iaddfrontapp e1 l1)
                                      val e4 = (APPL(e1,e3))
                                      val l3 = if(Iis_redex e4) then (Irireduce (Ired e4)) else
                                        if (Iis_var e1) then [e4] else
                                          (Irireduce (APPL(Ione_rireduce e1, e3)))
                                              in l2 @ l3 end);

fun Iprintrireduce e = (let val tmp = (Irireduce e)
                          in Iprintlistreduce tmp end);

fun Ione_loreduce (VAR v)       = (VAR v)
  | Ione_loreduce (ABS(id,e))   = ABS(id,(Ione_loreduce e))
  | Ione_loreduce (APPL(e1,e2)) = if (Iis_redex (APPL(e1,e2))) then (Ired (APPL(e1,e2))) else
                                    if (Ihas_redex e1) then APPL(Ione_loreduce e1, e2) else
                                    if (Ihas_redex e2) then APPL(e1, (Ione_loreduce e2)) else (APPL(e1,e2));

fun Ione_lreduce (VAR v)       = (VAR v)
  | Ione_lreduce (ABS(id,e))   = ABS(id,(Ione_lreduce e))
  | Ione_lreduce (APPL(e1,e2)) = if (Iis_redex (APPL(e1,e2))) then (Ired (APPL(e1,e2))) else
                                  if (Ihas_redex e1) then APPL(Ione_lreduce e1, e2) else
                                  if (Ihas_redex e2) then APPL(e1, (Ione_lreduce e2)) else (APPL(e1,e2));

fun Ione_rreduce (VAR v) = (VAR v)
  | Ione_rreduce (ABS(id,e)) = ABS(id, (Ione_rreduce e))
  | Ione_rreduce (APPL(e1,e2)) = if (Ihas_redex e2) then (APPL(e1, (Ione_rreduce e2))) else
                                                                  if (Iis_redex (APPL(e1,e2))) then (Ired (APPL(e1,e2))) else
                                                                  if (Ihas_redex e1) then (APPL((Ione_rireduce e1), e2)) else
                                                                        (APPL(e1,e2));

fun Iloreduce (VAR v)       = [(VAR v)]
  | Iloreduce (ABS(id,e))   = (Iaddlam id (Iloreduce e))
  | Iloreduce (APPL(e1,e2)) = (let val l1 = if (Iis_redex (APPL(e1,e2))) then (Iloreduce(Ired(APPL(e1,e2)))) else
                                if (Ihas_redex e1) then (Iloreduce (APPL(Ione_loreduce e1,e2))) else
                                if (Ihas_redex e2) then (Iloreduce(APPL(e1,(Ione_loreduce e2)))) else []
                                in [APPL(e1,e2)] @ l1 end);

fun Iprintloreduce e = (let val tmp = (Iloreduce e)
                          in Iprintlistreduce tmp end);

(* Task 4. Define an SML function LEXP which takes an LEXP and reduces it using
   the leftmost reduction strategy*)
fun lreduce (ID id)       =  [(ID id)]
  | lreduce (LAM(id,e))   = (addlam id (lreduce e))
  | lreduce (APP(e1,e2))  = (let val l1 = if (is_redex (APP(e1,e2))) then  (lreduce (red (APP(e1,e2)))) else
                                          if (has_redex e1) then (lreduce (APP(one_loreduce e1, e2))) else
                                          if (has_redex e2) then  (lreduce (APP(e1,(one_loreduce e2)))) else []
                                            in [APP(e1,e2)]@l1 end);

(* Task 5.  Write an SML function Ilreduce which reduces terms of IEXP to normal
   form by reducing the Ileftmost redex. *)
fun Ilreduce (VAR v)        = [(VAR v)]
  | Ilreduce (ABS(id,e))    = (Iaddlam id (Ilreduce e))
  | Ilreduce (APPL(e1,e2))  = (let val l1 = if (Iis_redex (APPL(e1,e2))) then (Ilreduce (Ired (APPL(e1,e2)))) else
                                            if (Ihas_redex e1) then (Ilreduce (APPL(Ione_lreduce e1, e2))) else
                                            if (Ihas_redex e2) then (Ilreduce (APPL(e1,(Ione_lreduce e2)))) else []
                                             in [APPL(e1,e2)]@l1 end);

(* Rightmost reduces an item lambda term. *)
fun Irreduce (VAR v) =  [(VAR v)]
|   Irreduce (ABS(id,e)) = (Iaddlam id (Irreduce e))
|   Irreduce (APPL(e1,e2)) = (let val l1 = (Irreduce e2)
                                  val e3 = (List.last l1)
                                  val l2 = (Iaddfrontapp e1 l1)
                                  val e4 = (APPL(e1,e3))
                                  val l3 =  if (Iis_redex e4) then (Irreduce (Ired e4)) else
                                            if Iis_var(e1) then [e4] else
                                             	(Irreduce (APPL(Ione_rreduce e1, e3)))
                                             			in l2 @ l3 end);
(* Task 4 continued. *)
fun printlreduce e = (let val tmp =  (lreduce e)
            		        in printlistreduce tmp end);

(* Task 5 continued. *)
fun Iprintlreduce e = (let val tmp =  (Ilreduce e)
                        in Iprintlistreduce tmp end);

(* Task 7.  Iprintrreduce. *)
fun Iprintrreduce e = (let val tmp = (Irreduce e)
                        in Iprintlistreduce tmp end);

Ifindme  "x" ["x", "x1", "x11", "x111"];

(*  Task 6.
    Calculates the length of a list - 1.  Can be used to find the number of reduction
    steps in a certain type of reduction. *)
fun steps [] = 0-1
  | steps (h::tl) = 1 + steps tl;

(* The IEXP terms that correspond to the LEXP terms below. *)
val Ivx = (VAR "x");
val Ivy = (VAR "y");
val Ivz = (VAR "z");
val It1 = (ABS("x",Ivx));
val It2 = (ABS("y",Ivx));
val It3 = (APPL(APPL(It1,It2),Ivz));
val It4 = (APPL(It1,Ivz));
val It5 = (APPL(It3,It3));
val It6 = (ABS("x",(ABS("y",(ABS("z",(APPL(APPL(Ivx,Ivz),(APPL(Ivy,Ivz))))))))));
val It7 = (APPL(APPL(It6,It1),It1));
val It8 = (ABS("z", (APPL(Ivz,(APPL(It1,Ivz))))));
val It9 = (APPL(It8,It3));
val It10 = (APPL(It8,It8));
(* My own 'interesting' terms *)
val It11 = (APPL(APPL(ABS("x",(APPL(Ivx, Ivy))), (ABS("y", Ivy))), Ivz));
val It12 = (ABS("y",APPL((ABS("x",(APPL(Ivx, Ivy))), Ivx))));

(* The LEXP terms from data-files.sml *)
val vx = (ID "x");
val vy = (ID "y");
val vz = (ID "z");
val t1 = (LAM("x",vx));
val t2 = (LAM("y",vx));
val t3 = (APP(APP(t1,t2),vz));
val t4 = (APP(t1,vz));
val t5 = (APP(t3,t3));
val t6 = (LAM("x",(LAM("y",(LAM("z",(APP(APP(vx,vz),(APP(vy,vz))))))))));
val t7 = (APP(APP(t6,t1),t1));
val t8 = (LAM("z", (APP(vz,(APP(t1,vz))))));
val t9 = (APP(t8,t3));
val t11 = (APP(vx, vy))
(* My own terms. *)
val t10 = (APP(t8,t8));
(* val t11 = (APP(LAM("x",t10)));
val t12 = (LAM("y",vy));
(* Example we were given in section 1.3. *)
(*val t11 = (APP(APP(t11,t12),vz));*)
*)
