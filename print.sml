signature PRINT =
sig
  (* print an expression *)
  val expToString : Syntax.exp -> string
  val typToString : Syntax.typ -> string
end

structure Print :> PRINT =
struct

  open Syntax

  (* NOTE: you can change this to suppress the type annotations on terms *)
  val showTypesInTerms = false

  (* NOTE: you can change this to determine whether bool/nat/list values
           get printed out expanded into products/sums/recursive types or not.

           note that patterns are always expanded because they don't
           have enough type information to un-expand
  *)
  val expandValues = false

  fun typ t = 
      case t of 
          TVar(x) => nameToString x
        | Arrow(t1,t2) => "( " ^ typ t1 ^ " -> " ^ typ t2 ^ " )"
        | Product(t1,t2) => "(" ^ typ t1 ^ " * " ^ typ t2 ^ " )"
        | Sum(t1,t2) => "(" ^ typ t1 ^ " + " ^ typ t2 ^ " )"
        | Rec(a,t) => "rec " ^ nameToString a ^ " is " ^ typ t
        | Unit => "unit"

  fun maybetyp t = if showTypesInTerms then typ t else ""

  fun exp0 (tab, e) = case e of
      App(e1, e2) =>
          exp0 (tab, e1) ^ "@" ^ expinf (tab, e2)
    | _ =>
          let
                fun bib (e : exp) : bool option =
                    case e of
                        InLeft(Unit,Triv) => SOME true
                      | InRight(Unit,Triv) => SOME false
                      | _ => NONE
                            
                fun bin (e : exp) : int option =
                    case e of
                        Fold((a,t),InLeft(_,_)) => if alphaEquivTyp (Rec(a,t) , Syntax.natTyp) then SOME 0 else NONE
                      | Fold((a,t),InRight(_,e)) => if alphaEquivTyp (Rec(a,t) , Syntax.natTyp) then Option.map (fn x => 1 + x) (bin e) else NONE
                      | _ => NONE
                            
                fun bil (e : exp) : (int list) option =
                    case e of
                        Fold((a,t),InLeft(_,Triv)) => if alphaEquivTyp (Rec(a,t), Syntax.listTyp) then SOME [] else NONE
                      | Fold((a,t),InRight(_,Pair(e1,e2))) =>
                            if alphaEquivTyp (Rec(a,t), Syntax.listTyp) 
                            then
                                case (bin e1, bil e2) of
                                    (SOME x, SOME xs) => SOME (x::xs)
                                  | _ => NONE
                            else NONE
                                  | _ => NONE
                                
          in 
              if expandValues
              then expinf (tab, e)
              else (* detect nats and lists and uncompile them *)
                  (case bin e of
                       SOME v => Int.toString v
                     | NONE => (case bil e of
                                    SOME v => "[" ^ List.foldr (fn (x,y) => Int.toString x ^ "," ^ y) "]" v
                                  | NONE =>
                                    case bib e of
                                        SOME true => "true"
                                      | SOME false => "false"
                                      | NONE => expinf (tab, e)))
          end
                       
  and expinf (tab, e) = case e of
      Var(x) => nameToString x
    | Lam(t,(x,e)) => "(lam " ^ nameToString x ^ " : " ^ maybetyp t ^ "." ^ exp0 (tab,e) ^")"
    | Let(e1, (x, e2)) =>
          let val tab' = tab ^ "    "
          in "let " ^ nameToString x ^ " be " ^ exp0 (tab, e1) ^ " in" ^
              tab' ^ exp0 (tab', e2) ^
              tab ^ "end" end
    | InLeft(t,e) => "inleft[" ^ maybetyp t ^ "](" ^ exp0 (tab,e) ^ ")"
    | InRight(t,e) => "inright[" ^ maybetyp t ^ "](" ^ exp0 (tab,e) ^ ")"
    | Triv => "<>"
    | Pair(e1, e2) => "< " ^ exp0 (tab,e1) ^ " , " ^ exp0 (tab,e2) ^ ">"
    | Case (e, bs) => 
          "case " ^ exp0 (tab,e) ^ " { " ^ branches (tab,bs) ^ " } "
    | Fix(t,(x,e)) => "(fix " ^ nameToString x ^ " : " ^ maybetyp t ^ "." ^ exp0 (tab,e) ^")"
    | Fold((a,t),e) => "fold[" ^ maybetyp (Rec(a,t)) ^ "](" ^ exp0 (tab,e) ^ ")"
    | _ => "(" ^ exp0 (tab, e) ^ ")"

  and branches (tab,bs) =
      case bs of
          [] => ""
        | [b] => branch(tab,b)
        | b :: bs => branch(tab,b) ^ " | " ^ branches(tab,bs)

  and branch (tab,(p,e)) = pat (tab,p) ^ " => " ^ exp0(tab,e)

  and pat (tab,p) = case p of
      VarPat(x) => nameToString x
    | InLeftPat(p) => "inleft(" ^ pat(tab,p) ^ ")"
    | InRightPat(p) => "inright(" ^ pat(tab,p) ^ ")"
    | TrivPat => "<>"
    | PairPat(p1, p2) => "< " ^ pat (tab,p1) ^ " , " ^ pat (tab,p2) ^ ">"
    | FoldPat(p) => "fold (" ^ pat (tab,p) ^ ")"
    | AsPat(p,n) => "name " ^ pat (tab,p) ^ " as " ^ nameToString n
    | WildPat => "_"
          
  fun expToString t = exp0 ("\n", t)
  fun typToString t = typ t

end;  (* functor PrintFun *)
