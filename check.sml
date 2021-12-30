structure Check :>
sig

    exception TypeError of string

    (* Given a context gamma and expression e,
       return tau if there is a tau such that gamma |- e : tau, or
       raise TypeError otherwise *)
    val check : Syntax.exp -> Syntax.typ

end  =
struct

    open Syntax

    type context = (name * typ) list

    (* if you want, you can always
       raise TypeError ""
       but if you put in nice error messages
       then it might help when you're programming in FPC later in the assignment *)
    exception TypeError of string

    (* Given a function conv from 'a to string and an 'a list, return a string representation of that list *)
    fun listToString(conv : 'a -> string, l : 'a list) : string =
        List.foldr (fn (a,b) => conv(a) ^ ", " ^ b) "" l

    (*Convert a type to  a string for debugging purposes *)
    fun typToString(t : typ) : string =
        case t of
            Unit => "Unit"
          | Arrow(t1,t2) => typToString(t1) ^ " -> " ^ typToString(t2)
          | Product(t1, t2) => typToString(t1) ^ " * " ^ typToString(t2)
          | Sum(t1,t2) => typToString(t1) ^ " + " ^ typToString(t2)
          | Rec(x, t) => "Rec " ^ nameToString(x) ^ " is " ^ typToString(t)
          | TVar x => "TVar " ^ nameToString(x)

    (* Given a pattern p and a type t, check whether p : t binding Delta for some context Delta,
       and if so return Delta. Otherwise, raise TypeError *)
    fun checkPat(p : pat, t : typ) : context =
        case p of
            TrivPat => []
          | WildPat => []
          | VarPat x => (x, t) :: []
          | PairPat(p1,p2) => (case t of
                                  Product(t1,t2) => checkPat(p1,t1) @ checkPat(p2,t2)
                                | _ => raise TypeError ("tried to match as a pair with non-pair type " ^ typToString(t)))
          | InLeftPat p' => (case t of
                                Sum(t1, t2) => checkPat(p', t1)
                             | _ => raise TypeError "tried to match as left-inj with non-sum type")
          | InRightPat p' => (case t of
                                Sum(t1, t2) => checkPat(p', t2)
                              | _ => raise TypeError "tried to match as right-inj with non-sum type")
          | FoldPat p' => (case t of
                               Rec(a, t) => checkPat(p', substTyp(t, (Rec(a,t), a)))
                            | _ => raise TypeError "tried to match as fold with non-rec type")
          | AsPat (p',x) => (x, t) :: checkPat(p', t)


    (* Look up a variable in a context, returning its type if it exists or raising TypeError otherwise *)
    fun lookup (g : context) (v : name) : typ =
        case List.find (fn (v', t) => v = v') g of
            NONE => raise TypeError ("Free Variable " ^ Syntax.nameToString v ^ " not found in context")
          | SOME (_, t) => t

    (* Given a context gamma and expression e,
       return tau if there is a tau such that gamma |- e : tau, or
       raise TypeError otherwise *)
    fun checkOpen (g : context, e : exp) : typ =
        case e of
            Var v => lookup g v
          | Lam (t, (x,e)) => let val t' = checkOpen ((x,t)::g, e) in Arrow(t,t') end
          | App(e1, e2) => (case checkOpen(g, e1) of
                                Arrow(t, t') => let val t2 = checkOpen(g, e2) in if Syntax.alphaEquivTyp(t,t2) then t' else
                                                                                 raise TypeError "mismatched applied and applier types" end
                              | _ => raise TypeError "First argument to app needs to be a function")
          | Triv => Unit
          | Let (e1, (x, e2)) => checkOpen((x,checkOpen(g, e1))::g, e2)
          | Pair(e1, e2) => Product(checkOpen(g, e1), checkOpen(g, e2))
          | InLeft(t2, e) => Sum(checkOpen(g,e), t2)
          | InRight(t1, e) => Sum(t1, checkOpen(g,e))
          | Fix(t, (x, e)) => checkOpen((x,t)::g, e)
          | Fold((t,tau),e) => let val t' = checkOpen(g,e)
                                   val topTyp = substTyp(tau, (Rec(t, tau), t))
                               in
                                 if alphaEquivTyp(t', topTyp) then Rec(t, tau) else
                                 raise TypeError ("type equation for fold not satisfied, expected " ^
                                       typToString(topTyp) ^ " but got " ^ typToString(t')) end
          | Case(e, branches) => let val t = checkOpen(g, e)
                                     val bindings = List.map (fn (pat,exp) => (checkPat(pat,t), exp)) branches
                                     val ts = List.map (fn (delt, exp) => checkOpen(g@delt, exp)) bindings
                                     val sigma::rest = ts
                                 in
                                   if List.all (fn t => alphaEquivTyp(sigma, t)) rest then sigma else
                                   raise TypeError ("case branches have different RHS types, " ^ listToString(typToString, ts))

                                 end



    (* Given an expression e,
       return tau if there is a tau such that empty |- e : tau,
       or raise TypeError if e is not well-typed in the empty context *)
    fun check e = checkOpen ([], e)

end
