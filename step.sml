structure Step :>
sig
    datatype result =
        Done
      | Stepped of Syntax.exp

    (* Given a closed, well-typed expression e (i.e. empty |- e : tau for some tau),
       returns an Stepped e' for an e' such that e |-> e' if such an e' exists, or
       returns Done if e is done *)
    val progress : Syntax.exp -> result

end =
struct

    open Syntax

    datatype result =
        Done
      | Stepped of Syntax.exp

    exception DoesntMatch

    (* given a pattern p and a done expression e,
       return theta if p matches e with theta for some theta,
       or raise exception DoesntMatch otherwise *)
    fun match (p : pat, e : exp) : ssubst =
        case p of
            TrivPat => if e = Triv then [] else raise DoesntMatch
          | WildPat => []
          | VarPat x => [(e, x)]
          | PairPat (p1, p2) => (case e of
                                    Pair(e1, e2) => match(p1,e1) @ match(p2, e2)
                                  | _ => raise DoesntMatch)
          | InLeftPat p' => (case e of
                                 InLeft (_, e') => match(p', e')
                               | _ => raise DoesntMatch)
          | InRightPat p' => (case e of
                                  InRight (_, e') => match(p', e')
                                | _ => raise DoesntMatch)
          | FoldPat p' => (case e of
                               Fold ((n, t), e') => match(p', e')
                             | _ => raise DoesntMatch)
          | AsPat (p', x) => (e, x) :: match(p', e)

    (* Find the first branch in branches that matches e, and return the appropriate substitution
       and the original expression *)
    fun caseHelp(branches : (pat * exp) list, e : exp) : (ssubst * exp) =
        case branches of
            [] => raise Fail "nonexhaustive case patterns"
          | (p, rhs)::ps => (match(p, e), rhs) handle DoesntMatch => caseHelp(ps, e)


    fun progress e =
        case e of
            Lam (t,e) => Done
          | App (e1,e2) =>
                     Stepped (case progress e1 of
                                  Done => (case progress e2 of
                                               Done => (case e1 of Lam (t,(x,e)) => subst (e, [(e2,x)]))
                                             | Stepped e2' => App (e1 , e2'))
                                | Stepped e1' => App (e1', e2))
          | Let (e1,(x,e2)) => Stepped (case progress e1 of
                                            Done => (subst (e2, [(e1,x)]))
                                          | Stepped e1' => (Let (e1', (x,e2))))
          | Triv => Done
          | Pair(e1,e2) => (case progress e1 of
                                Done => (case progress e2 of
                                             Done => Done
                                          | Stepped e2' => Stepped (Pair (e1 , e2')))
                              | Stepped e1' => Stepped (Pair (e1', e2)))
          | InLeft (t,e) =>  (case progress e of
                                Done => Done
                              | Stepped e' => Stepped (InLeft (t,e')))
          | InRight (t,e) =>  (case progress e of
                                   Done => Done
                                 | Stepped e' => Stepped (InRight (t,e')))
          | Fold ((a,t),e) => (case progress e of
                                   Done => Done
                                | Stepped e' => Stepped(Fold ((a,t), e')))
          | Case (e, branches) => (case progress e of
                                       Stepped e' => Stepped(Case(e', branches))
                                     | Done => let val (s, rhs) = caseHelp(branches, e) in
                                                 Stepped(Syntax.subst(rhs, s)) end )
          | whole as Fix(t,(x,e)) => Stepped(Syntax.subst(e, [(whole, x)]))

end
