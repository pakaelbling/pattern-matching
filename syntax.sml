structure Syntax :>
sig

    (* for this assignment, we represent names by a pair of a string and
       a unique int suffix (used for alpha-conversion).
       freshName generates a new suffix that has never been used before,
       so freshName x is guaranteed to be different from all previously used variables.

       Note that you can still use (x = y) to check if two names are equal.

       In a term, variable names (x,i) are printed as x[i].  You can
       mostly ignore [i] when reading the term, and only look at them
       for disambiguation if things seem wrong.

       *)
    type name = string * int
    val freshNameString : string -> name
    val freshName : name -> name
    val nameToString : name -> string

    datatype typ =
        Arrow of typ * typ
      | Unit
      | Product of typ * typ
      | Sum of typ * typ
      | Rec of name * typ
      | TVar of name

    (* freshen the top-level bound variables in e if e is a binding form (Rec) *)
    val freshenTopTyp : typ -> typ

    (* substTyp(tau, (sigma,a)) is the substitution tau[sigma/a] *)
    val substTyp : typ * (typ * name) -> typ

    (* check if two types are alpha-equivalent *)
    val alphaEquivTyp : typ * typ -> bool

    datatype pat =
        TrivPat
      | PairPat of pat * pat
      | InLeftPat of pat
      | InRightPat of pat
      | FoldPat of pat
      | VarPat of name
      | WildPat
      | AsPat of pat * name

    val binds : pat -> name list

    datatype exp =
	Var of name
      | Lam of typ * (name * exp)
      | App of exp * exp
      | Let of exp * (name * exp)
      | Triv
      | Pair of exp * exp
      | InLeft of typ * exp
      | InRight of typ * exp
      | Fold of (name * typ) * exp
      | Case of exp * (pat * exp) list
      | Fix of typ * (name * exp)

    (* freshen the top-level bound variables in e if e is a binding form *)
    val freshenTop : exp -> exp

    (* simultaneous substitution *)
    type ssubst = (exp * name) list
    val subst : exp * ssubst -> exp

    (* builtins with special pattern matching defined in terms of other types *)

    val boolTyp : typ
    val trueExp : exp
    val falseExp : exp
    val truePat : pat
    val falsePat : pat

    val natTyp : typ
    val zeroExp : exp
    val succExp : exp -> exp
    val zeroPat : pat
    val succPat : pat -> pat

    val listTyp : typ
    val nilExp : exp
    val consExp : exp -> exp
    val nilPat : pat
    val consPat : pat -> pat

end =
struct

    type name = string * int

    local
	val suffix = ref 0
    in
        fun freshNameString (s : string) : name =
            (suffix := (!suffix)+1;
             (s,(!suffix)))

	fun freshName ((s,i) : name) : name =
	    freshNameString s
    end

    fun nameToString (x,s) = x ^ "[" ^ Int.toString s ^"]"

    (* freshen the top-level bound variables in e if e is a binding form (Rec) *)
    datatype typ = Arrow of typ * typ | Unit | Product of typ * typ | Sum of typ * typ | Rec of name * typ | TVar of name

    fun swapName (z : name, (x : name, y : name)) =
	if z = x then y
	else if z = y then x
	else z

    fun swapTyp (t : typ, (z : name, w : name)) : typ =
	let (* give short names to the recursive call and
               swapName call since they always get called with the same x and y *)
            fun st e = swapTyp (e, (z, w))
	    fun sn x = swapName (x ,(z, w))
        in
            case t of
                Arrow(t1,t2) => Arrow (st t1, st t2)
              | Product(t1,t2) => Product (st t1, st t2)
              | Sum(t1,t2) => Sum (st t1, st t2)
              | TVar name => TVar (sn name)
              | Rec(alpha,tau) => Rec(sn alpha, st tau)
              | Unit => Unit
	end

    fun freshenTopTyp t =
        case t of
            Rec (alpha, t) =>
                let val alpha' = freshName alpha
                in Rec(alpha', swapTyp (t, (alpha,alpha')))
                end
          | _ => t

    fun substTyp (t, (t', a')) =
	let (* give short names to the recursive call and
               swapName call since they always get called with the same x and y *)
            fun st t = substTyp (t, (t',a'))
        in
            case t of
                Arrow(t1,t2) => Arrow(st t1, st t2)
              | Product(t1,t2) => Product(st t1, st t2)
              | Sum(t1,t2) => Sum(st t1, st t2)
              | Unit => Unit
              | Rec(a,t) => Rec(a, st t)
              | TVar a => (case a = a' of
                               true => t'
                             | false => TVar a)
        end

    fun alphaEquivTyp (t : typ, t' : typ) : bool =
        case (t,t') of
            (Arrow(t1,t2), Arrow(t1',t2')) => alphaEquivTyp(t1,t1') andalso alphaEquivTyp(t2,t2')
          | (Product(t1,t2), Product(t1',t2')) => alphaEquivTyp(t1,t1') andalso alphaEquivTyp(t2,t2')
          | (Sum(t1,t2), Sum(t1',t2')) => alphaEquivTyp(t1,t1') andalso alphaEquivTyp(t2,t2')
          | (TVar x, TVar y) => x = y
          | (Unit,Unit) => true
          | (Rec(a,t), Rec(a',t')) =>
                let val z = freshName a
                in
                    alphaEquivTyp( swapTyp(t, (a,z)), swapTyp(t', (a',z)))
                end
          | _ => false

    datatype pat =
        TrivPat
      | PairPat of pat * pat
      | InLeftPat of pat
      | InRightPat of pat
      | FoldPat of pat
      | VarPat of name
      | WildPat
      | AsPat of pat * name

    datatype exp =
	Var of name
      | Lam of typ * (name * exp)
      | App of exp * exp
      | Let of exp * (name * exp)
      | Triv
      | Pair of exp * exp
      | InLeft of typ * exp
      | InRight of typ * exp
      | Fold of (name * typ) * exp
      | Case of exp * (pat * exp) list
      | Fix of typ * (name * exp)

    type swaps = (name * name) list

    fun sswapName (z : name, rho : swaps) : name =
        (case List.find (fn(x,y) => x = z orelse y = z) rho of
             SOME (x,y) => if x=z then y else x
           | NONE => z)

    fun swapPat (p : pat, rho : swaps) : pat =
	let (* give short names to the recursive call and
               swapName call since they always get called with the same x and y *)
            fun sp e = swapPat (e, rho)
	    fun sn x = sswapName (x , rho)
        in
            case p of
                VarPat z => VarPat (sn z)
              | TrivPat => TrivPat
              | PairPat(p1, p2) => PairPat(sp p1, sp p2)
              | InLeftPat (p) => InLeftPat (sp p)
              | InRightPat (p) => InRightPat (sp p)
              | FoldPat (p) => FoldPat (sp p)
              | WildPat => WildPat
              | AsPat(p,n) => AsPat(sp p, sn n)
	end

    (* applies rho to the expression variables in e only, not the type variables *)
    fun swapExp (e : exp, rho : swaps) : exp =
	let (* give short names to the recursive call and
               swapName call since they always get called with the same x and y *)
            fun se e = swapExp (e, rho)
	    fun sn x = sswapName (x , rho)
        in
            case e of
                Var z => Var (sn z)
              | Lam (t, (x,e)) => Lam (t, (sn x, se e))
              | App (e1, e2) => App (se e1 , se e2)
              | Let(e1, (x, e2)) => Let(se e1, (sn x, se e2))
              | Triv => Triv
              | Pair(e1, e2) => Pair(se e1, se e2)
              | InLeft (t, e) => InLeft (t, se e)
              | InRight (t, e) => InRight (t, se e)
              | Fold((a,t),e) => Fold ((a,t), se e)
              | Fix(t,(x,e)) => Fix (t, (sn x, se e))
              | Case(e, branches) => Case(se e, List.map (fn (p,e) => (swapPat (p,rho), se e)) branches)
	end

    fun binds(p : pat) : name list =
        case p of
            VarPat x => [x]
          | TrivPat => []
          | PairPat(p1,p2) => binds p1 @ binds p2
          | InLeftPat(p) => binds p
          | InRightPat(p) => binds p
          | FoldPat(p) => binds p
          | WildPat => []
          | AsPat(p,n) => n :: binds p

    fun freshenBranch(p : pat , e : exp) : pat * exp =
        let val pvars : name list = binds p
            val ren : swaps = List.map (fn x => (x, freshName x)) pvars
        in
            (swapPat (p, ren), swapExp (e, ren))
        end

    (* freshen the topmost binder in e *)
    fun freshenTop (e : exp) : exp =
        case e of
            Let (e1, (x, e2)) =>
                let val x' = freshName x in
                    Let (e1, (x', swapExp (e2, [(x, x')])))
                end
          | Lam (t, (x,e)) =>
                let val x' = freshName x
                in Lam (t,(x',swapExp(e, [(x,x')])))
                end
          | Case (e, branches) =>
                Case (e, List.map freshenBranch branches)
          | Fold ((a,t), e) =>
                let val a' = freshName a
                in Fold ((a', swapTyp (t,(a,a'))),e)
                end
          | Fix (t, (x,e)) =>
                let val x' = freshName x
                in Fix (t,(x',swapExp(e, [(x,x')])))
                end
          | e => e

    type ssubst = (exp * name) list

    fun subst (e : exp, theta : ssubst) : exp =
	let (* give short names to the recursive call since they always get called with the same x and y *)
            fun se e = subst (e, theta)
        in
            (* since we freshen the outermost bound variable here,
               the substitution will work even with shadowing and not capture
               *)
            case freshenTop e of
                Var x =>
                    (case List.find (fn (_,x') => x = x') theta of
                         SOME (e',_) => e'
                       | NONE => Var x)
              | Lam (t, (x,e)) => Lam (t, (x, se e))
              | App (e1, e2) => App (se e1 , se e2)
              | Let(e1, (x, e2)) => Let (se e1, (x, se e2))
              | Triv => Triv
              | Pair(e1,e2) => Pair(se e1, se e2)
              | InLeft (t, e) => InLeft (t, se e)
              | InRight (t, e) => InRight (t, se e)
              | Fold((alpha,t),e) => Fold((alpha,t),se e)
              | Fix(t,(x,e)) => Fix(t,(x,se e))
              | Case(e, branches) => Case(se e, List.map (fn (p,e) => (p, se e)) branches)
        end


    val boolTyp = Sum(Unit,Unit)
    val trueExp = InLeft(Unit,Triv)
    val falseExp = InRight(Unit,Triv)
    val truePat = InLeftPat(TrivPat)
    val falsePat = InRightPat(TrivPat)

    (* TASK: define these built-ins; they are defined to be Unit as a placeholder for now
       so that the code compiles.
     *)
    val tName = freshNameString("a")
    val natTyp = let val n = freshNameString("a") in Rec(tName, Sum(Unit, TVar tName)) end
    val zeroExp = let val t = freshNameString ("t") in Fold ((t, Sum(Unit, TVar t)), InLeft(natTyp, Triv)) end
    val zeroPat = FoldPat(InLeftPat(TrivPat))
    fun succExp(e) = let val t = freshNameString("t") in Fold((t, Sum(Unit, TVar t)), InRight(Unit, e)) end
    fun succPat(e) = FoldPat(InRightPat(e))

    val listTyp = let val n = freshNameString("a") in Rec(n, Sum(Unit, Product(natTyp, TVar n))) end
    val nilExp = let val t = freshNameString("t") in Fold((t, Sum(Unit, Product(natTyp, TVar t))), InLeft(Product(natTyp, listTyp), Triv)) end
    fun consExp(e) = let val t = freshNameString("t") in Fold((t, Sum(Unit, Product(natTyp, TVar t))), InRight(Unit, e)) end
    val nilPat = FoldPat(InLeftPat(TrivPat))
    fun consPat(e) = FoldPat(InRightPat(e))


end
