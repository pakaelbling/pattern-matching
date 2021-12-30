signature PARSE =
sig

  val parse : (Lexer.token * char list) Stream.stream -> Syntax.exp Stream.stream

  exception Error of string
end;  (* signature PARSE *)

structure Parse :> PARSE = 
struct

    type exp = Syntax.exp
    
    structure S = Stream
    open Syntax
    open Lexer

    exception Error of string

    (* 
       The concrete grammar parsed by this module is as follows:

       program ::= exp0 SEMICOLON

       typ ::= NAT | LPAREN typ ARR typ RPAREN | LPAREN typ PRODUCT typ RPAREN | LPAREN typ SUM typ RPAREN | rec VAR(s) DOT type
       
       exp0    ::= exp0 APP expinf | expinf
       expinf  ::= LPAREN exp0 RPAREN
                |  NUMBER(k)
                |  VAR(s)
                |  LET VAR(s) BE exp0 IN exp0 END
                |  ZERO
                |  SUCC exp0 
                |  REC exp0 LCURLY ZERO GOESTO exp0 BAR SUCC VAR(s) WITH VAR(s) GOESTO exp0 RCURLY
                |  LAM var(S) COLON typ DOT exp0
                |  LANGLE exp0 COMMA exp0 RANGLE 
                |  LANGLE RANGLE 
                |  INLEFT LBRACKET typ RBRACKET exp0 
                |  INRIGHT LBRACKET typ RBRACKET exp0 
                |  CASE exp0 LCURLY INLEFT VAR(s) GOESTO exp0 BAR INRIGHT VAR(s) GOESTO exp0 RCURLY

    *)

    exception Unbound of string

    fun noDups(l : name list) : bool =
        case l of
            [] => true
          | x :: xs => not (List.exists (fn y => y = x) xs) andalso noDups xs
    
    fun Num 0 = zeroExp
      | Num n = succExp ( (Num (n-1)))

    fun NumPat 0 = zeroPat
      | NumPat n = succPat ( (NumPat (n-1)))

    (* next s = (x,s'), where x is the head of s, s' the tail of s
       raises Error if stream is empty
    *)
    fun next s =
        case S.force s
          of S.Nil => raise Error "Unexpected end of stream"
           | S.Cons result => result

    type pstream = (Lexer.token * char list) Stream.stream 
    type env = string -> name
        
    fun expected (s : pstream) (msg : string) : 'a =
        let val ((_, l), _) = next s
        in raise Error ("Expected " ^ msg ^ " at `" ^
                        concat (map Char.toString l) ^ "'") end

    fun require (s : pstream) (token : token) =
            let val ((t,l), s') = next s
            in if t = token then s'
               else expected s (Lexer.tokenToString token ^ " token")
            end

    (* d is type environment 
       g is expression environment *)

    fun extend (g : env, x : string) : env =
        let
            val v = Syntax.freshNameString x in (fn y => if x = y then v else g y)
        end
    
    fun var (s : pstream) : string * pstream =
        case next s of
            ((VAR(x),_), s) => (x, s)
          | _ => expected s "a variable name"
                
    fun program (s : pstream) : exp * pstream =
        let
            val Xname = freshNameString "X"
            val Yname = freshNameString "Y"
            val Zname = freshNameString "Z"
            val (e, s) = exp0 ((fn "X" => Xname
                                 |  "Y" => Yname
                                 | "Z" => Zname
                                 | x => raise Error ("Free type variable `" ^ x ^ "'")),
                               (fn x => raise Error ("Free variable `" ^ x ^ "'")),
                               s) 
                val s = require s SEMICOLON
        in (e, s)
        end

    and typ (d : env, s : pstream) : typ * pstream = 
        case next s of
            ((VAR(x),_), s) => ( (Syntax.TVar(d x)), s)
          | ((NAT,_),s) => (Syntax.natTyp,s)
          | ((LIST,_),s) => (Syntax.listTyp,s)
          | ((BOOL,_),s) => (Syntax.boolTyp,s)
          | ((UNIT,_),s) => (Syntax.Unit,s)
          | ((LPAREN,_),s) => let val (t1,s) = typ (d,s)
                                  val ((middlet,_),s) = next s
                                  val con = (case middlet of
                                                 ARR => Syntax.Arrow
                                               | SUM => Syntax.Sum
                                               | PRODUCT => Syntax.Product
                                               | _ => expected s "an infix type constructor") 
                                  val (t2,s) = typ (d,s)
                                  val s = require s RPAREN
                              in
                                  (con(t1,t2),s)
                              end
          | ((REC,_),s) => let val (a,s) = var s
                               val s = require s IS
                               val d' = extend(d,a)
                               val (t,s) = typ(d',s)
                           in
                               (Syntax.Rec (d' a, t) , s)
                           end
          | ((t,_),s) => expected s "a type" 

    and exp0 (d : env, g : env, s : pstream) : exp * pstream =
        let
            val (e, s) = expinf (d, g, s)
        in
            exp0' (e, d, g, s)
        end
    
   and exp0' (e : exp, d : env, g : env, s : pstream) : exp * pstream =
       case next s
           of ((APP,_), s) => 
               let val (e', s) = expinf (d, g, s)
               in exp0' ( (App(e, e')), d, g, s) end
         | _ => (e, s)
                   
   and expinf (d : env, g : env, s : pstream) : exp * pstream =
       case next s of
           ((LPAREN,_), s) => let val (e, s) = exp0 (d, g, s)
                                  val s = require s RPAREN
                              in (e, s) end
         | ((NUMBER(k),_), s) => ( (Num(k)), s)
         | ((VAR(x),_), s) => ( (Var(g x)), s)
         | ((LET,_), s) => let val (x, s) = var s
                               val s = require s BE
                               val (e1, s) = exp0 (d, g, s)
                               val s = require s IN
                               val g' = extend(g, x)
                               val (e2, s) = exp0 (d, g', s)
                               val s = require s END
                           in ( (Let(e1, (g' x, e2))), s) end
         | ((ZERO,_) , s) => ( zeroExp , s)
         | ((SUCC,_) , s) => let val (e,s) = exp0 (d, g , s) in ( (succExp e) , s) end
         | ((TRUE,_) , s) => ( trueExp , s)
         | ((FALSE,_) , s) => ( falseExp , s)
         | ((NIL,_) , s) => ( nilExp , s)
         | ((CONS,_) , s) => let val (e,s) = exp0 (d, g , s) in ( (consExp e) , s) end
         | ((LAM,_),s) => let val (x, s) = var s
                              val s = require s COLON
                              val (t,s) = typ (d,s)
                              val s = require s DOT
                              val g' = extend (g,x)
                              val (e,s) = exp0 (d, g',s)
                          in
                              ( (Lam(t,(g' x,e))),s)
                          end
         | ((LEFTANGLE,_),s) =>
                          (case next s of
                               ((RIGHTANGLE,_),s) => (Triv, s)
                             | _ =>
                                   let val (e1,s) = exp0 (d, g , s)
                                       val s = require s COMMA
                                       val (e2,s) = exp0 (d, g , s)
                                       val s = require s RIGHTANGLE
                                   in
                                       ( Pair (e1,e2) , s)
                                   end
                               )
         | ((INLEFT,_),s) => let
                                 val s = require s LEFTBRACKET
                                 val (t,s) = typ (d,s)
                                 val s = require s RIGHTBRACKET
                                 val (e,s) = exp0 (d, g , s)
                             in
                                 ( InLeft (t,e) , s)
                             end
         | ((INRIGHT,_),s) => let
                                  val s = require s LEFTBRACKET
                                  val (t,s) = typ (d,s)
                                  val s = require s RIGHTBRACKET
                                  val (e,s) = exp0 (d, g , s)
                              in
                                  ( InRight (t,e) , s)
                              end
         | ((CASE,_),s) => let val (e,s) = exp0 (d, g,s)
                               val s = require s LEFTCURLY
                               val (bs,s) = branches (d,g,s)
                               val s = require s RIGHTCURLY
                           in
                               ( (Case(e, bs)), s) 
                           end
         | ((FIX,_),s) => let val (x, s) = var s
                              val s = require s COLON
                              val (t,s) = typ (d,s)
                              val s = require s DOT
                              val g' = extend (g,x)
                              val (e,s) = exp0 (d, g',s)
                          in
                              (Fix(t,(g' x,e)),s)
                          end
         | ((FOLD,_), s) => let val s = require s LEFTBRACKET
                                val s = require s REC
                                val (a,s) = var s
                                val s = require s IS
                                val d' = extend(d,a)
                                val (t,s) = typ(d',s)
                                val s = require s RIGHTBRACKET
                                val (e,s) = exp0 (d,g,s)
                            in
                                ( Fold((d' a, t),e) , s)
                            end
         | _ => expected s "an expression"

    (* note: variables in the pattern should not be in g already;
       g is supplied so that we can store-pass to extend it

       FIXME: check that all variables are distinct 
       *)
    and pat (d : env, g : env, s : pstream) : pat * env * pstream =
        case next s of
            ((LPAREN,_), s) => let val (p, g, s) = pat (d, g, s)
                                   val s = require s RPAREN
                               in (p, g, s) end
         | ((NUMBER(k),_), s) => ( (NumPat(k)), g, s)
         | ((VAR(x),_), s) =>
               let val g = extend (g, x)
               in
                   ( (VarPat(g x)), g , s)
               end 
         | ((ZERO,_) , s) => ( zeroPat , g, s)
         | ((SUCC,_) , s) => let val (p,g,s) = pat (d, g , s) in ( (succPat p) , g, s) end
         | ((TRUE,_) , s) => ( truePat , g, s)
         | ((FALSE,_) , s) => ( falsePat , g, s)
         | ((NIL,_) , s) => ( nilPat , g, s)
         | ((CONS,_) , s) => let val (p,g,s) = pat (d, g , s) in ( (consPat p) , g, s) end
         | ((INLEFT,_),s) => let
                                 val (p,g,s) = pat (d, g , s)
                             in
                                 ( InLeftPat p , g, s)
                             end
         | ((INRIGHT,_),s) => let
                                 val (p,g,s) = pat (d, g , s)
                              in
                                  ( InRightPat p , g, s)
                              end
         | ((FOLD,_), s) => let
                                val (p,g,s) = pat (d, g , s)
                            in
                                ( FoldPat(p) , g, s)
                            end
         | ((LEFTANGLE,_),s) =>
                          (case next s of
                               ((RIGHTANGLE,_),s) => (TrivPat, g, s)
                             | _ =>
                                   let val (p1,g,s) = pat (d, g , s)
                                       val s = require s COMMA
                                       val (p2,g,s) = pat (d, g , s)
                                       val s = require s RIGHTANGLE
                                   in
                                       ( PairPat (p1,p2) , g, s)
                                   end
                               )
         | ((WILD,_),s) => (WildPat , g , s)
         | ((NAME,_),s) => let val (p,g,s) = pat (d,g,s)
                               val s = require s AS
                               val (n,s) = var s
                               val g = extend (g,n)
                           in
                               ( AsPat(p,g n) , g, s)
                           end 
                               
         | _ => expected s "a pattern"
                            
    and branch (d : env, g : env, origs as s : pstream) : (pat * exp) * pstream =
        let 
            val (p,g1,s) = pat (d,g,s) 
            val s = require s GOESTO 
            val (e,s) = exp0 (d, g1,s)
        in
            if noDups (binds p)
            then ((p,e), s)
            else expected origs " all pattern variables to be distinct"
        end 

   and branches (d : env, g : env, s : pstream) : ((pat * exp) list) * pstream =
       let val (b, s) = branch (d,g,s)
       in
           case next s of
               ((BAR,_), s) =>
                   let val (bs, s) = branches(d,g,s)
                   in
                       (b :: bs, s)
                   end 
             | _ => ([b], s) 
       end 
        
    (* Exported parsing function *)
          
    fun parse s = S.delay (fn () =>
            case S.force s
              of S.Nil => S.Nil
               | S.Cons _ => let val (e, s) = program s
                             in S.Cons(e, parse s) end)

end;  (* functor ParseFun *)
