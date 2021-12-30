signature LEXER =
sig
    datatype token =
        LET
      | BE
      | IN
      | END
      | LPAREN
      | RPAREN
      | SEMICOLON
      | NUMBER of int
      | VAR of string
      | SUCC
      | ZERO
      | LEFTCURLY
      | RIGHTCURLY
      | WITH
      | LAM
      | COLON
      | DOT
      | GOESTO
      | BAR
      | NAT
      | ARR
      | APP
      | LEFTANGLE
      | RIGHTANGLE
      | LEFTBRACKET
      | RIGHTBRACKET
      | COMMA 
      | INLEFT
      | INRIGHT
      | CASE
      | PRODUCT
      | SUM
      | UNIT
      | FOLD
      | REC
      | FIX
      | TRUE
      | FALSE
      | NIL
      | CONS
      | BOOL
      | LIST 
      | IS
      | WILD
      | NAME 
      | AS
        
    exception Error of string

    val lex : (char * char list) Stream.stream -> (token * char list) Stream.stream

    val tokenToString : token -> string
end;  (* signature LEXER *)


structure Lexer :> LEXER =
struct

    structure S = Stream

    exception Error of string

    datatype token =
        LET
      | BE
      | IN
      | END
      | LPAREN
      | RPAREN
      | SEMICOLON
      | NUMBER of int
      | VAR of string
      | SUCC
      | ZERO
      | LEFTCURLY
      | RIGHTCURLY
      | WITH
      | LAM
      | COLON
      | DOT
      | GOESTO
      | BAR
      | NAT
      | ARR
      | APP
      | LEFTANGLE
      | RIGHTANGLE
      | LEFTBRACKET
      | RIGHTBRACKET
      | COMMA 
      | INLEFT
      | INRIGHT
      | CASE
      | PRODUCT
      | SUM
      | UNIT
      | FOLD
      | REC
      | FIX
      | TRUE
      | FALSE
      | NIL
      | CONS
      | BOOL
      | LIST
      | IS
      | WILD
      | NAME 
      | AS
        
    fun next s =
        case S.force s of
            S.Nil => raise Error "Unexpected end of stream"
          | S.Cons result => result
   
    fun isNum (c) = Char.isDigit (c)
    fun isAlpha (c) = Char.contains "_'" c orelse Char.isDigit (c)
                      orelse Char.isLower (c) orelse Char.isUpper (c)

    fun keywords ("let") = LET
      | keywords ("be") = BE
      | keywords ("in") = IN
      | keywords ("end") = END
      | keywords ("s") = SUCC
      | keywords ("z") = ZERO
      | keywords ("with") = WITH
      | keywords ("lam") = LAM
      | keywords ("nat") = NAT
      | keywords ("unit") = UNIT
      | keywords ("inleft") = INLEFT
      | keywords ("inright") = INRIGHT
      | keywords ("case") = CASE
      | keywords ("fold") = FOLD
      | keywords ("rec") = REC
      | keywords ("fix") = FIX
      | keywords ("true") = TRUE
      | keywords ("false") = FALSE
      | keywords ("nil") = NIL
      | keywords ("cons") = CONS
      | keywords ("bool") = BOOL
      | keywords ("list") = LIST
      | keywords ("is") = IS
      | keywords ("as") = AS
      | keywords ("name") = NAME
      | keywords v = VAR(v)

    fun lexAlpha (s, v, l) =
        let val ((c,_), s') = next s
        in if isAlpha (c) then lexAlpha (s', c::v, l)
                          else ((keywords(implode(rev(v))), l), s)
        end

    fun lexNum (s, k, l) =
        let val ((c,_), s') = next s
        in if isNum (c) then lexNum (s', 10*k + (ord c - ord #"0"), l)
                        else ((NUMBER(k), l), s)
        end

    fun token ((#"(",l), s) = ((LPAREN,l), s)
      | token ((#")",l), s) = ((RPAREN,l), s)
      | token ((#";",l), s) = ((SEMICOLON,l), s)
      | token ((#"}",l), s) = ((RIGHTCURLY,l), s)
      | token ((#"{",l), s) = ((LEFTCURLY,l), s)
      | token ((#":",l), s) = ((COLON,l), s)
      | token ((#".",l), s) = ((DOT,l), s)
      | token ((#"|",l), s) = ((BAR,l), s)
      | token ((#"@",l), s) = ((APP,l), s)
      | token ((#"<",l), s) = ((LEFTANGLE,l), s)
      | token ((#">",l), s) = ((RIGHTANGLE,l), s)
      | token ((#"[",l), s) = ((LEFTBRACKET,l), s)
      | token ((#"]",l), s) = ((RIGHTBRACKET,l), s)
      | token ((#",",l), s) = ((COMMA,l), s)
      | token ((#"+",l), s) = ((SUM,l), s)
      | token ((#"*",l), s) = ((PRODUCT,l), s)
      | token ((#"_",l), s) = ((WILD,l), s)
      | token ((#"=",l), s) = 
        (case next s of
             ((#">",l),s) => ((GOESTO,l),s)
          | _ => raise Error ("Expected > after ="))
      | token ((#"-",l), s) = 
        (case next s of
             ((#">",l),s) => ((ARR,l),s)
          | _ => raise Error ("Expected > after -"))
      | token ((c,l), s) =
             if isNum c then lexNum (s, ord c - ord #"0", l)
             else if isAlpha c then lexAlpha (s, [c], l)
             else raise Error ("Illegal character at `" ^
                               concat (map Char.toString l) ^ "'")

    and lex s =
        S.delay (fn () => lex' (S.force s))

    (* process characters, skipping whitespace *)
    and lex' S.Nil = S.Nil
      | lex' (S.Cons ((#" ",_), s)) = lex' (S.force s)
      | lex' (S.Cons ((#"\r",_), s)) = lex' (S.force s)
      | lex' (S.Cons ((#"\t",_), s)) = lex' (S.force s)
      | lex' (S.Cons ((#"\v",_), s)) = lex' (S.force s)
      | lex' (S.Cons ((#"\n",_), s)) = lex' (S.force s)
      | lex' (S.Cons r) =
            let val (t, s) = token r
            in S.Cons (t, lex s) end

    fun tokenToString t = 
        case t of
            LET => "LET"
          | BE => "BE"
          | IN => "IN"
          | END => "END"
          | LPAREN => "LPAREN"
          | RPAREN => "RPAREN"
          | LEFTCURLY => "LEFTCURLY"
          | RIGHTCURLY => "RIGHTCURLY"
          | SEMICOLON => "SEMICOLON"
          | COLON => "COLON"
          | DOT => "DOT"
          | WITH => "WITH"
          | LAM => "LAM"
          | NUMBER k => "NUMBER(" ^ Int.toString k ^ ")"
          | VAR v => "VAR(" ^ v ^ ")"
          | GOESTO => "GOESTO"
          | BAR => "BAR"
          | SUCC => "SUCC"
          | ZERO => "ZERO"
          | NAT => "NAT"
          | ARR => "ARR"
          | APP => "APP"
          | PRODUCT => "PRODUCT"
          | SUM => "SUM"
          | LEFTANGLE => "LEFTANGLE"
          | RIGHTANGLE => "RIGHTANGLE"
          | COMMA => "COMMA"
          | CASE => "CASE"
          | INLEFT => "INLEFT"
          | INRIGHT => "INRIGHT"
          | LEFTBRACKET => "LEFTBRACKET"
          | RIGHTBRACKET => "RIGHTBRACKET"
          | UNIT => "UNIT"
          | FOLD => "FOLD"
          | REC => "REC"
          | FIX => "FIX" 
          | TRUE => "TRUE"
          | FALSE => "FALSE"
          | NIL => "NIL"
          | CONS => "CONS"
          | BOOL => "BOOL"
          | LIST => "LIST"
          | IS => "IS"
          | WILD => "WILD"
          | NAME => "NAME"
          | AS => "AS"
                
end;  (* structure Lexer *)
