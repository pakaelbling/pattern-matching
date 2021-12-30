signature TOP =
sig

    (* interactive loop *)

    (* just print the same expression back *)
    val loop_print : unit -> unit 

    (* just type check *)
    val loop_type  : unit -> unit 

    (* type check the input program, then,
       if it was well-typed, 
       try to evaluate the program to a value, and then
       show the final value and its type (which is
       determined by re-typechecking the value).
       *)
    val loop_eval  : unit -> unit 

    (* Starting with the initial program, 
       show each step of evaluation with its type
       (which is determined by re-typechecking after each step).
       Stops when the result of a step is ill-typed.  

       By preservation, these types *should* all be the same,
       but if they're not, it can be helpful for finding bugs.
       *)
    val loop_step  : unit -> unit

    (* *Ignoring the type checker*, 
       try to evaluate the program to a value,
       and then show the final value.

       You can use this to test your operational semantics
       if you want to work on that first or 
       if your type checker isn't working.
       *)
    val loop_eval_no_typechcker : unit -> unit

    (* *Ignoring the type checker*, show each step of evaluation.

       You can use this to test your operational semantics
       if you want to work on that first or 
       if your type checker isn't working.
       *)
    val loop_step_no_typechecker : unit -> unit

    (* read an EXP source file *)
    val file_print : string -> unit
    val file_type  : string -> unit
    val file_eval  : string -> unit
    val file_step  : string -> unit
    val file_eval_no_typechecker  : string -> unit
    val file_step_no_typechecker  : string -> unit

end;  (* signature TOP *)

structure Top :> TOP =
struct

    type exp = Syntax.exp

    type action = exp -> unit

    fun typing (e : exp) : string =
        " : " ^ Print.typToString ( Check.check e) handle Check.TypeError s => s

    exception Stop of string
                
    fun typingFail (e : exp) : string =
        " : " ^ Print.typToString ( Check.check e) handle Check.TypeError s => raise Stop (Print.expToString e ^ " has a type error: " ^ s)

  (* A few actions *)

  fun show (e : exp) : unit =
      List.app print [Print.expToString e, ";\n"]

  fun showType (e : exp) : unit =
      List.app print [Print.expToString e, " ", typing e, "\n"]

  fun showTypeFail (e : exp) : unit =
      List.app print [Print.expToString e, " ", typingFail e, "\n"]
      
  fun stepToValue (e : exp) : exp =
      case Step.progress e of
          Step.Done => e
        | Step.Stepped e' => stepToValue e'

  (* do the action on the resulting value *)
  fun eval (action : exp -> unit) (e : exp) : unit =
      (print "input expression:\n"; showType e;  
       print "evaluates to "; action (stepToValue e); 
       print "\n")

  fun evalFail (action : exp -> unit) (e : exp) : unit =
      (print "input expression:\n"; showTypeFail e;  
       print "evaluates to "; action (stepToValue e); 
       print "\n")
      
  (* do the action and then wait for input *)
  fun wait (action : exp -> unit) (e : exp) : unit =
      (action e;
       print "Press return:";
       TextIO.inputLine TextIO.stdIn;
       ())

  (* do the action before each step *)
  fun step (action : exp -> unit) (e : exp) : unit =
          (action e;
           case Step.progress e of
               Step.Done => ()
             | Step.Stepped e' => step action e')
          
  (* Running the actions on an interactive loop or a file *)

  fun loop (action : exp -> unit) : unit =
         Stream.app action
         (Input.promptKeybd "T>" "...  >"
         (fn s => Parse.parse (Lexer.lex s)))

  fun loopFile (name : string) (action : exp -> unit) : unit =
         Stream.app action
         (Parse.parse(Lexer.lex(Input.readFile name)))

    fun hdl (f : (exp -> unit) -> unit) (x : exp -> unit) = (f x)
            handle Lexer.Error s => print ("\nLexer error: " ^ s ^ "\n")
                 | Parse.Error s => print ("\nParse error: " ^ s ^ "\n")
                 | Stop s => print ("The expression\n" ^ s ^ "\nis ill-typed -- not continuing to evaluate it.  Run {loop,file}_{step,eval}_no_typechecker instead if you want to evaluate it.\n")

    fun loop_print () = hdl loop show
    fun loop_type () = hdl loop showType
    fun loop_eval () = hdl loop (evalFail showType)
    fun loop_step () = hdl loop (step (wait showTypeFail))
    fun loop_eval_no_typechcker () = hdl loop (eval showType)
    fun loop_step_no_typechecker () = hdl loop (step (wait showType))

    fun file_print f = hdl (loopFile f) show
    fun file_type f = hdl (loopFile f) showType
    fun file_eval f = hdl (loopFile f) (evalFail showType)
    fun file_step f = hdl (loopFile f) (step (wait showTypeFail))
    fun file_eval_no_typechecker f = hdl (loopFile f) (eval show)
    fun file_step_no_typechecker f = hdl (loopFile f) (step (wait show))

end;  


