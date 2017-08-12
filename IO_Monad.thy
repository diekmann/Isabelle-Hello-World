(*DRAFT!*)
theory IO_Monad
  imports Main
    "~~/src/HOL/Library/Monad_Syntax"
    "~~/src/HOL/Library/Code_Char" (*must be loaded at the end*)
begin

(*Programming TLS in Isabelle/HOL by Andreas Lochbihler and Marc Züst uses a partial function (\<rightharpoonup>)!
typedecl real_world
typedef 'a IO = "UNIV :: (real_world \<rightharpoonup> 'a \<times> real_world) set" by simp
*)


text \<open>Definitions from @{url "https://wiki.haskell.org/IO_inside"}\<close>

typedecl real_world -- \<open>fake type. Dangerous.\<close>

text \<open>The set of all functions which take a @{typ real_world} and return an @{typ 'a} and a @{typ real_world}.\<close>
typedef 'a IO = "UNIV :: (real_world \<Rightarrow> 'a \<times> real_world) set"
proof -
  show "\<exists>x. x \<in> UNIV" by simp
qed


term Abs_IO --\<open>Takes a @{typ "(real_world \<Rightarrow> 'a \<times> real_world)"} and abstracts it to an @{typ "'a IO"}.\<close>
term Rep_IO --\<open>Unpacks an @{typ "'a IO"} to a @{typ "(real_world \<Rightarrow> 'a \<times> real_world)"}\<close>


(*context begin
qualified*)
definition bind :: "'a IO \<Rightarrow> ('a \<Rightarrow> 'b IO) \<Rightarrow> 'b IO" where [code del]:
  "bind action1 action2 = Abs_IO (\<lambda>world0.
                                  let (a, world1) = (Rep_IO action1) world0;
                                      (b, world2) = (Rep_IO (action2 a)) world1
                                  in (b, world2))"
(*
(>>=) :: IO a -> (a -> IO b) -> IO b
(action1 >>= action2) world0 =
   let (a, world1) = action1 world0
       (b, world2) = action2 a world1
   in (b, world2)
*)
hide_const (open) bind
adhoc_overloading bind IO_Monad.bind


code_printing constant IO_Monad.bind \<rightharpoonup> (Haskell) "_ >>= _"
                                    and (SML) "(let val res = _ in _ res end)" (*TODO really? Better not use name res*)


  
text\<open>We can now use monad syntax\<close>
lemma "bind (foo::'a IO) (\<lambda>a. bar a) = foo \<bind> (\<lambda>a. bar a)"
  by(simp)
  
text\<open>Make sure the code generator does not try to define @{typ "'a IO"} by itself, but always uses
     The full qualified Prelude.IO\<close>
code_printing type_constructor IO \<rightharpoonup> (Haskell) "Prelude.IO _"
                                 and (SML) "_"
code_reserved Haskell IO
code_reserved SML IO


text\<open>
In Isabelle, a @{typ string} is just a type synonym for @{typ "char list"}.
Consequently, translating a @{typ string} to Haskell yields a [Prelude.Char].
The Isabelle @{typ String.literal} gets translated to a Haskell String.\<close>

text\<open>Define a constant in Isabelle and provide a Haskell module which implements it.\<close>
consts println :: "String.literal \<Rightarrow> unit IO"
code_printing constant println \<rightharpoonup> (Haskell) "StdIO.println"
                              and (SML) "print (_ ^ \"\\n\")" (*adding newline manually*)
code_printing code_module StdIO \<rightharpoonup> (Haskell) {*
import qualified Prelude (putStrLn);
println = Prelude.putStrLn;
*}
code_reserved Haskell println StdIO
code_reserved SML println print


  
lemma "bind (println (String.implode ''foo''))
            (\<lambda>_.  println (String.implode ''bar''))
      = (println (String.implode ''foo'') \<bind> (\<lambda>_. println (String.implode ''bar'')))"
  by(simp)
lemma "do { _ \<leftarrow> println (String.implode ''foo'');
            println (String.implode ''bar'')} =
      (println (String.implode ''foo'') \<bind> (\<lambda>_. println (String.implode ''bar'')))" by simp 

text\<open>The main function, defined in Isabelle. It should have the right type in Haskell.\<close>
definition main :: "unit IO" where
  "main \<equiv> do {
               _ \<leftarrow> println (String.implode ''Hello World!'');
               println (String.implode ''Such command chaining.'')
             }"
  
  (*
setup_lifting type_definition_IO
value "term_of_class.term_of (x::real_world)"
value "term_of_class.term_of x"
value "term_of_class.term_of (Rep_IO::unit IO \<Rightarrow> real_world \<Rightarrow> unit \<times> real_world)"
value[code] "main"
  *)
export_code main in Haskell
export_code main in Haskell module_name "Main" file "code"
(*
  $ cd code
  $ runhaskell code/Main.hs
*)
  
  
export_code main in SML
export_code main in SML file test.sml
(*
  $ LD_PRELOAD=~/bin/Isabelle2016-1/contrib/polyml-5.6-1/x86-linux/libgmp.so.3  ~/bin/Isabelle2016-1/contrib/polyml-5.6/x86-linux/poly --use test.sml
*)
end