theory IO_Monad
  imports Main
    "~~/src/HOL/Library/Monad_Syntax"
begin

text \<open>Definitions from @{url "https://wiki.haskell.org/IO_inside"}\<close>

text \<open>Model the real world with a fake type. Dangerous.
Models an arbitrary type we cannot reason about. Don't reason about the complete world!\<close>
typedecl real_world

text \<open>The set of all functions which take a @{typ real_world} and return an @{typ 'a} and a @{typ real_world}.\<close>
typedef 'a IO = "UNIV :: (real_world \<Rightarrow> 'a \<times> real_world) set"
proof -
  show "\<exists>x. x \<in> UNIV" by simp
qed
(*Programming TLS in Isabelle/HOL by Andreas Lochbihler and Marc Züst uses a partial function (\<rightharpoonup>)!
typedecl real_world
typedef 'a IO = "UNIV :: (real_world \<rightharpoonup> 'a \<times> real_world) set" by simp
We use a total function. This implies the dangerous assumption that all IO functions are total (e.g. terminate).
*)

text \<open>typedef gives us some convenient definitions. They must never end up in generated code.\<close>
term Abs_IO --\<open>Takes a @{typ "(real_world \<Rightarrow> 'a \<times> real_world)"} and abstracts it to an @{typ "'a IO"}.\<close>
term Rep_IO --\<open>Unpacks an @{typ "'a IO"} to a @{typ "(real_world \<Rightarrow> 'a \<times> real_world)"}\<close>


definition bind :: "'a IO \<Rightarrow> ('a \<Rightarrow> 'b IO) \<Rightarrow> 'b IO" where [code del]:
  "bind action1 action2 = Abs_IO (\<lambda>world0.
                                  let (a, world1) = (Rep_IO action1) world0;
                                      (b, world2) = (Rep_IO (action2 a)) world1
                                  in (b, world2))"
(* Haskell:
(>>=) :: IO a -> (a -> IO b) -> IO b
(action1 >>= action2) world0 =
   let (a, world1) = action1 world0
       (b, world2) = action2 a world1
   in (b, world2)
*)
hide_const (open) bind
adhoc_overloading bind IO_Monad.bind

text\<open>Don't expose our @{const IO_Monad.bind} definition to code. Use the built-in definitions of the target language.\<close>
code_printing constant IO_Monad.bind \<rightharpoonup> (Haskell) "_ >>= _"
                                    and (SML) "(let val res = _ in _ res end)" (*TODO really? Better not use name res*)


  
text\<open>We can now use monad syntax.\<close>
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



  (* failed attempt to get value[code] working
setup_lifting type_definition_IO
value "term_of_class.term_of (x::real_world)"
value "term_of_class.term_of x"
value "term_of_class.term_of (Rep_IO::unit IO \<Rightarrow> real_world \<Rightarrow> unit \<times> real_world)"
value[code] "main"
  *)
end