theory HelloWorld
  imports Main "~~/src/HOL/Library/Code_Char"
begin

(*copied from Programming TLS in Isabelle/HOL by Andreas Lochbihler and Marc Züst*)
typedecl real_world
typedef 'a IO = "UNIV :: (real_world \<rightharpoonup> 'a \<times> real_world) set" by simp

text\<open>Make sure the code generator does not try to define @{typ "'a IO"} by itself, but always uses
     The full qualified Prelude.IO\<close>
code_printing type_constructor IO \<rightharpoonup> (Haskell) "Prelude.IO _"

text\<open>Define a constant in Isabelle and provide a Haskell module which implements it.\<close>
consts println :: "String.literal \<Rightarrow> unit IO"
code_printing constant println \<rightharpoonup> (Haskell) "StdIO.println"
code_printing code_module StdIO \<rightharpoonup> (Haskell) {*
import qualified Prelude (putStrLn);
println = Prelude.putStrLn;
*}
code_reserved Haskell StdIO IO

text\<open>The main function, defined in Isabelle. It should have the right type in Haskell.\<close>
definition main :: "unit IO" where
  "main \<equiv> println (String.implode ''Hello World'')"

export_code main in Haskell
export_code main in Haskell module_name "Main" file "code"

(*
  $ cd code
  $ runhaskell code/Main.hs
*)
end