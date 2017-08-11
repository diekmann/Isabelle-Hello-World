theory HelloWorld
  imports Main "~~/src/HOL/Library/Code_Char"
begin

typedecl real_world
  (*copied from Programming TLS in Isabelle/HOL by Andreas Lochbihler and Marc Züst*)
typedef 'a IO = "UNIV :: (real_world \<rightharpoonup> 'a \<times> real_world) set" by simp

code_printing type_constructor IO \<rightharpoonup> (Haskell) "Prelude.IO _"

consts println :: "String.literal \<Rightarrow> unit IO"
code_printing constant println \<rightharpoonup> (Haskell) "StdIO.println"
code_printing code_module StdIO \<rightharpoonup> (Haskell) {*
import qualified Prelude (putStrLn);
println = Prelude.putStrLn;
*}
code_reserved Haskell StdIO IO

definition "main \<equiv> println (String.implode ''Hello World'')"

export_code main in Haskell
export_code main in Haskell module_name "Main" file "code"

(*
  $ cd code
  $ runhaskell code/Main.hs
*)
end