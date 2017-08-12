theory HelloWorld
  imports IO_Monad
    "~~/src/HOL/Library/Code_Char" (*must be loaded at the end*)
begin

  text\<open>The main function, defined in Isabelle. It should have the right type in Haskell.\<close>
definition main :: "unit IO" where
  "main \<equiv> do {
               _ \<leftarrow> println (String.implode ''Hello World!'');
               println (String.implode ''Such command chaining.'')
             }"

export_code main in Haskell
export_code main in Haskell module_name "Main" file "code"
(*
  $ cd code
  $ runhaskell code/Main.hs
*)


export_code main in SML
export_code main in SML file "code/main.sml"
(*
  $ LD_PRELOAD=~/bin/Isabelle2016-1/contrib/polyml-5.6-1/x86-linux/libgmp.so.3 \
    ~/bin/Isabelle2016-1/contrib/polyml-5.6-1/x86-linux/poly --use main.sml
*)
end