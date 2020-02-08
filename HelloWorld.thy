theory HelloWorld
  imports IO_Monad
begin

text\<open>The main function, defined in Isabelle. It should have the right type in Haskell.\<close>
definition main :: "unit IO" where
  "main \<equiv> do {
               _ \<leftarrow> println (String.implode ''Hello World! What is your name?'');
               name \<leftarrow> getLine;
               println (String.implode (''Hello '' @ (String.explode name)))
             }"

export_code main in Haskell
export_code main in Haskell module_name "Main" file "code"
(*
  $ cd code
  $ runhaskell Main.hs
*)

export_code main in SML
export_code main in SML file "code/main.sml"
(*
  $ cd code
  $ LD_PRELOAD=~/bin/Isabelle2016-1/contrib/polyml-5.6-1/x86-linux/libgmp.so.3 \
    ~/bin/Isabelle2016-1/contrib/polyml-5.6-1/x86-linux/poly --use main.sml
  Loads a interpreter and executes main during this. Hacky.
*)
end