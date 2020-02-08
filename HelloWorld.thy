theory HelloWorld
  imports IO_Monad
begin

text\<open>The main function, defined in Isabelle. It should have the right type in Haskell.\<close>
definition main :: "unit IO" where
  "main \<equiv> do {
               _ \<leftarrow> println (STR ''Hello World! What is your name?'');
               name \<leftarrow> getLine;
               println (STR ''Hello '' + name)
             }"

export_code main checking Haskell SML


export_code main in SML file "/tmp/yolo.sml"

ML_val\<open>
Isabelle_System.bash ("echo -n 'Super Goat 2000' | " ^
                      "\"${POLYML_EXE?}\" --use /tmp/yolo.sml --eval 'HelloWorld.main ()'")
\<close>

end