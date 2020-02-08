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

end