theory HelloWorld
  imports IO_Monad
begin

section\<open>Hello, World!\<close>

text\<open>
  The idea of a \<^term>\<open>main :: unit IO\<close> function is that, upon start of your program, you will be
  handed a value of type \<^typ>\<open>real_world\<close>. You can pass this world through your code and modify it.
  Be careful with the \<^typ>\<open>real_world\<close>, it's the only one we have.
\<close>


text\<open>The main function, defined in Isabelle. It should have the right type in Haskell.\<close>
definition main :: "unit IO" where
  "main \<equiv> do {
               _ \<leftarrow> println (STR ''Hello World! What is your name?'');
               name \<leftarrow> getLine;
               println (STR ''Hello, '' + name + STR ''!'')
             }"

export_code main checking Haskell? SML

export_code main in Haskell file "/tmp/yolo_hs"
ML_val\<open>
if Isabelle_System.bash "which runhaskell" = 0 then
  Isabelle_System.bash "cd /tmp/yolo_hs && echo 'Cyber Cat 42' | runhaskell HelloWorld"
else 0
\<close>

export_code main in SML file "/tmp/yolo.sml"

ML_val\<open>
Isabelle_System.bash ("echo 'Super Goat 2000' | " ^
                      "\"${POLYML_EXE?}\" --use /tmp/yolo.sml --eval 'HelloWorld.main ()'")
\<close>

end