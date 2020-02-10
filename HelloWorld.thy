theory HelloWorld
  imports IO
begin

section\<open>Hello, World!\<close>

text\<open>
  The idea of a \<^term>\<open>main :: unit io\<close> function is that, upon start of your program, you will be
  handed a value of type \<^typ>\<open>\<^url>\<close>. You can pass this world through your code and modify it.
  Be careful with the \<^typ>\<open>\<^url>\<close>, it's the only one we have.
\<close>


text\<open>The main function, defined in Isabelle. It should have the right type in Haskell.\<close>
definition main :: "unit io" where
  "main \<equiv> do {
               _ \<leftarrow> println (STR ''Hello World! What is your name?'');
               name \<leftarrow> getLine;
               println (STR ''Hello, '' + name + STR ''!'')
             }"

export_code main checking Haskell? SML

section\<open>Running the Generated Code\<close>
text\<open>The following examples show how to run the executed code outside Isabelle.\<close>

(*Maintainer note: We invoke the generated code ON PURPOSE from bash to demonstrate how to use
  the generated code from outside Isabelle.*)

export_code main in Haskell file "/tmp/exported_hs"
ML_val\<open>
val r = if Isabelle_System.bash "which runhaskell" = 0 then
  Isabelle_System.bash "cd /tmp/exported_hs && echo 'Cyber Cat 42' | runhaskell HelloWorld"
else 0;

if r <> 0 then
  raise (Fail ("example SML code did not run as expected, exit code was " ^ (Int.toString r)))
else ();
\<close>

export_code main in SML file "/tmp/exported.sml"

ML_val\<open>
val r = Isabelle_System.bash
          ("echo 'Super Goat 2000' | " ^
           "\"${POLYML_EXE?}\" --use /tmp/exported.sml --eval 'HelloWorld.main ()'");

if r <> 0 then
  raise (Fail ("example SML code did not run as expected, exit code was " ^ (Int.toString r)))
else ();
\<close>

end