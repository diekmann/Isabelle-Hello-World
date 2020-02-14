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

subsection\<open>Haskell\<close>

export_code main in Haskell

ML\<open>
val (files, _) =
  Code_Target.produce_code @{context} false [@{const_name main}] "Haskell" "Main" NONE []

val target = File.tmp_path (Path.basic ("export" ^ serial_string ()))

val ghc = getenv "ISABELLE_GHC";

val cmd =
  "cd " ^ Path.implode target ^ " && " ^
    Bash.string ghc ^ " Main.hs && " ^
    "(  echo 'Cyber Cat 42' | ./Main )";

Isabelle_System.mkdirs target;

app (fn ([file], content) =>
   let
     val path = Path.append target (Path.basic file)
   in
     File.write path content
   end) files;

val exitcode =
  if ghc <> "" then
    Isabelle_System.bash cmd
  else
    0;

if exitcode <> 0 then
  raise (Fail ("example Haskell code did not run as expected, " ^
                 "exit code was " ^ (Int.toString exitcode)))
else ()
\<close>


subsection\<open>SML\<close>

export_code main in SML

ML\<open>

val ([(_, content)], _) =
  Code_Target.produce_code @{context} false [@{const_name main}] "SML" "HelloWorld" NONE []

val target = File.tmp_path (Path.basic ("export" ^ serial_string ()))
val file = Path.append target (Path.basic "main.ML")

val cmd =
  "echo 'Super Goat 2000' | " ^
    "\"${POLYML_EXE?}\" --use " ^ Path.implode file ^
    " --eval 'HelloWorld.main ()'";

Isabelle_System.mkdirs target;
File.write file content;

val exitcode = Isabelle_System.bash cmd;

if exitcode <> 0 then
  raise (Fail ("example SML code did not run as expected, " ^
                 "exit code was " ^ (Int.toString exitcode)))
else ()
\<close>

end