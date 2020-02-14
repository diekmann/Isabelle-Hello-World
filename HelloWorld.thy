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


section\<open>Generating Code\<close>

text\<open>Checking that the generated code compiles.\<close>
export_code main checking Haskell? SML


subsection\<open>Haskell\<close>

export_code main in Haskell file "/tmp/exported_hs"

text\<open>The generated helper module \<^file>\<open>/tmp/exported_hs/StdIO.hs\<close> is shown below.\<close>
text_raw\<open>\verbatiminput{/tmp/exported_hs/StdIO.hs}\<close>
 
text\<open>The generated main file \<^file>\<open>/tmp/exported_hs/HelloWorld.hs\<close> is shown below.\<close>
text_raw\<open>\verbatiminput{/tmp/exported_hs/HelloWorld.hs}\<close>


subsection\<open>SML\<close>

export_code main in SML file "/tmp/exported.sml"

text\<open>The generated SML code in \<^file>\<open>/tmp/exported.sml\<close> is shown below.\<close>
text_raw\<open>\verbatiminput{/tmp/exported.sml}\<close>


end