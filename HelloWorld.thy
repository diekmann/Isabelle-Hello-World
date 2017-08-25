theory HelloWorld
  imports IO_Monad
    "~~/src/HOL/Library/Code_Char" (*must be loaded at the end*)
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




text\<open>With the appropriate assumptions about @{const println} and @{const getLine}, we can even prove something.\<close>
locale yolo =
  --\<open>We model stdin and stdout as part of the @{typ real_world}. Note that we know nothing about @{typ real_world},
     we just model that we can find stdin and stdout somewhere in there.\<close>
  fixes get_stdout::"real_world \<Rightarrow> string list"
  and get_stdin::"real_world \<Rightarrow> string list"

  --\<open>Assumptions about stdin:
      Calling @{const println} appends to the end of stdout and @{const getLine} does not change anything.
    \<close>
  assumes get_stdout_println: "get_stdout world = stdout \<Longrightarrow> get_stdout (snd (Rep_IO (println (STR str)) world)) = (stdout@[str])"
  and get_stdout_getLine: "get_stdout world = stdout \<Longrightarrow> get_stdout (snd (Rep_IO getLine world)) = stdout"

  --\<open>Assumptions about stdin:
      Calling @{const println} does not change anything and @{const getLine} removes the first element from the stdin stream.
    \<close>
  and get_stdin_println: "get_stdin world = stdin \<Longrightarrow> get_stdin (snd (Rep_IO (println (STR str)) world)) = stdin"
  and get_stdin_getLine: "get_stdin world = inp#stdin \<Longrightarrow>
                            get_stdin (snd (Rep_IO getLine world)) = stdin \<and> fst (Rep_IO getLine world) = STR inp"
begin

lemma get_stdout_println_append:
      "get_stdout world = stdout \<Longrightarrow> str1 = STR str2 \<Longrightarrow>
        get_stdout (snd (Rep_IO (println str1) world)) = stdout @ [str2]"
  by(simp add: get_stdout_println)

text\<open>Correctness of @{const main}:
  If stdout is initially empty and only @{term "''corny''"} will be typed into stdin, then the program will output:
  @{term "[''Hello World! What is your name?'', ''Hello corny'']"}.
\<close>
lemma assumes stdout: "get_stdout world = []" and stdin: "get_stdin world = [''corny'']"
  shows "get_stdout (snd ((Rep_IO main) world)) = [''Hello World! What is your name?'', ''Hello corny'']"
proof -
  let ?world1="snd (Rep_IO (println (String.implode ''Hello World! What is your name?'')) world)"
  let ?world2="snd (Rep_IO getLine ?world1)"
  from get_stdout_println[OF stdout] have stdout_world2:
    "get_stdout ?world2 = [''Hello World! What is your name?'']"
    apply (simp add: implode_def)
    by (simp add: get_stdout_getLine)
  from get_stdin_getLine[where stdin="[]", OF stdin] have stdin_world2:
    "fst (Rep_IO getLine ?world1) = STR ''corny''"
    apply (simp add: implode_def)
    using get_stdin_getLine get_stdin_println stdin by blast
  show ?thesis
    apply(simp add: main_def)
    apply(simp add: bind_def)
    apply(simp add: Abs_IO_inverse)
    apply(case_tac "Rep_IO (println (String.implode ''Hello World! What is your name?'')) world", simp, rename_tac world1)
    apply(case_tac "Rep_IO getLine world1", simp, rename_tac inp world2)
    apply(rule get_stdout_println_append[where stdout="[''Hello World! What is your name?'']", simplified])
    subgoal using stdout_world2 by simp
    apply(insert stdin_world2)
    by(simp add: implode_def STR_inverse)
qed
end

end