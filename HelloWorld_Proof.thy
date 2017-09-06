theory HelloWorld_Proof
  imports HelloWorld
begin

text\<open>Apply a function @{term iofun} to a specific world and return the new world (discarding the result of @{term iofun}).\<close>
definition get_new_world :: "'a IO \<Rightarrow> real_world \<Rightarrow> real_world" where
  "get_new_world iofun world = snd (Rep_IO iofun world)"

text\<open>Similar, but only get the result.\<close>
definition get_new_result :: "'a IO \<Rightarrow> real_world \<Rightarrow> 'a" where
  "get_new_result iofun world = fst (Rep_IO iofun world)"

lemma get_new_world_Abs_IO: "get_new_world (Abs_IO f) world = snd (f world)"
  by(simp add: get_new_world_def Abs_IO_inverse)

lemma get_new_world_then:
    "get_new_world (io1 \<then> io2) world = get_new_world io2 (get_new_world io1 world)"
  and get_new_result_then:
    "get_new_result (io1 \<then> io2) world = get_new_result io2 (get_new_world io1 world)"
  by (simp_all add: get_new_world_def get_new_result_def bind_def Abs_IO_inverse split_beta)

lemma get_new_world_bind:
    "get_new_world (io1 \<bind> io2) world = get_new_world (io2 (get_new_result io1 world)) (get_new_world io1 world)"
  and get_new_result_bind:
    "get_new_result (io1 \<bind> io2) world = get_new_result (io2 (get_new_result io1 world)) (get_new_world io1 world)"
  by(simp_all add: get_new_world_def get_new_result_def bind_def Abs_IO_inverse split_beta)


text\<open>With the appropriate assumptions about @{const println} and @{const getLine}, we can even prove something.\<close>
locale yolo =
  --\<open>We model stdin and stdout as part of the @{typ real_world}. Note that we know nothing about @{typ real_world},
     we just model that we can find stdin and stdout somewhere in there.\<close>
  fixes get_stdout::"real_world \<Rightarrow> string list"
  and get_stdin::"real_world \<Rightarrow> string list"

  --\<open>Assumptions about stdin:
      Calling @{const println} appends to the end of stdout and @{const getLine} does not change anything.
    \<close>
assumes get_stdout_println:
    "get_stdout world = stdout \<Longrightarrow> get_stdout (get_new_world (println (STR str)) world) = stdout@[str]"
  and get_stdout_getLine:
    "get_stdout world = stdout \<Longrightarrow> get_stdout (get_new_world getLine world) = stdout"

  --\<open>Assumptions about stdin:
      Calling @{const println} does not change anything and @{const getLine} removes the first element from the stdin stream.
    \<close>
  and get_stdin_println:
    "get_stdin world = stdin \<Longrightarrow> get_stdin (get_new_world (println (STR str)) world) = stdin"
  and get_stdin_getLine:
    "get_stdin world = inp#stdin \<Longrightarrow>
     get_stdin (get_new_world getLine world) = stdin \<and> get_new_result getLine world = STR inp"
begin

lemma get_stdout_println_append:
      "get_stdout world = stdout \<Longrightarrow> str1 = STR str2 \<Longrightarrow>
        get_stdout (get_new_world (println str1) world) = stdout @ [str2]"
  by(simp add: get_stdout_println)

text\<open>Correctness of @{const main}:
  If stdout is initially empty and only @{term "''corny''"} will be typed into stdin, then the program will output:
  @{term "[''Hello World! What is your name?'', ''Hello corny'']"}.
\<close>
lemma assumes stdout: "get_stdout world = []" and stdin: "get_stdin world = [''corny'']"
  shows "get_stdout (get_new_world main world) = [''Hello World! What is your name?'', ''Hello corny'']"
proof -
  let ?world1="get_new_world (println (String.implode ''Hello World! What is your name?'')) world"
  let ?world2="get_new_world getLine ?world1"
  from get_stdout_println[OF stdout] have stdout_world2:
    "get_stdout ?world2 = [''Hello World! What is your name?'']"
    by (simp add: implode_def get_stdout_getLine)
  from get_stdin_getLine[where stdin="[]", OF stdin] have stdin_world2:
    "get_new_result getLine ?world1 = STR ''corny''"
    by (simp add: implode_def get_stdin_getLine get_stdin_println stdin)
  show ?thesis
    apply(simp add: main_def)
    apply(simp add: get_new_world_bind)
    apply(rule get_stdout_println_append[where stdout="[''Hello World! What is your name?'']", simplified])
    subgoal using stdout_world2 by(simp)
    using stdin_world2 by(simp add: implode_def STR_inverse)
qed
end

end