theory HelloWorld_Proof
  imports HelloWorld
begin

text\<open>
  Apply some function \<^term>\<open>iofun\<close> to a specific world and return the new world
  (discarding the result of \<^term>\<open>iofun\<close>).\<close>
definition get_new_world :: "'\<alpha> io \<Rightarrow> \<^url> \<Rightarrow> \<^url>" where
  "get_new_world iofun world = snd (Rep_io iofun world)"

text\<open>Similar, but only get the result.\<close>
definition get_new_result :: "'\<alpha> io \<Rightarrow> \<^url> \<Rightarrow> '\<alpha>" where
  "get_new_result iofun world = fst (Rep_io iofun world)"

lemma get_new_world_Abs_io: "get_new_world (Abs_io f) world = snd (f world)"
  by(simp add: get_new_world_def Abs_io_inverse)

lemma get_new_world_then:
    "get_new_world (io\<^sub>1 \<then> io\<^sub>2) world = get_new_world io\<^sub>2 (get_new_world io\<^sub>1 world)"
  and get_new_result_then:
    "get_new_result (io\<^sub>1 \<then> io\<^sub>2) world = get_new_result io\<^sub>2 (get_new_world io\<^sub>1 world)"
  by (simp_all add: get_new_world_def get_new_result_def bind_def Abs_io_inverse split_beta)

lemma get_new_world_bind:
    "get_new_world (io\<^sub>1 \<bind> io\<^sub>2) world = get_new_world (io\<^sub>2 (get_new_result io\<^sub>1 world)) (get_new_world io\<^sub>1 world)"
  and get_new_result_bind:
    "get_new_result (io\<^sub>1 \<bind> io\<^sub>2) world = get_new_result (io\<^sub>2 (get_new_result io\<^sub>1 world)) (get_new_world io\<^sub>1 world)"
  by(simp_all add: get_new_world_def get_new_result_def bind_def Abs_io_inverse split_beta)

text\<open>
  With the appropriate assumptions about \<^const>\<open>println\<close> and \<^const>\<open>getLine\<close>,
  we can even prove something.
\<close>
locale io_stdinout =
  \<comment> \<open>We model stdin and stdout as part of the \<^typ>\<open>\<^url>\<close>.
     Note that we know nothing about \<^typ>\<open>\<^url>\<close>,
     we just model that we can find stdin and stdout somewhere in there.\<close>
  fixes get_stdout::"\<^url> \<Rightarrow> string list"
  and get_stdin::"\<^url> \<Rightarrow> string list"

  \<comment> \<open>Assumptions about stdin:
      Calling \<^const>\<open>println\<close> appends to the end of stdout and \<^const>\<open>getLine\<close> does not change anything.\<close>
assumes get_stdout_println[simp]:
    "get_stdout (get_new_world (println str) world) = get_stdout world@[String.explode str]"
  and get_stdout_getLine[simp]:
    "get_stdout (get_new_world getLine world) = get_stdout world"

  \<comment> \<open>Assumptions about stdin:
      Calling \<^const>\<open>println\<close> does not change anything and \<^const>\<open>getLine\<close> removes the first element
      from the stdin stream.\<close>
  and get_stdin_println[simp]:
    "get_stdin (get_new_world (println str) world) = get_stdin world"
  and get_stdin_getLine:
    "get_stdin world = inp#stdin \<Longrightarrow>
     get_stdin (get_new_world getLine world) = stdin \<and> get_new_result getLine world = String.implode inp"
begin

text\<open>Correctness of \<^const>\<open>main\<close>:
  If stdout is initially empty and only \<^term>\<open>''corny''\<close> will be typed into stdin,
  then the program will output: \<^term>\<open>[''Hello World! What is your name?'', ''Hello corny'']\<close>.
\<close>
lemma assumes stdout: "get_stdout world = []" and stdin: "get_stdin world = [''corny'']"
  shows "get_stdout (get_new_world main world) = [''Hello World! What is your name?'', ''Hello, corny!'']"
proof -
  let ?world1="get_new_world (println (STR ''Hello World! What is your name?'')) world"
  let ?world2="get_new_world getLine ?world1"
  from stdout have stdout_world2:
    "get_stdout ?world2 = [''Hello World! What is your name?'']"
    apply simp
    apply code_simp
    done
  from get_stdin_getLine[where stdin="[]", OF stdin] have stdin_world2:
    "get_new_result getLine ?world1 = String.implode ''corny''"
    by (simp add: get_stdin_getLine stdin)
  show ?thesis
    unfolding main_def using stdout
    apply(auto simp add: get_new_world_bind)
     apply code_simp
    apply (subst stdin_world2)
    apply (subst plus_literal.rep_eq)+
    apply code_simp
    done
qed
end

end