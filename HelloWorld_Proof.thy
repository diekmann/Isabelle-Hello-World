theory HelloWorld_Proof
  imports HelloWorld
begin

text\<open>
  Apply some function \<^term>\<open>iofun\<close> to a specific world and return the new world
  (discarding the result of \<^term>\<open>iofun\<close>).
\<close>
definition exec :: "'\<alpha> io \<Rightarrow> \<^url> \<Rightarrow> \<^url>" where
  "exec iofun world = snd (Rep_io iofun world)"

text\<open>Similar, but only get the result.\<close>
definition eval :: "'\<alpha> io \<Rightarrow> \<^url> \<Rightarrow> '\<alpha>" where
  "eval iofun world = fst (Rep_io iofun world)"

lemma exec_Abs_io: "exec (Abs_io f) world = snd (f world)"
  by(simp add: exec_def Abs_io_inverse)

lemma exec_then:
    "exec (io\<^sub>1 \<then> io\<^sub>2) world = exec io\<^sub>2 (exec io\<^sub>1 world)"
  and eval_then:
    "eval (io\<^sub>1 \<then> io\<^sub>2) world = eval io\<^sub>2 (exec io\<^sub>1 world)"
  by (simp_all add: exec_def eval_def bind_def Abs_io_inverse split_beta)

lemma exec_bind:
    "exec (io\<^sub>1 \<bind> io\<^sub>2) world = exec (io\<^sub>2 (eval io\<^sub>1 world)) (exec io\<^sub>1 world)"
  and eval_bind:
    "eval (io\<^sub>1 \<bind> io\<^sub>2) world = eval (io\<^sub>2 (eval io\<^sub>1 world)) (exec io\<^sub>1 world)"
  by(simp_all add: exec_def eval_def bind_def Abs_io_inverse split_beta)

text\<open>
  With the appropriate assumptions about \<^const>\<open>println\<close> and \<^const>\<open>getLine\<close>,
  we can even prove something.
\<close>
locale io_stdio =
  \<comment> \<open>We model \<^verbatim>\<open>STDIN\<close> and \<^verbatim>\<open>STDOUT\<close> as part of the \<^typ>\<open>\<^url>\<close>.
     Note that we know nothing about \<^typ>\<open>\<^url>\<close>,
     we just model that we can find \<^verbatim>\<open>STDIN\<close> and \<^verbatim>\<open>STDOUT\<close> somewhere in there.\<close>
  fixes stdout_of::"\<^url> \<Rightarrow> string list"
  and stdin_of::"\<^url> \<Rightarrow> string list"

  \<comment> \<open>Assumptions about \<^verbatim>\<open>STDIN\<close>:
      Calling \<^const>\<open>println\<close> appends to the end of \<^verbatim>\<open>STDOUT\<close> and \<^const>\<open>getLine\<close> does not change anything.\<close>
assumes stdout_of_println[simp]:
    "stdout_of (exec (println str) world) = stdout_of world@[String.explode str]"
  and stdout_of_getLine[simp]:
    "stdout_of (exec getLine world) = stdout_of world"

  \<comment> \<open>Assumptions about \<^verbatim>\<open>STDIN\<close>:
      Calling \<^const>\<open>println\<close> does not change anything and \<^const>\<open>getLine\<close> removes the first element
      from the \<^verbatim>\<open>STDIN\<close> stream.\<close>
  and stdin_of_println[simp]:
    "stdin_of (exec (println str) world) = stdin_of world"
  and stdin_of_getLine:
    "stdin_of world = inp#stdin \<Longrightarrow>
     stdin_of (exec getLine world) = stdin \<and> eval getLine world = String.implode inp"
begin

  text\<open>Correctness of \<^const>\<open>main\<close>:
    If \<^verbatim>\<open>STDOUT\<close> is initially empty and only \<^term>\<open>''corny''\<close> will be typed into \<^verbatim>\<open>STDIN\<close>,
    then the program will output: \<^term>\<open>[''Hello World! What is your name?'', ''Hello corny'']\<close>.
  \<close>
  lemma
    assumes stdout: "stdout_of world = []"
         and stdin: "stdin_of world = [''corny'']"
    shows "stdout_of (exec main world) = [''Hello World! What is your name?'', ''Hello, corny!'']"
  proof -
    let ?world1="exec (println (STR ''Hello World! What is your name?'')) world"
    let ?world2="exec getLine ?world1"
    have stdout_world2:
      "literal.explode STR ''Hello World! What is your name?'' = ''Hello World! What is your name?''"
      by code_simp
    from stdin_of_getLine[where stdin="[]", OF stdin] have stdin_world2:
      "eval getLine ?world1 = String.implode ''corny''"
      by (simp add: stdin_of_getLine stdin)
    show ?thesis
      unfolding main_def
      apply(simp add: exec_bind)
      apply(simp add: stdout)
      apply(simp add: stdout_world2 stdin_world2)
      apply(simp add: plus_literal.rep_eq)
      apply code_simp
      done
  qed
end

end