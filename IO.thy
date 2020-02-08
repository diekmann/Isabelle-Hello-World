theory IO
  imports Main
    "HOL-Library.Monad_Syntax"
begin

section\<open>Isabelle IO Monad inspired by Haskell\<close>
text \<open>Definitions from \<^url>\<open>https://wiki.haskell.org/IO_inside\<close>\<close>

subsection\<open>Real World\<close>
text \<open>Model the real world with a fake type. Dangerous.
Models an arbitrary type we cannot reason about. Don't reason about the complete world!\<close>
typedecl real_world (\<open>\<^url>\<close>)

subsection\<open>IO Monad\<close>
text \<open>The set of all functions which take a \<^typ>\<open>\<^url>\<close> and return an \<^typ>\<open>'\<alpha>\<close> and a \<^typ>\<open>\<^url>\<close>.\<close>

typedef '\<alpha> io = "UNIV :: (\<^url> \<Rightarrow> '\<alpha> \<times> \<^url>) set"
proof -
  show "\<exists>x. x \<in> UNIV" by simp
qed

text \<open>
  \<^emph>\<open>Programming TLS in Isabelle/HOL\<close> by Andreas Lochbihler and Marc Züst uses a partial function
  (\<open>\<rightharpoonup>\<close>).
  \<^theory_text>\<open>
    typedecl real_world
    typedef '\<alpha> io = "UNIV :: (real_world \<rightharpoonup> '\<alpha> \<times> real_world) set" by simp
  \<close>
  We use a total function. This implies the dangerous assumption that all IO functions are total
  (i.e., terminate).
\<close>

text \<open>
  The \<^theory_text>\<open>typedef\<close> above gives us some convenient definitions.
  They should not end up in generated code.
\<close>
term Abs_io \<comment> \<open>Takes a \<^typ>\<open>(\<^url> \<Rightarrow> '\<alpha> \<times> \<^url>)\<close> and abstracts it to an \<^typ>\<open>'\<alpha> io\<close>.\<close>
term Rep_io \<comment> \<open>Unpacks an \<^typ>\<open>'\<alpha> io\<close> to a \<^typ>\<open>(\<^url> \<Rightarrow> '\<alpha> \<times> \<^url>)\<close>\<close>


subsection\<open>Monad Operations\<close>
definition bind :: "'\<alpha> io \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> io) \<Rightarrow> '\<beta> io" where [code del]:
  "bind action\<^sub>1 action\<^sub>2 = Abs_io (\<lambda>world\<^sub>0.
                                  let (a, world\<^sub>1) = (Rep_io action\<^sub>1) world\<^sub>0;
                                      (b, world\<^sub>2) = (Rep_io (action\<^sub>2 a)) world\<^sub>1
                                  in (b, world\<^sub>2))"

text \<open>
  In Haskell:
  \<^verbatim>\<open>
    (>>=) :: IO a -> (a -> IO b) -> IO b
    (action1 >>= action2) world0 =
       let (a, world1) = action1 world0
           (b, world2) = action2 a world1
       in (b, world2)
  \<close>
\<close>

hide_const (open) bind
adhoc_overloading bind IO.bind

text \<open>Thanks to \<^theory_text>\<open>adhoc_overloading\<close>, we can use monad syntax.\<close>
lemma "bind (foo :: '\<alpha> io) (\<lambda>a. bar a) = foo \<bind> (\<lambda>a. bar a)"
  by simp


definition return :: "'\<alpha> \<Rightarrow> '\<alpha> io" where [code del]:
  "return a \<equiv> Abs_io (\<lambda>world. (a, world))"

hide_const (open) return

text \<open>
  In Haskell:
  \<^verbatim>\<open>
    return :: a -> IO a
    return a world0  =  (a, world0)
  \<close>
\<close>


subsection\<open>Monad Laws\<close>
lemma left_id:
  fixes f :: "'\<alpha> \<Rightarrow> '\<beta> io" \<comment> \<open>Make sure we use our \<^const>\<open>IO.bind\<close>.\<close>
  shows "(IO.return a \<bind> f) = f a"
  by(simp add: return_def IO.bind_def Abs_io_inverse Rep_io_inverse)

lemma right_id:
  fixes m :: "'\<alpha> io" \<comment> \<open>Make sure we use our \<^const>\<open>IO.bind\<close>.\<close>
  shows "(m \<bind> IO.return) = m"
  by(simp add: return_def IO.bind_def Abs_io_inverse Rep_io_inverse)
    
lemma bind_assoc:
  fixes m :: "'\<alpha> io" \<comment> \<open>Make sure we use our \<^const>\<open>IO.bind\<close>.\<close>
  shows "((m \<bind> f) \<bind> g) = (m \<bind> (\<lambda>x. f x \<bind> g))"
  by(simp add: IO.bind_def Abs_io_inverse Abs_io_inject fun_eq_iff split: prod.splits)


text \<open>
  Don't expose our \<^const>\<open>IO.bind\<close> definition to code. Use the built-in definitions of the
  target language.
\<close>
code_printing constant IO.bind \<rightharpoonup> (Haskell) "_ >>= _"
                                    and (SML) "bind"
            | constant IO.return \<rightharpoonup> (Haskell) "return"
                                    and (SML) "(() => _)"

text\<open>SML does not come with a bind function. We just define it (hopefully correct).\<close>
code_printing code_module Bind \<rightharpoonup> (SML) \<open>
fun bind x f () = f (x ()) ();
\<close>
code_reserved SML bind return
  
text\<open>
  Make sure the code generator does not try to define \<^typ>\<open>'\<alpha> io\<close> by itself, but always uses
  the one of the target language.
  For Haskell, this is the fully qualified Prelude.IO.
  For SML, we wrap it in a nullary function.
\<close>
code_printing type_constructor io \<rightharpoonup> (Haskell) "Prelude.IO _"
                                 and (SML) "unit -> _"

subsection\<open>Code Generator Setup and Basic Functions\<close>
text\<open>
In Isabelle, a \<^typ>\<open>string\<close> is just a type synonym for \<^typ>\<open>char list\<close>.
When translating a \<^typ>\<open>string\<close> to Haskell, Isabelle does not use Haskell's \<^verbatim>\<open>String\<close> or 
\<^verbatim>\<open>[Prelude.Char]\<close>. Instead, Isabelle serializes its own
  \<^verbatim>\<open>data Char = Char Bool Bool Bool Bool Bool Bool Bool Bool\<close>.
The resulting code will look just ugly.

To use the native strings of Haskell, we use the Isabelle type \<^typ>\<open>String.literal\<close>.
This gets translated to a Haskell \<^verbatim>\<open>String\<close>.

A string literal in Isabelle is created with \<^term>\<open>STR ''foo'' :: String.literal\<close>.
\<close>

text\<open>Define IO functions in Isabelle without implementation.\<close>

axiomatization
  println :: "String.literal \<Rightarrow> unit io" and
  getLine :: "String.literal io"

code_printing constant println \<rightharpoonup> (Haskell) "StdIO.println"
                              and (SML) "println"
            | constant getLine \<rightharpoonup> (Haskell) "StdIO.getLine"
                              and (SML) "getLine"

text \<open>A Haskell module named \<^verbatim>\<open>StdIO\<close> which just implements \<^verbatim>\<open>println\<close> and \<^verbatim>\<open>getLine\<close>.\<close>
code_printing code_module StdIO \<rightharpoonup> (Haskell) \<open>
module StdIO (println, getLine) where
import qualified Prelude (putStrLn, getLine)
println = Prelude.putStrLn
getLine = Prelude.getLine
\<close>                              and (SML) \<open>
fun println s () = TextIO.print (s ^ "\n");
fun getLine () = case (TextIO.inputLine TextIO.stdIn) of
                  SOME s => String.substring (s, 0, String.size s - 1)
                | NONE => raise Fail "getLine";
\<close>
code_reserved Haskell StdIO println getLine
code_reserved SML println print getLine TextIO

text\<open>Monad Syntax\<close>
lemma "bind (println (STR ''foo''))
            (\<lambda>_.  println (STR ''bar'')) =
       println (STR ''foo'') \<bind> (\<lambda>_. println (STR ''bar''))"
  by simp 
lemma "do { _ \<leftarrow> println (STR ''foo'');
            println (STR ''bar'')} =
      println (STR ''foo'') \<then> (println (STR ''bar''))"
  by simp

end