theory IO_Monad
  imports Main
    "HOL-Library.Monad_Syntax"
begin

section\<open>Isabelle IO Monad inspired by Haskell\<close>
text \<open>Definitions from @{url "https://wiki.haskell.org/IO_inside"}\<close>

subsection\<open>Real World\<close>
text \<open>Model the real world with a fake type. Dangerous.
Models an arbitrary type we cannot reason about. Don't reason about the complete world!\<close>
typedecl real_world

subsection\<open>IO Monad\<close>
text \<open>The set of all functions which take a @{typ real_world} and return an @{typ 'a} and a @{typ real_world}.\<close>

typedef 'a IO = "UNIV :: (real_world \<Rightarrow> 'a \<times> real_world) set"
proof -
  show "\<exists>x. x \<in> UNIV" by simp
qed

text \<open>
  \<^emph>\<open>Programming TLS in Isabelle/HOL\<close> by Andreas Lochbihler and Marc Züst uses a partial function
  (\<open>\<rightharpoonup>\<close>).
  \<^theory_text>\<open>
    typedecl real_world
    typedef 'a IO = "UNIV :: (real_world \<rightharpoonup> 'a \<times> real_world) set" by simp
  \<close>
  We use a total function. This implies the dangerous assumption that all IO functions are total
  (i.e., terminate).
\<close>

text \<open>\<^theory_text>\<open>typedef\<close> gives us some convenient definitions. They should not end up in generated code.\<close>
term Abs_IO \<comment> \<open>Takes a @{typ "(real_world \<Rightarrow> 'a \<times> real_world)"} and abstracts it to an @{typ "'a IO"}.\<close>
term Rep_IO \<comment> \<open>Unpacks an @{typ "'a IO"} to a @{typ "(real_world \<Rightarrow> 'a \<times> real_world)"}\<close>


subsection\<open>Monad Operations\<close>
definition bind :: "'a IO \<Rightarrow> ('a \<Rightarrow> 'b IO) \<Rightarrow> 'b IO" where [code del]:
  "bind action1 action2 = Abs_IO (\<lambda>world0.
                                  let (a, world1) = (Rep_IO action1) world0;
                                      (b, world2) = (Rep_IO (action2 a)) world1
                                  in (b, world2))"

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
adhoc_overloading bind IO_Monad.bind

definition return :: "'a \<Rightarrow> 'a IO" where [code del]:
  "return a \<equiv> Abs_IO (\<lambda>world. (a, world))"

hide_const (open) return

text \<open>
  In Haskell:
  \<^verbatim>\<open>
    return :: a -> IO a
    return a world0  =  (a, world0)
  \<close>
\<close>


text \<open>We can use monad syntax.\<close>
lemma "bind (foo :: 'a IO) (\<lambda>a. bar a) = foo \<bind> (\<lambda>a. bar a)"
  by simp

subsection\<open>Monad Laws\<close>
lemma left_id:
  fixes f :: "'a \<Rightarrow> 'b IO" \<comment> \<open>Make sure we use our @{const IO_Monad.bind}.\<close>
  shows "(IO_Monad.return a \<bind> f) = f a"
  by(simp add: return_def IO_Monad.bind_def Abs_IO_inverse Rep_IO_inverse)

lemma right_id:
  fixes m :: "'a IO" \<comment> \<open>Make sure we use our @{const IO_Monad.bind}.\<close>
  shows "(m \<bind> IO_Monad.return) = m"
  by(simp add: return_def IO_Monad.bind_def Abs_IO_inverse Rep_IO_inverse)
    
lemma bind_assoc:
  fixes m :: "'a IO" \<comment> \<open>Make sure we use our @{const IO_Monad.bind}.\<close>
  shows "((m \<bind> f) \<bind> g) = (m \<bind> (\<lambda>x. f x \<bind> g))"
  by(simp add: IO_Monad.bind_def Abs_IO_inverse Abs_IO_inject fun_eq_iff split: prod.splits)


text \<open>
  Don't expose our @{const IO_Monad.bind} definition to code. Use the built-in definitions of the
  target language.
\<close>
code_printing constant IO_Monad.bind \<rightharpoonup> (Haskell) "_ >>= _"
                                    and (SML) "bind"
            | constant IO_Monad.return \<rightharpoonup> (Haskell) "return"
                                    and (SML) "(() => _)"

text\<open>SML does not come with a bind function. We just define it (hopefully correct).\<close>
code_printing code_module Bind \<rightharpoonup> (SML) \<open>
fun bind x f () = f (x ()) ();
\<close>
code_reserved SML bind return
  
text\<open>
  Make sure the code generator does not try to define @{typ "'a IO"} by itself, but always uses
  the one of the target language.
  For Haskell, this is the full qualified Prelude.IO.
  For SML, we just ignore the IO.
\<close>
code_printing type_constructor IO \<rightharpoonup> (Haskell) "Prelude.IO _"
                                 and (SML) "unit -> _"
code_reserved Haskell IO
code_reserved SML IO

subsection\<open>Code Generator Setup and Basic Functions\<close>
text\<open>
In Isabelle, a @{typ string} is just a type synonym for @{typ "char list"}.
When translating a @{typ string} to Haskell, Isabelle does not use Haskell's \<^verbatim>\<open>String\<close> or 
\<^verbatim>\<open>[Prelude.Char]\<close>. Instead, Isabelle serializes its own
  \<^verbatim>\<open>data Char = Char Bool Bool Bool Bool Bool Bool Bool Bool\<close>.
The resulting code will look just ugly.

To use the native strings of Haskell, we use the Isabelle type @{typ String.literal}.
This gets translated to a Haskell \<^verbatim>\<open>String\<close>.

A string literal in Isabelle is created with \<^term>\<open>STR ''foo'' :: String.literal\<close>.
\<close>

text\<open>Define IO functions in Isabelle without implementation.\<close>

axiomatization
  println :: "String.literal \<Rightarrow> unit IO" and
  getLine :: "String.literal IO"

code_printing constant println \<rightharpoonup> (Haskell) "StdIO.println"
                              and (SML) "println" (*adding newline manually*)
            | constant getLine \<rightharpoonup> (Haskell) "StdIO.getLine"
                              and (SML) "getLine"

text \<open>A Haskell module named StdIO which just implements println and getLine.\<close>
code_printing code_module StdIO \<rightharpoonup> (Haskell) \<open>
import qualified Prelude (putStrLn, getLine);
println = Prelude.putStrLn;
getLine = Prelude.getLine;
\<close>                              and (SML) \<open>
fun println s () = TextIO.print (s ^ "\n");
fun getLine () = case (TextIO.inputLine TextIO.stdIn) of
                  SOME s => s
                | NONE => raise Fail "getLine";
\<close>
code_reserved Haskell StdIO println getLine
code_reserved SML println print getLine TextIO

text\<open>Monad Syntax\<close>
lemma "bind (println (String.implode ''foo''))
            (\<lambda>_.  println (String.implode ''bar''))
      = (println (String.implode ''foo'') \<bind> (\<lambda>_. println (String.implode ''bar'')))"
  by(simp)
lemma "do { _ \<leftarrow> println (String.implode ''foo'');
            println (String.implode ''bar'')} =
      (println (String.implode ''foo'') \<then> (println (String.implode ''bar'')))" by simp 

end