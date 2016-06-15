subsection {* Example: A Reference Monitor for a Simple Language *}

theory Simple_Lang
imports Main
begin

text \<open>In this example we will use the above theorem to prove the security of a very simplistic
programming language incorporating a reference monitor.\<close>

subsubsection {* Language *}

text \<open>As actions, we only consider assignments of the form @{text "n :=\<^bsub>d\<^esub> \<tau>"}, where @{text n}
is a variable name, @{text d} is a domain, and @{text \<tau>} is an expression. We only consider basic
expressions that are built using constants, variable references, subtraction, and addition:\<close>

datatype 'var expr =
  Var 'var
| Const integer
| Plus "'var expr" "'var expr"
| Minus "'var expr" "'var expr"

text \<open>For example, @{text "Minus (Plus (Var Y) (Var Z)) (Const 5)"} is an expression and denotes
the expression @{text "(Y + Z) - 5"}.

The state of the automaton is simply a mapping from variable names to integers.\<close>

type_synonym 'var state = "'var \<Rightarrow> integer"

text \<open>The function @{text \<E>} evaluates an expression in a given state.\<close>

fun \<E> :: "'var expr \<Rightarrow> 'var state \<Rightarrow> integer" where
  "\<E> (Var v) s = s v"
| "\<E> (Const c) s = c"
| "\<E> (Plus e1 e2) s = \<E> e1 s + \<E> e2 s"
| "\<E> (Minus e1 e2) s = \<E> e1 s - \<E> e2 s"

text \<open>The function @{text Vars} returns the set of variables appearing in an expression.\<close>

fun Vars :: "'var expr \<Rightarrow> 'var set" where
  "Vars (Var v) = {v}"
| "Vars (Const c) = {}"
| "Vars (Plus e1 e2) = Vars e1 \<union> Vars e2"
| "Vars (Minus e1 e2) = Vars e1 \<union> Vars e2"

text \<open>Actions are assignments of expressions to variables, annotated with a domain.\<close>

datatype ('var, 'dom) cmd =
  Assign 'var (dom: 'dom) "'var expr" ("_ :=\<^bsub>_\<^esub> _")

lemma "dom (v :=\<^bsub>d\<^esub> e) = d"
by auto

text \<open>The effect of an assignment @{text "v :=\<^bsub>d\<^esub> e"} in a state @{text s} is that the value of
@{text v} is updated to the evaluation of @{text "e"} in @{text s}.\<close>

fun execute :: "'var state \<Rightarrow> ('var, 'dom) cmd \<Rightarrow> 'var state" where
  "execute s (v :=\<^bsub>d\<^esub> e) = s(v := \<E> e s)"

text \<open>The following coincidence lemma will be useful: If two states coincide on the variables
appearing in an expression, then the result of evaluating the expression in both states is equal.\<close>

lemma coincidence:
  assumes "\<forall>v \<in> Vars e. s v = t v"
  shows "\<E> e s = \<E> e t"
using assms
by (induction e) auto

end
