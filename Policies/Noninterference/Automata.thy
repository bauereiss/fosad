section {* Basic automata *}

theory Automata
imports Main
begin

text \<open>We consider automata defined by a type @{text "'state"} (corresponding to a non-empty set)
of states, a type @{text "'act"} of actions, a type @{text "'out"} of outputs, a starting state
@{text s0}, a step function @{text step}, and an output function @{text out}.\footnote{The
Isabelle command @{text locale} opens a new context where we can fix variables and/or define
assumptions. We can use these variables and assumptions inside the context, and we can reuse
and extend the context later by referring to its name (in this case @{text "Automaton"}).
We can also @{emph \<open>instantiate\<close>} a context (using the command @{text \<open>interpretation\<close>},
or @{emph \<open>sublocale\<close>} if we are inside another context): We then have to prove that the
assumptions hold, and afterwards, we are allowed to use the definitions and theorems from
inside the context.}\<close>

locale Automaton =
  fixes s0 :: "'state"
    and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'state"
    and out :: "'state \<Rightarrow> 'act \<Rightarrow> 'out"
begin

text \<open>We define @{text "run s \<alpha>"} so that it returns the state we reach when performing the
action sequence @{text \<alpha>}, beginning in the state @{text s}.\<close>

text \<open>The function @{text run} is defined recursively. In Isabelle, the empty list is denoted
as @{text "[]"}, the addition of an @{emph \<open>element\<close>} @{text a} at the beginning of a list
@{text \<alpha>} is denoted as @{text "a # \<alpha>"}, and the concatenation of two @{emph \<open>lists\<close>}
@{text \<alpha>} and @{text \<beta>} is denoted as @{text "\<alpha> @ \<beta>"}.\<close>

fun run :: "'state \<Rightarrow> 'act list \<Rightarrow> 'state" where
  "run s [] = s"
| "run s (a # \<alpha>) = run (step s a) \<alpha>"

text \<open>After writing down definitions, Isabelle allows us to prove properties of them. For example,
we can (almost\footnote{We tell Isabelle to perform induction over @{text \<alpha>}. Moreover, we
tell Isabelle to generalize the induction hypothesis to arbitrary states @{text s}, because
we need to apply the induction hypothesis not for the original @{text s}, but for the successor
state reached after performing the first action of the trace.}) automatically prove that we can
concatenate two traces of actions, if the first trace ends in the starting state of the second.\<close>

lemma "\<lbrakk>run s \<alpha> = t \<and> run t \<beta> = u\<rbrakk> \<Longrightarrow> run s (\<alpha> @ \<beta>) = u"
by (induction \<alpha> arbitrary: s) auto

text \<open>Note that free variables in lemmas are implicitly universally quantified, i.e.\ this lemma
holds @{emph \<open>for all\<close>} \<open>s\<close>, \<open>t\<close>, \<open>u\<close>, \<open>\<alpha>\<close>, and \<open>\<beta>\<close>.\<close>

end

end
