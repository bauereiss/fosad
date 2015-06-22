subsection {* Example: A Reference Monitor for a Simple Language *}

theory Simple_Lang
imports Main
begin

subsubsection {* Language *}

type_synonym 'var state = "'var \<Rightarrow> integer"

datatype 'var expr =
  Var 'var
| Plus "'var expr" "'var expr"

primrec eval :: "'var state \<Rightarrow> 'var expr \<Rightarrow> integer" where
  "eval s (Var v) = s v"
| "eval s (Plus e1 e2) = eval s e1 + eval s e2"

primrec FV :: "'var expr \<Rightarrow> 'var set" where
  "FV (Var v) = {v}"
| "FV (Plus e1 e2) = FV e1 \<union> FV e2"

datatype ('var, 'dom) cmd =
  Assign 'var (dom: 'dom) "'var expr" ("_ :=\<^bsub>_\<^esub> _")

lemma "dom (Assign v d e) = d"
by auto

primrec execute :: "'var state \<Rightarrow> ('var, 'dom) cmd \<Rightarrow> 'var state" where
  "execute s (Assign v d e) = s(v := eval s e)"

lemma coincidence:
  assumes "\<forall>v \<in> FV e. s v = t v"
  shows "eval s e = eval t e"
using assms
by (induction e) auto

end
