theory Simple_Lang
imports Main
begin

type_synonym 'var state = "'var \<Rightarrow> integer"

datatype 'var expr =
  Var 'var
| Plus "'var expr" "'var expr"

datatype ('var, 'dom) cmd =
  Assign 'var 'dom "'var expr" ("_ :=\<^bsub>_\<^esub> _")

primrec eval :: "'var state \<Rightarrow> 'var expr \<Rightarrow> integer" where
  "eval s (Var v) = s v"
| "eval s (Plus e1 e2) = eval s e1 + eval s e2"

primrec execute :: "'var state \<Rightarrow> ('var, 'dom) cmd \<Rightarrow> 'var state" where
  "execute s (Assign v d e) = s(v := eval s e)"

primrec dom :: "('var, 'dom) cmd \<Rightarrow> 'dom" where
  "dom (Assign v d e) = d"

primrec FV :: "'var expr \<Rightarrow> 'var set" where
  "FV (Var v) = {v}"
| "FV (Plus e1 e2) = FV e1 \<union> FV e2"

lemma coincidence:
  assumes "\<forall>v \<in> FV e. s v = t v"
  shows "eval s e = eval t e"
using assms
by (induction e) auto

end
