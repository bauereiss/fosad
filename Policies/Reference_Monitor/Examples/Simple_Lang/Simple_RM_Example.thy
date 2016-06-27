subsubsection {* Example instantiation *}

theory Simple_RM_Example
imports Simple_RM
begin

text \<open>As a concrete example, we consider a monitor with two domains and six variables.\<close>

datatype domain = D1 | D2

datatype var = A | B | C | X | Y | Z

text \<open>Information is allowed to flow from @{text D1} to @{text D2} (and from each domain to itself),
but not from @{text D2} to @{text D1}.\<close>

definition [simp]: "FP \<equiv> {(D1, D1), (D1, D2), (D2, D2)}"

text \<open>The variables are assigned as follows:\<close>

fun observe :: "domain \<Rightarrow> var set" where
  "observe D1 = {A, B, C}"
| "observe D2 = {A, B, C, X, Y, Z}"

fun alter :: "domain \<Rightarrow> var set" where
  "alter D1 = {A, B, C, X, Y, Z}"
| "alter D2 = {X, Y, Z}"

definition s0 :: "var state" where "s0 v = 0"

lemma [simp]: "\<And>d :: domain. d \<noteq> D1 \<longleftrightarrow> d = D2"
  and [simp]: "\<And>d :: domain. d \<noteq> D2 \<longleftrightarrow> d = D1"
using domain.exhaust by blast+

text \<open>In order to instantiate the simple reference monitor, we just have to show that the
concrete flow policy and the definitions of @{text alter} and @{text observe} fit together ---
which is automatic.\<close>

global_interpretation Simple_RM s0 observe alter FP
defines ex_check = "check" and ex_step = "step" and ex_out = "out"
proof
  show "refl FP" and "trans FP" by (auto simp add: refl_on_def trans_def)
next
  fix u v
  assume "(u, v) \<in> FP"
  then show "observe u \<subseteq> observe v" by auto
next
  fix n u v
  assume "n \<in> alter u" and "n \<in> observe v"
  then show "(u, v) \<in> FP" by auto
qed

text \<open>The fact that this instance is secure is then directly inherited from the general case.\<close>

theorem "NI_secure"
using monitor_secure .

text \<open>We can also export our definitions as executable code (in SML, OCaml, Haskell, or Scala),
and we can evaluate some example assignments.\<close>

export_code s0 step out in Scala
notation Assign ("_ :=\<^bsub>_\<^esub> _")

value "out s0 (X :=\<^bsub>D2\<^esub> (Minus (Plus (Var Y) (Var Z)) (Const 5)))"
  -- \<open>outputs ``- 5''\<close>
value "out s0 (A :=\<^bsub>D2\<^esub> (Minus (Plus (Var Y) (Var Z)) (Const 5)))"
  -- \<open>outputs ``0'', because the check fails\<close>
value "out s0 (A :=\<^bsub>D1\<^esub> (Minus (Plus (Var Y) (Var Z)) (Const 5)))"
  -- \<open>outputs ``0'', because the check fails\<close>
value "out s0 (A :=\<^bsub>D1\<^esub> (Minus (Plus (Var B) (Var C)) (Const 5)))"
  -- \<open>outputs ``- 5''\<close>

end
