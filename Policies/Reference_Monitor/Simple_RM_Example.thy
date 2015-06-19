subsubsection {* Example instantiation *}

theory Simple_RM_Example
imports Simple_RM
begin

datatype domain = D1 | D2

datatype var = A | B | C | X | Y | Z

definition
 [simp]: "FP \<equiv> {(D1, D1), (D1, D2), (D2, D2)}"

primrec observe :: "domain \<Rightarrow> var set" where
  "observe D1 = {A, B, C}"
| "observe D2 = {A, B, C, X, Y, Z}"

primrec alter :: "domain \<Rightarrow> var set" where
  "alter D1 = {A, B, C, X, Y, Z}"
| "alter D2 = {X, Y, Z}"

definition s0 :: "var state" where
  "s0 v = 0"

lemma [simp]: "\<And>d :: domain. d \<noteq> D1 \<longleftrightarrow> d = D2"
  and [simp]: "\<And>d :: domain. d \<noteq> D2 \<longleftrightarrow> d = D1"
using domain.exhaust by blast+

text \<open>In order to instantiate the simple reference monitor, we just have to show that the
concrete flow policy and the definitions of @{text alter} and @{text observe} fit together ---
which is automatic.\<close>

interpretation Simple_RM s0 observe alter FP
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

end
