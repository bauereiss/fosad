theory Simple_RM_Example
imports Simple_RM
begin

datatype domain = D1 | D2

datatype var = A | B | C | X | Y | Z

definition "FP \<equiv> {(D1, D1), (D1, D2), (D2, D2)}"

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

interpretation Simple_RM s0 observe alter FP
apply (unfold_locales)
by (auto simp add: FP_def refl_on_def trans_def)

theorem "NI_secure"
using monitor_secure .

end
