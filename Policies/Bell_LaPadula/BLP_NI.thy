subsection \<open>Proving Noninterference\<close>

theory BLP_NI
imports BLP_Monitor "../Noninterference/Noninterference"
begin

context BLP_Monitor
begin

text \<open>We can show that, in a specific sense, a Bell/LaPadula reference monitor satisfies a
noninterference policy.\<close>

text \<open>The lattice of security levels of a Bell/LaPadula policy can be interpreted as a flow policy
in the sense of Goguen-Meseguer: @{text "(l \<leadsto> l') \<longleftrightarrow> (l \<le> l')"}\<close>

definition FP :: "'level rel" where
  "FP = {(l, l'). l \<le> l'}"

text \<open>We now have to define the labeling of actions with security domains/levels. We could label
an action according to the object that is written to or read from, or according to the subject that
performs the action, or even according to a combination of both (i.e. take the supremum of the two
levels).

It turns out that we can show noninterference for each of these choices.

In the following, we choose the labeling according to subject. The intuition is that an observer on
level @{text l} may see the actions (and outputs of those actions) of all users with a clearance of
@{text l} and below, while the observer must not learn anything about actions of users in other
security levels.\<close>

primrec dom :: "('subj, 'obj, 'val) act \<Rightarrow> 'level" where
  "dom (R subj obj) = sc subj"
| "dom (W subj obj val) = sc subj"

sublocale NI init step out FP dom
unfolding FP_def
by (unfold_locales) (auto simp add: refl_on_def trans_def)

notation flow ("_ \<leadsto> _")

lemma [simp]: "(l \<leadsto> l') \<longleftrightarrow> (l \<le> l')"
unfolding FP_def by simp

text \<open>In order to show that the Bell/LaPadula monitor satisfies noninterference
wrt. this policy, we proceed by using the unwinding theorem.\<close>

text \<open>We choose an unwinding relation for each security level @{text l} so that two states are
equivalent iff they coincide on the values of objects with level @{text l} or below.\<close>

definition view :: "'level \<Rightarrow> ('obj, 'val) state rel" where
  "view l \<equiv> {(s, s'). (\<forall>obj. oc obj \<le> l \<longrightarrow> s obj = s' obj)}"

sublocale View_Partitioning init step out FP dom view
by (unfold_locales)
   (auto simp add: view_def intro!: equivI refl_onI symI transI)

notation view' ("_ \<sim>\<^bsub>_\<^esub> _")

text \<open>With these unwinding relations, we can show noninterference by proving
the unwinding conditions:\<close>

lemma oc: "output_consistent"
unfolding output_consistent_def
proof (intro allI impI)
  fix a s t
  assume "s \<sim>\<^bsub>dom a\<^esub> t"
  then show "out s a = out t a"
    by (cases a) (auto simp add: view_def intro: read_secure)
qed

lemma lr: "locally_respects_FP"
unfolding locally_respects_FP_def
proof (intro allI impI)
  fix s l a
  assume "(dom a, l) \<notin> FP"
  then show "s \<sim>\<^bsub>l\<^esub> (step s a)"
    by (cases a) (auto simp add: view_def intro: write_secure order_trans)
qed

lemma sc: "step_consistent"
unfolding step_consistent_def
proof (intro allI impI, elim conjE)
  fix s t l a
  assume "(dom a) \<leadsto> l"
     and "s \<sim>\<^bsub>l\<^esub> t"
  then show "(step s a) \<sim>\<^bsub>l\<^esub> (step t a)"
    by (cases a) (auto simp add: view_def)
qed

theorem monitor_secure: "NI_secure"
using oc lr sc
by (intro unwinding_theorem)

end

end
