theory BLP_Monitor
imports Noninterference
begin

datatype perm = Read | Write

datatype ('s, 'o, 'v) act = R 's 'o | W 's 'o 'v

datatype 'v out = Val 'v | Ok | Err

type_synonym ('o, 'v) state = "'o \<Rightarrow> 'v"

locale BLP_Monitor =
  fixes sc :: "'subj \<Rightarrow> ('level :: order)"
    and oc :: "'obj \<Rightarrow> 'level"
    and M :: "'subj \<Rightarrow> 'obj \<Rightarrow> perm set"
    and init :: "('obj, 'val) state"
  assumes read_secure: "Read \<in> M s obj \<Longrightarrow> oc obj \<le> sc s"
      and write_secure: "Write \<in> M s obj \<Longrightarrow> sc s \<le> oc obj"
begin

primrec step :: "('obj, 'val) state
              \<Rightarrow> ('subj, 'obj, 'val) act
              \<Rightarrow> ('obj, 'val) state"
where
  "step s (R subj obj) = s"
| "step s (W subj obj val) = (if sc subj \<le> oc obj
                              then s(obj := val)
                              else s)"

primrec out :: "('obj, 'val) state
             \<Rightarrow> ('subj, 'obj, 'val) act
             \<Rightarrow> ('val) out"
where
  "out s (R subj obj) = (if oc obj \<le> sc subj
                         then Val (s obj)
                         else Err)"
| "out s (W subj obj val) = (if oc obj \<le> sc subj
                             then Ok
                             else Err)"

text \<open>The initial state and the step and output functions above define
an automaton: a Bell/LaPadula reference monitor.\<close>

sublocale Automaton init step out .

text \<open>The lattice of security levels can be interpreted as a flow policy
in the sense of Goguen-Meseguer.\<close>

definition FP :: "'level rel" where
  "FP = {(l, l'). l \<le> l'}"

primrec dom :: "('subj, 'obj, 'val) act \<Rightarrow> 'level" where
  "dom (R subj obj) = oc obj"
| "dom (W subj obj val) = oc obj"

sublocale NI init step out FP dom
unfolding FP_def
by (unfold_locales) (auto simp add: refl_on_def trans_def)

notation flow ("_ \<leadsto> _")

lemma [simp]: "(l \<leadsto> l') \<longleftrightarrow> (l \<le> l')"
unfolding FP_def by simp

text \<open>In order to show that the Bell/LaPadula monitor satisfies noninterference
wrt. this policy, we proceed by using the unwinding theorem.\<close>

text \<open>We choose an unwinding relation for each security level so that all states that
coincide on the values of objects with that level or below are considered equivalent.\<close>

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
    by (cases a) (auto simp add: view_def)
qed

lemma lr: "locally_respects_FP"
unfolding locally_respects_FP_def
proof (intro allI impI)
  fix s l a
  assume "(local.dom a, l) \<notin> FP"
  then show "s \<sim>\<^bsub>l\<^esub> (step s a)"
    by (cases a) (auto simp add: view_def)
qed

lemma sc: "step_consistent"
unfolding step_consistent_def
proof (intro allI impI, elim conjE)
  fix s t l a
  assume "(dom a) \<leadsto> l"
         "s \<sim>\<^bsub>l\<^esub> t"
  then show "(step s a) \<sim>\<^bsub>l\<^esub> (step t a)"
    by (cases a) (auto simp add: view_def)
qed

theorem "NI_secure"
using oc lr sc
by (intro unwinding_theorem)

end

end
