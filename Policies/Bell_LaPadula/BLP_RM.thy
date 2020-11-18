theory BLP_RM
imports BLP_Monitor "../Reference_Monitor/Reference_Monitor"
begin

context BLP_Monitor
begin

text \<open>We show that a Bell/LaPadula monitor satisfies the reference monitor assumptions of Rushby.
Hence, in a specific sense, a Bell/LaPadula monitor satisfies a noninterference policy.\<close>

definition contents :: "('obj, 'val) state \<Rightarrow> 'obj \<Rightarrow> 'val" where
  [simp]: "contents s obj = s obj"

definition observe :: "'level \<Rightarrow> 'obj set" where
  [simp]: "observe l = {obj. oc obj \<le> l}"

definition alter :: "'level \<Rightarrow> 'obj set" where
  [simp]: "alter l = {obj. l \<le> oc obj}"

sublocale Structured_State init step out contents .

text \<open>The lattice of security levels of a Bell/LaPadula policy can be interpreted as a flow policy
in the sense of Goguen-Meseguer: @{text "(l \<leadsto> l') \<longleftrightarrow> (l \<le> l')"}\<close>

definition FP :: "'level rel" where
  "FP = {(l, l'). l \<le> l'}"

text \<open>We now have to define the labeling of actions with security domains/levels.

In the following, we choose the labeling according to subject. The intuition is that an observer on
level @{text l} may see the actions (and outputs of those actions) of all users with a clearance of
@{text l} and below, while the observer must not learn anything about actions of users in other
security levels.\<close>

primrec dom :: "('subj, 'obj, 'val) act \<Rightarrow> 'level" where
  "dom (R subj obj) = sc subj"
| "dom (W subj obj val) = sc subj"

text \<open>We now instantiate the Reference_Monitor locale, proving the reference monitor assumptions.\<close>

text \<open>We first show that @{text observe} and @{text alter} are consistent with the flow policy
@{text FP}:\<close>

sublocale FP_Implementation init step out contents FP dom observe alter
proof
  show "refl FP" and "trans FP"
    by (auto simp add: FP_def refl_on_def trans_def)
next
  fix u v
  assume "(u, v) \<in> FP"
  then show "observe u \<subseteq> observe v"
    by (auto simp add: FP_def)
next
  fix n u v
  assume "n \<in> alter u" and "n \<in> observe v"
  then show "(u, v) \<in> FP"
    by (auto simp add: FP_def)
qed

notation view'' ("_ \<sim>\<^bsub>_\<^esub> _")

text \<open>We then show the remaining reference monitor assumptions:\<close>

sublocale Reference_Monitor init step out contents FP dom observe alter
proof
  fix s t a
  assume "s \<sim>\<^bsub>dom a\<^esub> t"
  with read_secure show "out s a = out t a"
    by (cases a) (auto simp add: view_def)
next
  fix s t a n
  assume "contents (step s a) n \<noteq> contents s n \<or> contents (step t a) n \<noteq> contents t n"
  then show "contents (step s a) n = contents (step t a) n"
    by (cases a) (auto split: if_splits)
next
  fix s a n
  assume "contents (step s a) n \<noteq> contents s n"
  with write_secure show "n \<in> alter (dom a)"
    by (cases a) (auto split: if_splits)
qed

notation flow ("_ \<leadsto> _")

lemma "(l \<leadsto> l') \<longleftrightarrow> (l \<le> l')"
by (auto simp add: FP_def)

thm dom.simps

thm monitor_secure

end

end
