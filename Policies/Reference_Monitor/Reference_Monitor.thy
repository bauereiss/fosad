theory Reference_Monitor
imports "../Noninterference/Noninterference"
begin

locale Structured_State =
  Automaton s0 step out
  for s0 :: "'state"
  and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'state"
  and out :: "'state \<Rightarrow> 'act \<Rightarrow> 'out"
+
  fixes contents :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
    and observe :: "'dom \<Rightarrow> 'var set"
    and alter :: "'dom \<Rightarrow> 'var set"
begin

definition view :: "'dom \<Rightarrow> 'state rel" where
  "view u \<equiv> {(s, t). \<forall>n \<in> observe u. contents s n = contents t n}"

abbreviation view'' :: "'state \<Rightarrow> 'dom \<Rightarrow> 'state \<Rightarrow> bool" ("_ \<sim>\<^bsub>_\<^esub> _")
where "(s \<sim>\<^bsub>u\<^esub> t) \<equiv> (s, t) \<in> view u"

lemma viewI:
  assumes "\<And>n. n \<in> observe u \<Longrightarrow> contents s n = contents t n"
  shows "s \<sim>\<^bsub>u\<^esub> t"
using assms unfolding view_def by auto

end

locale Reference_Monitor =
  Structured_State s0 step out contents observe alter
+ NI s0 step out FP dom
  for s0 :: "'state"
  and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'state"
  and out :: "'state \<Rightarrow> 'act \<Rightarrow> 'out"
  and contents :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and observe :: "'dom \<Rightarrow> 'var set"
  and alter :: "'dom \<Rightarrow> 'var set"
  and FP :: "'dom rel"
  and dom :: "'act \<Rightarrow> 'dom"
+ assumes RMA1: "(s \<sim>\<^bsub>dom a\<^esub> t) \<Longrightarrow> out s a = out t a"
      and RMA2: "(s \<sim>\<^bsub>dom a\<^esub> t)
                 \<Longrightarrow> (contents (step s a) n \<noteq> contents s n)
                   \<or> (contents (step t a) n \<noteq> contents t n)
                 \<Longrightarrow> contents (step s a) n = contents (step t a) n"
      and RMA3: "contents (step s a) n \<noteq> contents s n \<Longrightarrow> n \<in> alter (dom a)"
      and RMA4: "(u \<leadsto> v) \<Longrightarrow> observe u \<subseteq> observe v"
      and RMA5: "n \<in> alter u \<Longrightarrow> n \<in> observe v \<Longrightarrow> (u \<leadsto> v)"
begin

lemma view_spec:
  assumes "u \<leadsto> v"
      and "s \<sim>\<^bsub>v\<^esub> t"
  shows "s \<sim>\<^bsub>u\<^esub> t"
using assms RMA4
unfolding view_def
by auto

sublocale View_Partitioning s0 step out FP dom view
proof
  show "\<forall>u. equiv UNIV (view u)"
    unfolding view_def
    by (auto intro!: equivI symI refl_onI transI)
qed

theorem monitor_secure: "NI_secure"
proof (intro unwinding_theorem)
  show "output_consistent"
    using RMA1
    unfolding output_consistent_def
    by auto
next
  show "step_consistent"
    unfolding step_consistent_def
  proof (intro allI impI, elim conjE)
    fix s t u a
    assume "(dom a) \<leadsto> u"
       and "s \<sim>\<^bsub>u\<^esub> t"
    then have "s \<sim>\<^bsub>dom a\<^esub> t" by (rule view_spec)
    show "(step s a) \<sim>\<^bsub>u\<^esub> (step t a)"
    proof (intro viewI)
      fix n
      assume n: "n \<in> observe u"
      show "contents (step s a) n = contents (step t a) n"
      proof (cases "contents (step s a) n = contents s n
                  \<and> contents (step t a) n = contents t n")
        case True
          then show ?thesis using `s \<sim>\<^bsub>u\<^esub> t` n unfolding view_def by auto
      next
        case False
          then show ?thesis using `s \<sim>\<^bsub>dom a\<^esub> t` RMA2 by auto
      qed
    qed
  qed
next
  show "locally_respects_FP"
    unfolding locally_respects_FP_def
  proof (intro allI impI)
    fix s u a
    assume "(dom a, u) \<notin> FP"
    show "s \<sim>\<^bsub>u\<^esub> (step s a)"
    proof (rule ccontr)    -- \<open>Proof by contradiction!\<close>
      assume "\<not> (s \<sim>\<^bsub>u\<^esub> (step s a))"
      then obtain n where n: "n \<in> observe u"
                      and "contents (step s a) n \<noteq> contents s n"
        unfolding view_def
        by auto
      with RMA3 RMA5 have "(dom a) \<leadsto> u"
        by blast
      with `(dom a, u) \<notin> FP` show "False" by simp
    qed
  qed
qed

end

end
