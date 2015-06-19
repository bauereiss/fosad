subsubsection {* Monitor *}

theory Simple_RM
imports Reference_Monitor Simple_Lang
begin

locale Simple_RM =
  fixes s0 :: "'var state"
    and observe :: "'dom \<Rightarrow> 'var set"
    and alter :: "'dom \<Rightarrow> 'var set"
    and FP :: "'dom rel"
  assumes refl_FP: "refl FP"
      and trans_FP: "trans FP"
      and FP_observe: "(u, v) \<in> FP \<Longrightarrow> observe u \<subseteq> observe v"
      and alter_observe_FP: "n \<in> alter u \<Longrightarrow> n \<in> observe v \<Longrightarrow> (u, v) \<in> FP"
begin

primrec check :: "('var, 'dom) cmd \<Rightarrow> bool" where
  "check (v :=\<^bsub>d\<^esub> e) = (v \<in> alter d \<and> FV e \<subseteq> observe d)"

primrec step :: "'var state \<Rightarrow> ('var, 'dom) cmd \<Rightarrow> 'var state" where
  "step s (v :=\<^bsub>d\<^esub> e) = (if check (v :=\<^bsub>d\<^esub> e)
                         then execute s (v :=\<^bsub>d\<^esub> e)
                         else s)"

primrec out :: "'var state \<Rightarrow> ('var, 'dom) cmd \<Rightarrow> integer" where
  "out s (v :=\<^bsub>d\<^esub> e) = (if check (v :=\<^bsub>d\<^esub> e)
                        then eval s e
                        else 0)"

definition contents :: "'var state \<Rightarrow> 'var \<Rightarrow> integer" where
 [simp]: "contents s v = s v"

sublocale Automaton s0 step out .

sublocale Structured_State s0 step out contents observe alter .

notation view'' ("_ \<sim>\<^bsub>_\<^esub> _")

sublocale NI s0 step out FP dom
using refl_FP trans_FP 
by (unfold_locales)

lemma view_coincidence:
  assumes "s \<sim>\<^bsub>d\<^esub> t"
      and "check (v :=\<^bsub>d\<^esub> e)"
  shows "eval s e = eval t e"
proof (intro coincidence)
  from assms(2) have "FV e \<subseteq> observe d" by auto
  with assms(1) show "\<forall>v \<in> FV e. s v = t v" unfolding view_def by auto
qed

sublocale Reference_Monitor s0 step out contents observe alter FP dom
proof
  fix s t fix a :: "('var, 'dom) cmd"
  obtain v d e where [simp]: "a = (v :=\<^bsub>d\<^esub> e)" by (cases a)
  assume "s \<sim>\<^bsub>dom a\<^esub> t"
  then show "out s a = out t a"
  proof (cases "check a")
    case True
      then have "eval s e = eval t e" using `s \<sim>\<^bsub>dom a\<^esub> t` by (intro view_coincidence) auto
      then show "out s a = out t a" using True by auto
  next
    case False
      then have "out s a = 0" and "out t a = 0" by auto
      then show "out s a = out t a" by auto
  qed
next
  fix s t n fix a :: "('var, 'dom) cmd"
  obtain v d e where [simp]: "a = (v :=\<^bsub>d\<^esub> e)" by (cases a)
  assume "s \<sim>\<^bsub>dom a\<^esub> t"
     and "contents (step s a) n \<noteq> contents s n \<or> contents (step t a) n \<noteq> contents t n"
  then have "check a"
        and "contents (step s a) n = eval s e"
        and "contents (step t a) n = eval t e"
    by (auto split: split_if_asm)
  then show "contents (step s a) n = contents (step t a) n"
    using `s \<sim>\<^bsub>dom a\<^esub> t`
    by (auto intro: view_coincidence)
next
  fix s n fix a :: "('var, 'dom) cmd"
  obtain v d e where [simp]: "a = (v :=\<^bsub>d\<^esub> e)" by (cases a)
  assume "contents (step s a) n \<noteq> contents s n"
  then have "check a" and "v = n" by (auto split: split_if_asm)
  then show "n \<in> alter (dom a)" by simp
next
  fix u v
  assume "u \<leadsto> v"
  then show "observe u \<subseteq> observe v" using FP_observe by blast
next
  fix n u v
  assume "n \<in> alter u" and "n \<in> observe v"
  then show "u \<leadsto> v" using alter_observe_FP by blast
qed

thm monitor_secure

end

end
