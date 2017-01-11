theory Lang_NI
imports Main
begin

locale Lang_NI =
  fixes lang_semantics :: "'state \<Rightarrow> 'prog \<Rightarrow> 'state \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow> _")
    and view :: "'state \<Rightarrow> 'state \<Rightarrow> bool" ("_ \<sim> _")
begin

text \<open>Termination-Sensitive Non-Interference (TSNI):\<close>

definition "TSNI c \<equiv>
  \<forall> \<mu>1 \<mu>2 \<mu>1'. ((\<mu>1 \<sim> \<mu>2) \<and> (\<mu>1 \<turnstile> c \<Rightarrow> \<mu>1'))
             \<longrightarrow> (\<exists> \<mu>2'. (\<mu>2 \<turnstile> c \<Rightarrow> \<mu>2') \<and> (\<mu>1' \<sim> \<mu>2'))"

text \<open>Termination-Insensitive Non-Interference (TINI):\<close>

definition "TINI c \<equiv>
  \<forall> \<mu>1 \<mu>2 \<mu>1' \<mu>2'. ((\<mu>1 \<sim> \<mu>2) \<and> (\<mu>1 \<turnstile> c \<Rightarrow> \<mu>1') \<and> (\<mu>2 \<turnstile> c \<Rightarrow> \<mu>2'))
             \<longrightarrow> (\<mu>1' \<sim> \<mu>2')"

text \<open>Deterministic programs:\<close>

definition "det c \<equiv>
  \<forall> \<mu> \<mu>' \<mu>''. (\<mu> \<turnstile> c \<Rightarrow> \<mu>') \<and> (\<mu> \<turnstile> c \<Rightarrow> \<mu>'') \<longrightarrow> \<mu>' = \<mu>''"

text \<open>Termination of a program, starting from \<mu>:\<close>

definition "term c \<mu> \<equiv>
  \<exists>\<mu>'. (\<mu> \<turnstile> c \<Rightarrow> \<mu>')"

text \<open>For deterministic programs that are guaranteed to terminate, these two notions of
noninterference coincide.

Note that the proofs of the following lemmas are automatic; we spell them out merely for
illustration purposes.\<close>

lemma TSNI_TINI:
  assumes "TSNI c"
      and "det c"
  shows "TINI c"
unfolding TINI_def
proof (intro allI impI, elim conjE)
  fix \<mu>1 \<mu>2 \<mu>1' \<mu>2'
  assume "\<mu>1 \<sim> \<mu>2" and "\<mu>1 \<turnstile> c \<Rightarrow> \<mu>1'" and \<mu>2': "\<mu>2 \<turnstile> c \<Rightarrow> \<mu>2'"
  with `TSNI c` obtain \<mu>2'' where "\<mu>1' \<sim> \<mu>2''" and \<mu>2'': "\<mu>2 \<turnstile> c \<Rightarrow> \<mu>2''"
    unfolding TSNI_def by blast
  moreover have "\<mu>2' = \<mu>2''" using `det c` \<mu>2' \<mu>2''
    unfolding det_def by blast
  ultimately show "\<mu>1' \<sim> \<mu>2'" by simp
qed

lemma TINI_TSNI:
  assumes "TINI c"
      and "\<forall> \<mu>. term c \<mu>"
  shows "TSNI c"
unfolding TSNI_def
proof (intro allI impI, elim conjE)
  fix \<mu>1 \<mu>2 \<mu>1'
  assume "\<mu>1 \<sim> \<mu>2" and "\<mu>1 \<turnstile> c \<Rightarrow> \<mu>1'"
  moreover obtain \<mu>2' where \<mu>2': "\<mu>2 \<turnstile> c \<Rightarrow> \<mu>2'"
    using assms(2) unfolding term_def by blast
  ultimately have "\<mu>1' \<sim> \<mu>2'"
    using `TINI c` unfolding TINI_def by blast
  with \<mu>2' show "\<exists>\<mu>2'. (\<mu>2 \<turnstile> c \<Rightarrow> \<mu>2') \<and> (\<mu>1' \<sim> \<mu>2')" by blast
qed

theorem
assumes "det c" and "\<forall>\<mu>. term c \<mu>"
shows "TSNI c \<longleftrightarrow> TINI c"
using assms TSNI_TINI TINI_TSNI by blast

end

end
