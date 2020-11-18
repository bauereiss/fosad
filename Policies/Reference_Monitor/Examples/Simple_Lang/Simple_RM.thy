subsubsection \<open>Monitor\<close>

theory Simple_RM
imports "../../Reference_Monitor" Simple_Lang
begin

text \<open>We now define the implementation of a reference monitor for our simple programming language
(and a given flow policy).\<close>

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

text \<open>The @{text check} function returns true for an assignment @{text "v :=\<^bsub>d\<^esub> e"} if @{text v}
is writable by @{text d} and the variables in @{text e} are readable for @{text d}.\<close>

fun check :: "('var, 'dom) cmd \<Rightarrow> bool" where
  "check (v :=\<^bsub>d\<^esub> e) = (v \<in> alter d \<and> Vars e \<subseteq> observe d)"

text \<open>If the check is successful, the state is updated and the evaluation of the expressions is
given as output; otherwise, the state remains unchanged, and 0 is given as output.\<close>

fun step :: "'var state \<Rightarrow> ('var, 'dom) cmd \<Rightarrow> 'var state" where
  "step s (v :=\<^bsub>d\<^esub> e) = (if check (v :=\<^bsub>d\<^esub> e)
                         then execute s (v :=\<^bsub>d\<^esub> e)
                         else s)"

fun out :: "'var state \<Rightarrow> ('var, 'dom) cmd \<Rightarrow> integer" where
  "out s (v :=\<^bsub>d\<^esub> e) = (if check (v :=\<^bsub>d\<^esub> e)
                        then \<E> e s
                        else 0)"

definition contents :: "'var state \<Rightarrow> 'var \<Rightarrow> integer" where
 [simp]: "contents s v = s v"

sublocale Automaton s0 step out .

text \<open>We currently assume that the consistency conditions for the implementation of the flow policy
hold (we will have to prove this later for concrete instantiations).\<close>

sublocale FP_Implementation s0 step out contents FP dom observe alter
using refl_FP trans_FP FP_observe alter_observe_FP
by unfold_locales

notation view'' ("_ \<sim>\<^bsub>_\<^esub> _")

text \<open>We can, however, already prove generally that the reference monitor assumptions hold.

As a helper lemma, we prove that expressions used in assignments allowed for
@{text d} are evaluated to the same value in states equivalent for @{text d}.\<close>

lemma view_coincidence:
  assumes "s \<sim>\<^bsub>d\<^esub> t"
      and "check (v :=\<^bsub>d\<^esub> e)"
  shows "\<E> e s = \<E> e t"
proof (intro coincidence)
  from assms(2) have "Vars e \<subseteq> observe d" by auto
  with assms(1) show "\<forall>v \<in> Vars e. s v = t v" unfolding view_def by auto
qed

text \<open>We then prove the three reference monitor assumptions.\<close>

sublocale Reference_Monitor s0 step out contents FP dom observe alter
proof
  \<comment> \<open>RMA1\<close>
  fix s t fix a :: "('var, 'dom) cmd"
  obtain v d e where [simp]: "a = (v :=\<^bsub>d\<^esub> e)" by (cases a)
  assume "s \<sim>\<^bsub>dom a\<^esub> t"
  then show "out s a = out t a"
  proof (cases "check a")
    case True
      then have "\<E> e s = \<E> e t" using `s \<sim>\<^bsub>dom a\<^esub> t`
        by (intro view_coincidence) auto
      then show "out s a = out t a" using True by auto
  next
    case False
      then have "out s a = 0" and "out t a = 0" by auto
      then show "out s a = out t a" by auto
  qed
next
  \<comment> \<open>RMA2\<close>
  fix s t n fix a :: "('var, 'dom) cmd"
  obtain v d e where [simp]: "a = (v :=\<^bsub>d\<^esub> e)" by (cases a)
  assume "s \<sim>\<^bsub>dom a\<^esub> t"
     and "contents (step s a) n \<noteq> contents s n \<or>
          contents (step t a) n \<noteq> contents t n"
  then have "check a"
        and "contents (step s a) n = \<E> e s"
        and "contents (step t a) n = \<E> e t"
    by (auto split: if_splits)
  then show "contents (step s a) n = contents (step t a) n"
    using `s \<sim>\<^bsub>dom a\<^esub> t`
    by (auto intro: view_coincidence)
next
  \<comment> \<open>RMA3\<close>
  fix s n fix a :: "('var, 'dom) cmd"
  obtain v d e where [simp]: "a = (v :=\<^bsub>d\<^esub> e)" by (cases a)
  assume "contents (step s a) n \<noteq> contents s n"
  then have "check a" and "v = n" by (auto split: if_splits)
  then show "n \<in> alter (dom a)" by simp
qed

end

end
