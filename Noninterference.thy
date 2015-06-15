section {* Noninterference *}

theory Noninterference
imports Automata
begin

subsection {* Definition *}

locale NI =
  Automaton s0 step out
  for s0 :: "'state"
  and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'state"
  and out :: "'state \<Rightarrow> 'act \<Rightarrow> 'out"
+
  fixes FP :: "'dom rel"
    and dom :: "'act \<Rightarrow> 'dom"
  assumes "refl FP"
      and "trans FP"
begin

abbreviation flow :: "'dom \<Rightarrow> 'dom \<Rightarrow> bool" ("_ \<leadsto> _")
where "(D \<leadsto> D') \<equiv> (D, D') \<in> FP"

primrec purge :: "'act list \<Rightarrow> 'dom \<Rightarrow> 'act list" where
  "purge [] D = []"
| "purge (a # \<alpha>) D = (if (dom a) \<leadsto> D
                      then a # purge \<alpha> D
                      else purge \<alpha> D)"

definition "NI_secure
\<equiv> \<forall>a \<alpha>. out (run s0 \<alpha>) a = out (run s0 (purge \<alpha> (dom a))) a"

end

subsection {* Verification *}

locale View_Partitioning =
  NI s0 step out FP dom
  for s0 :: "'state"
  and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'state"
  and out :: "'state \<Rightarrow> 'act \<Rightarrow> 'out"
  and FP :: "'dom rel"
  and dom :: "'act \<Rightarrow> 'dom"
+
  fixes view :: "'dom \<Rightarrow> 'state rel"
  assumes view_equiv: "\<forall>u. equiv UNIV (view u)"
begin

abbreviation view' :: "'state \<Rightarrow> 'dom \<Rightarrow> 'state \<Rightarrow> bool" ("_ \<sim>\<^bsub>_\<^esub> _")
where "(s \<sim>\<^bsub>u\<^esub> t) \<equiv> (s, t) \<in> view u"

lemma view_refl: "s \<sim>\<^bsub>u\<^esub> s"
  and view_sym: "(s \<sim>\<^bsub>u\<^esub> s') \<Longrightarrow> (s' \<sim>\<^bsub>u\<^esub> s)"
  and view_trans: "(s \<sim>\<^bsub>u\<^esub> s') \<Longrightarrow> (s' \<sim>\<^bsub>u\<^esub> t) \<Longrightarrow> (s \<sim>\<^bsub>u\<^esub> t)"
using view_equiv
unfolding equiv_def refl_on_def sym_def trans_def
by blast+

definition "output_consistent
\<equiv> \<forall>a s t. (s \<sim>\<^bsub>dom a\<^esub> t) \<longrightarrow> out s a = out t a"

definition "step_consistent
\<equiv> \<forall>s t u a. (((dom a) \<leadsto> u) \<and> (s \<sim>\<^bsub>u\<^esub> t)) \<longrightarrow> ((step s a) \<sim>\<^bsub>u\<^esub> (step t a))"

definition "locally_respects_FP
\<equiv> \<forall>s u a. \<not>((dom a) \<leadsto> u) \<longrightarrow> (s \<sim>\<^bsub>u\<^esub> (step s a))"

text \<open>In order to prove noninterference using these conditions, we use induction (of course).
In the following, we use structural induction over the list of actions @{text \<alpha>}.

The induction schema for lists looks as follows:
@{thm [display] list.induct [no_vars]}

Also, we don't directly prove noninterference as-is, but we generalize the statement slightly:
Instead of running the lists of actions (unpurged and purged) from the starting state, we run them
from two equivalent, but otherwise arbitrary states @{text s} and @{text t}, respectively. This
makes the induction hypothesis much more useful, as we will see. Moreover, we focus first on
showing that the states after the two runs are equivalent for an @{text l}-observer (when purging
for @{text l}) --- the fact that afterwards also the outputs of @{text l}-actions are the same
then directly follows using output consistency.
\<close>

lemma unwinding_lemma:
  assumes lr: "locally_respects_FP"
      and sc: "step_consistent"
      and s_equiv_t: "s \<sim>\<^bsub>u\<^esub> t"
  shows "(run s \<alpha>) \<sim>\<^bsub>u\<^esub> (run t (purge \<alpha> u))"
    (is "?goal s t \<alpha>")
using s_equiv_t
proof (induction \<alpha> arbitrary: s t)
  case Nil
    -- \<open>Base case: empty list []\<close>
    note `s \<sim>\<^bsub>u\<^esub> t`
    moreover have "run s [] = s"
              and "run t (purge [] u) = t"
      by auto
    ultimately show "?goal s t []" by simp
next
  case (Cons a' \<alpha>')
    -- \<open>Induction step:\<close>
    -- \<open>List starts with action @{text a'} and continues with list @{text \<alpha>'} (possibly empty).\<close>
    -- \<open>The following induction hypothesis about @{text \<alpha>'} is available
        (for any @{text s'} and @{text t'}):\<close>
    -- \<open>@{thm Cons.IH[of "s'" "t'"]}\<close>
    show "?goal s t (a' # \<alpha>')"
    proof (cases "(dom a') \<leadsto> u")
      assume flow: "(dom a', u) \<in> FP"
      with `s \<sim>\<^bsub>u\<^esub> t` have "(step s a') \<sim>\<^bsub>u\<^esub> (step t a')"
        using sc              -- \<open>Step consistency\<close>
        unfolding step_consistent_def
        by auto
      then have "?goal (step s a') (step t a') \<alpha>'"
        using Cons.IH         -- \<open>Induction hypothesis!\<close>
        by simp
      then show "?goal s t (a' # \<alpha>')" using flow by auto
    next
      assume noflow: "(dom a', u) \<notin> FP"
      then have "s \<sim>\<^bsub>u\<^esub> (step s a')"
        using lr              -- \<open>Locally respects @{text \<leadsto>}\<close>
        unfolding locally_respects_FP_def
        by auto
      with `s \<sim>\<^bsub>u\<^esub> t` have "(step s a') \<sim>\<^bsub>u\<^esub> t"
        using view_sym view_trans
        by blast
      then have "?goal (step s a') t \<alpha>'"
        using Cons.IH         -- \<open>Induction hypothesis!\<close>
        by simp
      then show "?goal s t (a' # \<alpha>')" using noflow by auto
    qed
qed

text \<open>With this lemma, noninterference directly follows by setting @{text "s = t = s0"} and
using output consistency.\<close>

theorem unwinding_theorem:
  assumes "output_consistent"
      and "locally_respects_FP"
      and "step_consistent"
  shows "NI_secure"
using assms unwinding_lemma[where s = s0 and t = s0] view_refl
unfolding NI_secure_def output_consistent_def
by auto

end

end
