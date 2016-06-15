section {* Noninterference *}

theory Noninterference
imports Automata
begin

text \<open>We now consider security of such automata in the sense of Goguen and Meseguer's notion
of @{emph \<open>noninterference\<close>}.\<close>

subsection {* Definition *}

text \<open>For a given automaton, we add a function @{text dom}, which assigns a security domain to each
action, and a flow policy, which is a reflexive and transitive relation between domains, specifying
which flows of information are allowed.\<close>

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

text \<open>We write @{text "D \<leadsto> D'"} if the flow policy allows a flow from @{text D} to @{text D'}.\<close>

abbreviation flow :: "'dom \<Rightarrow> 'dom \<Rightarrow> bool" ("_ \<leadsto> _")
where "(D \<leadsto> D') \<equiv> (D, D') \<in> FP"

text \<open>We define the @{text purge} function, which removes all actions from a trace @{text \<alpha>} that
belong to a domain from which no flow is allowed to a given domain @{text D}. In other words,
we remove actions that should be secret for @{text D}.\<close>

fun purge :: "'act list \<Rightarrow> 'dom \<Rightarrow> 'act list" where
  "purge [] D = []"
| "purge (a # \<alpha>) D = (if (dom a) \<leadsto> D
                      then a # purge \<alpha> D
                      else purge \<alpha> D)"

text \<open>An automaton is considered secure wrt.\ a noninterference policy if the output of an action
@{text a} is independent of the execution of secret actions: Purging secret actions from the trace
that has been executed before does not change the output of @{text a}.\<close>

definition "NI_secure
\<equiv> \<forall>a \<alpha>. out (run s0 \<alpha>) a = out (run s0 (purge \<alpha> (dom a))) a"

text \<open>This is the @{emph \<open>definition\<close>} of (noninterference) security for automata.
In the following sections, we focus on techniques for the @{emph \<open>verification\<close>} of security.\<close>

end

subsection {* Verification *}

text \<open>In order to use the unwinding verification technique, we first have to choose a
@{emph \<open>view partitioning\<close>}, i.e.\ a family of equivalence relations on states, indexed by domain.
Hence, we have to choose an equivalence relation for each domain. When choosing these relations,
the intuition is to consider states as equivalent for a domain if they are supposed to be
indistinguishable for that domain.\<close>

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

text \<open>We write @{text "s \<sim>\<^bsub>u\<^esub> t"} if the states @{text s} and @{text t} are equivalent for the
domain @{text u} in our view partitioning.\<close>

abbreviation view' :: "'state \<Rightarrow> 'dom \<Rightarrow> 'state \<Rightarrow> bool" ("_ \<sim>\<^bsub>_\<^esub> _")
where "(s \<sim>\<^bsub>u\<^esub> t) \<equiv> (s, t) \<in> view u"

text \<open>Equivalence relations are reflexive, symmetric and transitive.\<close>

lemma view_refl: "s \<sim>\<^bsub>u\<^esub> s"
  and view_sym: "(s \<sim>\<^bsub>u\<^esub> s') \<Longrightarrow> (s' \<sim>\<^bsub>u\<^esub> s)"
  and view_trans: "(s \<sim>\<^bsub>u\<^esub> s') \<Longrightarrow> (s' \<sim>\<^bsub>u\<^esub> t) \<Longrightarrow> (s \<sim>\<^bsub>u\<^esub> t)"
using view_equiv
unfolding equiv_def refl_on_def sym_def trans_def
by blast+

text \<open>The unwinding theorem states that an automaton is secure wrt.\ a noninterference policy
if the following three properties are satisfied for the given view partitioning.\<close>

text \<open>@{emph \<open>Output consistency\<close>} requires that two states give the same output for an action
@{text a}, if they are equivalent for the domain of that action. In other words, observers in
a given domain cannot distinguish equivalent states via the outputs of their actions.\<close>

definition "output_consistent
\<equiv> \<forall>a s t. (s \<sim>\<^bsub>dom a\<^esub> t) \<longrightarrow> out s a = out t a"

text \<open>@{emph \<open>Step consistency\<close>} requires that performing a visible action from two equivalent
states again results in equivalent states.\<close>

definition "step_consistent
\<equiv> \<forall>s t u a. (((dom a) \<leadsto> u) \<and> (s \<sim>\<^bsub>u\<^esub> t)) \<longrightarrow> ((step s a) \<sim>\<^bsub>u\<^esub> (step t a))"

text \<open>@{emph \<open>Local respect of @{text \<leadsto>}\<close>} requires that performing a secret action preserves the
equivalence class of the current state.\<close>

definition "locally_respects_FP
\<equiv> \<forall>s u a. \<not>((dom a) \<leadsto> u) \<longrightarrow> (s \<sim>\<^bsub>u\<^esub> (step s a))"

text \<open>In order to prove noninterference using these conditions, we use structural induction over
the list of actions @{text \<alpha>}.

The induction schema for lists looks as follows:
@{thm [display] list.induct [no_vars]}

We prove noninterference using a helper lemma: Instead of letting the lists of actions (unpurged
and purged) run from the starting state, we let them run from two equivalent, but otherwise
arbitrary states @{text s} and @{text t}, respectively. This makes the induction hypothesis more
useful. Moreover, we focus first on showing that the states after the two runs are equivalent for
an observer in the domain @{text u} (when purging for @{text u}).
\<close>

lemma unwinding_lemma:
  assumes lr: "locally_respects_FP"
      and sc: "step_consistent"
      and "s \<sim>\<^bsub>u\<^esub> t"
  shows "(run s \<alpha>) \<sim>\<^bsub>u\<^esub> (run t (purge \<alpha> u))"
using `s \<sim>\<^bsub>u\<^esub> t`
proof (induction \<alpha> arbitrary: s t)
  case Nil
    -- \<open>Base case: empty list []\<close>
    have "run s [] = s"
     and "run t (purge [] u) = t"
      by auto
    with `s \<sim>\<^bsub>u\<^esub> t` show "(run s []) \<sim>\<^bsub>u\<^esub> (run t (purge [] u))" by simp
next
  case (Cons a' \<alpha>')
    -- \<open>Inductive step:\<close>
    -- \<open>List starts with action @{text a'} and continues with list @{text \<alpha>'} (possibly empty).\<close>
    -- \<open>The following induction hypothesis about @{text \<alpha>'} is available
        (for any @{text s'} and @{text t'}):\<close>
    -- \<open>@{thm Cons.IH[of "s'" "t'"]}\<close>
    -- \<open>We proceed by a case distinction whether @{text a'} is visible for @{text u} or not.\<close>
    show "(run s (a' # \<alpha>')) \<sim>\<^bsub>u\<^esub> (run t (purge (a' # \<alpha>') u))"
    proof (cases)
      assume flow: "(dom a') \<leadsto> u"
      with `s \<sim>\<^bsub>u\<^esub> t` have "(step s a') \<sim>\<^bsub>u\<^esub> (step t a')"
        using sc              -- \<open>Step consistency\<close>
        unfolding step_consistent_def
        by auto
      then have "(run (step s a') \<alpha>') \<sim>\<^bsub>u\<^esub> (run (step t a') (purge \<alpha>' u))"
        using Cons.IH         -- \<open>Induction hypothesis!\<close>
        by simp
      then show ?case using flow by auto
    next
      assume noflow: "(dom a', u) \<notin> FP"
      then have "s \<sim>\<^bsub>u\<^esub> (step s a')"
        using lr              -- \<open>Locally respects @{text \<leadsto>}\<close>
        unfolding locally_respects_FP_def
        by auto
      with `s \<sim>\<^bsub>u\<^esub> t` have "(step s a') \<sim>\<^bsub>u\<^esub> t"
        using view_sym view_trans
        by blast
      then have "(run (step s a') \<alpha>') \<sim>\<^bsub>u\<^esub> (run t (purge \<alpha>' u))"
        using Cons.IH         -- \<open>Induction hypothesis!\<close>
        by simp
      then show ?case using noflow by auto
    qed
qed

text \<open>With this lemma, noninterference follows directly by setting @{text "s = t = s0"} and
using output consistency.\<close>

theorem unwinding_theorem:
  assumes "output_consistent"
      and "locally_respects_FP"
      and "step_consistent"
  shows "NI_secure"
using assms unwinding_lemma[where s = s0 and t = s0] view_refl[of s0]
unfolding NI_secure_def output_consistent_def
by auto

end

end
