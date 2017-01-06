section {* Reference Monitors *}

theory Reference_Monitor
imports "../Noninterference/Noninterference"
begin

text \<open>We now consider a special class of automata with structured state: there is a type
@{text "'var"} of variable names, and a state stores a value for each variable.\<close>

subsection {* Definition *}

text \<open>We formalize this with a function @{text contents}, which takes a state and a variable name,
and returns the value stored under that variable name in the state.\<close>

locale Structured_State =
  Automaton s0 step out
  for s0 :: "'state"
  and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'state"
  and out :: "'state \<Rightarrow> 'act \<Rightarrow> 'out"
+ fixes contents :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"

subsection {* Verification *}

text \<open>We implement a flow policy for an automaton with structured state by specifying which
variables can be read and written in a domain: @{text "observe u"} gives the set of variables that
may be read in the domain @{text u}, and @{text "alter u"} gives the set of variables that may be
written by @{text u}.

These functions have to be consistent with the flow policy in the following sense:
\<^item> if information is allowed to flow from domain @{text u} to domain @{text v}, then all variables
that may be read by @{text u} may also be read by @{text v} (condition @{text FP_impl1} below), and
\<^item> if a variable may be written by @{text u} and read by @{text v}, then information must be allowed
to flow from @{text u} to @{text v}  (condition @{text FP_impl2} below.)\<close>

locale FP_Implementation =
  Structured_State s0 step out contents
+ NI s0 step out FP dom
  for s0 :: "'state"
  and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'state"
  and out :: "'state \<Rightarrow> 'act \<Rightarrow> 'out"
  and contents :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and FP :: "'dom rel"
  and dom :: "'act \<Rightarrow> 'dom"
+
fixes observe :: "'dom \<Rightarrow> 'var set"
  and alter :: "'dom \<Rightarrow> 'var set"
assumes FP_impl1: "(u \<leadsto> v) \<Longrightarrow> observe u \<subseteq> observe v"
    and FP_impl2: "n \<in> alter u \<Longrightarrow> n \<in> observe v \<Longrightarrow> (u \<leadsto> v)"
begin

text \<open>We will prove the security of the automaton using the unwinding theorem. For this purpose,
we define a view partitioning where two states are equivalent for a domain @{text u} iff they
coincide on the variables that are observable for @{text u}.\<close>

definition view :: "'dom \<Rightarrow> 'state rel" where
  "view u \<equiv> {(s, t). \<forall>n \<in> observe u. contents s n = contents t n}"

abbreviation view'' :: "'state \<Rightarrow> 'dom \<Rightarrow> 'state \<Rightarrow> bool" ("_ \<sim>\<^bsub>_\<^esub> _")
where "(s \<sim>\<^bsub>u\<^esub> t) \<equiv> (s, t) \<in> view u"

lemma viewI:
  assumes "\<And>n. n \<in> observe u \<Longrightarrow> contents s n = contents t n"
  shows "s \<sim>\<^bsub>u\<^esub> t"
using assms unfolding view_def by auto

text \<open>This is indeed a view partitioning: for all domains @{text u}, the relation @{text "\<sim>\<^bsub>u\<^esub>"}
is an equivalence relation.\<close>

sublocale View_Partitioning s0 step out FP dom view
proof
  show "\<forall>u. equiv UNIV (view u)"
    unfolding view_def
    by (auto intro!: equivI symI refl_onI transI)
qed

text \<open>As a helper lemma for the proof below, we note that, if information is allowed to flow from
@{text u} to @{text v}, then two states are equivalent for @{text u} if they are equivalent for
@{text v}, i.e.\ @{text "\<sim>\<^bsub>v\<^esub>"} is a @{emph \<open>finer\<close>} equivalence relation than @{text "\<sim>\<^bsub>u\<^esub>"}.\<close>

lemma view_spec:
  assumes "u \<leadsto> v"
      and "s \<sim>\<^bsub>v\<^esub> t"
  shows "s \<sim>\<^bsub>u\<^esub> t"
using assms FP_impl1
unfolding view_def
by auto

end

text \<open>In order to prove the unwinding conditions, we require that the implementation of the flow
policy satisfies three additional assumptions:
\<^item> output consistency has to hold (RMA1),
\<^item> if a visible action is performed on two equivalent states and changes the value of a variable
in one of them, then it has to be changed to the same value in the other state (RMA2), and
\<^item> if an action @{text a} changes the value of a variable, then that variable must be writable by
the domain of @{text a} (RMA3).\<close>

locale Reference_Monitor = FP_Implementation
+ assumes RMA1: "(s \<sim>\<^bsub>dom a\<^esub> t) \<Longrightarrow> out s a = out t a"
      and RMA2: "(s \<sim>\<^bsub>dom a\<^esub> t)
                 \<Longrightarrow> (contents (step s a) n \<noteq> contents s n)
                   \<or> (contents (step t a) n \<noteq> contents t n)
                 \<Longrightarrow> contents (step s a) n = contents (step t a) n"
      and RMA3: "contents (step s a) n \<noteq> contents s n \<Longrightarrow> n \<in> alter (dom a)"
begin

text \<open>Together with the assumptions on the consistency of implementation and flow policy
(@{text "FP_impl1"} and @{text "FP_impl2"}), this is sufficient to prove the unwinding conditions.\<close>

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
    assume noflow: "\<not>((dom a) \<leadsto> u)"
    then have not_alter_observe: "\<forall>n. n \<notin> alter (dom a) \<or> n \<notin> observe u"
      using FP_impl2 by auto
    show "s \<sim>\<^bsub>u\<^esub> (step s a)"
    proof (intro viewI)
      fix n
      assume "n \<in> observe u"
      with not_alter_observe have "n \<notin> alter (dom a)" by auto
      with RMA3 have "contents (step s a) n = contents s n" by auto
      then show "contents s n = contents (step s a) n" ..
    qed
  qed
qed

end

end
