subsection {* Example: A Ticket Automaton *}

text \<open>As another example, we consider an automaton modeling a ticket vending system, where
users can buy normal tickets or VIP tickets.

We will prove a noninterference property: buyers of normal tickets learn nothing about
the actions of VIP buyers.\<close>

theory Ticket_Automaton
imports Reference_Monitor "~~/src/HOL/Library/Code_Target_Nat"
begin

text \<open>The state stores the number of remaining normal and VIP tickets, respectively, in two
variables.\<close>

record state =
  NTickets :: nat
  VTickets :: nat

text \<open>There are actions for initializing the system with a given number of normal or VIP tickets,
buying tickets, and querying the number of remaining tickets.\<close>

datatype act =
  NInit nat
| VInit nat
| NQuery
| VQuery
| NBuy
| VBuy

datatype "output" =
  OK
| Err
| Out_NTickets nat
| Out_NVTickets "(nat \<times> nat)"

datatype var =
  Var_NTickets
| Var_VTickets

text \<open>The automaton starts without any tickets. The initialization actions supply the system with
a given number of tickets of the respective category. Customers can query the remaining number of
tickets (where prospective VIP customers can query both the remaining numbers of normal and VIP
tickets.) Buying is possible as long as there are still remaining tickets. If a category of
tickets is sold out, it can be refilled with the corresponding initialization action.\<close>

definition "s0 = \<lparr>NTickets = 0, VTickets = 0\<rparr>"

fun step :: "state \<Rightarrow> act \<Rightarrow> state" where
  "step s (NInit i) = (if NTickets s = 0 then s\<lparr>NTickets := i\<rparr> else s)"
| "step s (VInit j) = (if VTickets s = 0 then s\<lparr>VTickets := j\<rparr> else s)"
| "step s (NQuery) = s"
| "step s (VQuery) = s"
| "step s (NBuy) = (if NTickets s = 0 then s else s\<lparr>NTickets := NTickets s - 1\<rparr>)"
| "step s (VBuy) = (if VTickets s = 0 then s else s\<lparr>VTickets := VTickets s - 1\<rparr>)"

fun out :: "state \<Rightarrow> act \<Rightarrow> output" where
  "out s (NInit i) = (if NTickets s = 0 then OK else Err)"
| "out s (VInit j) = (if VTickets s = 0 then OK else Err)"
| "out s (NQuery) = Out_NTickets (NTickets s)"
| "out s (VQuery) = Out_NVTickets (NTickets s, VTickets s)"
| "out s (NBuy) = (if NTickets s = 0 then Err else OK)"
| "out s (VBuy) = (if VTickets s = 0 then Err else OK)"

text \<open>This is an instance of automata with structured states.\<close>

fun contents :: "state \<Rightarrow> var \<Rightarrow> nat" where
  "contents s Var_NTickets = NTickets s"
| "contents s Var_VTickets = VTickets s"

global_interpretation Structured_State s0 step out contents defines ex_run = run .

value "out (run s0 [NBuy, NInit 10000, NBuy, VInit 100, NBuy, NInit 50, VBuy, NBuy]) VQuery"
 -- \<open>outputs \<open>Out_NVTickets (9997, 99)\<close>\<close>

text \<open>We now consider two security domains: Normal ticket buyers, and VIP ticket buyers.\<close>

datatype domain =
  N
| V

text \<open>We allow information to flow from normal to VIP users, but not the other way around.\<close>

definition [simp]: "FP = {(N, N), (N, V), (V, V)}"

lemma [simp]: "\<And>d :: domain. d \<noteq> N \<longleftrightarrow> d = V"
  and [simp]: "\<And>d :: domain. d \<noteq> V \<longleftrightarrow> d = N"
using domain.exhaust by blast+
hide_const dom

fun dom :: "act \<Rightarrow> domain" where
  "dom (NInit i) = N"
| "dom (VInit j) = V"
| "dom (NQuery) = N"
| "dom (VQuery) = V"
| "dom (NBuy) = N"
| "dom (VBuy) = V"

global_interpretation NI s0 step out FP dom defines ex_purge = purge
proof
  show "refl FP" and "trans FP" by (auto simp add: refl_on_def trans_def)
qed

text \<open>The noninterference policy requires that the output of \<open>N\<close> actions must not depend on any
\<open>V\<close> actions that have happened before. In the following example, this is the case: Purging the
\<open>V\<close> actions does not change the output of \<open>NQuery\<close>.\<close>

value "out (run s0 [NBuy, NInit 10000, NBuy, VInit 100, NBuy, NInit 50, VBuy, NBuy]) NQuery"
 -- \<open>outputs \<open>Out_NTickets 9997\<close>\<close>
value "out (run s0 (purge [NBuy, NInit 10000, NBuy, VInit 100, NBuy, NInit 50, VBuy, NBuy] N)) NQuery"
 -- \<open>outputs \<open>Out_NTickets 9997\<close>\<close>

text \<open>We prove that noninterference holds generally for this system by proving the reference
monitor assumptions.

We implement the policy by restricting which variables may be read and written by the two
domains.\<close>

fun observe :: "domain \<Rightarrow> var set" where
  "observe N = {Var_NTickets}"
| "observe V = {Var_NTickets, Var_VTickets}"

fun alter :: "domain \<Rightarrow> var set" where
  "alter N = {Var_NTickets}"
| "alter V = {Var_VTickets}"

text \<open>This essentially specifies access control requirements, which are sufficient to implement
the information flow policy.\<close>

global_interpretation FP_Implementation s0 step out contents FP dom observe alter
proof
  fix u v
  assume "(u, v) \<in> FP"
  then show "observe u \<subseteq> observe v" by auto
next
  fix n u v
  assume "n \<in> alter u" and "n \<in> observe v"
  then show "(u, v) \<in> FP" by auto
qed

text \<open>We now have to verify that the automaton correctly implements the access control
requirements.\<close>

notation view'' ("_ \<sim>\<^bsub>_\<^esub> _")

text \<open>The visibility of variables, as specified by \<open>observe\<close>, induces state equivalence relations
for each domain. For our concrete system, we can simplify the general definition of these relations
as follows.\<close>

lemma [simp]:
 "(s \<sim>\<^bsub>N\<^esub> t) \<longleftrightarrow> NTickets s = NTickets t"
 "(s \<sim>\<^bsub>V\<^esub> t) \<longleftrightarrow> s = t"
unfolding view_def by auto

text \<open>It turns out that, using these characterizations of the equivalence relations, the built-in
reasoner in Isabelle can prove the reference monitor assumptions automatically (after case
distinction wrt.\ actions and variables.)\<close>

global_interpretation Reference_Monitor s0 step out contents FP dom observe alter
proof (unfold_locales, goal_cases)
  case (1 s t a) then show ?case by (cases a) auto next
  case (2 s t a n) then show ?case by (cases a; cases n) auto next
  case (3 s a n) then show ?case by (cases a; cases n) (auto split: if_splits)
qed

text \<open>Hence, the system is secure wrt.\ the noninterference policy.\<close>

theorem "NI_secure"
using monitor_secure .

end
