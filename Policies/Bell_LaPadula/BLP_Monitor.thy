section {* A Reference Monitor for Bell/LaPadula *}

theory BLP_Monitor
imports "../Noninterference/Automata"
begin

subsection {* Defining the Monitor *}

datatype perm = Read | Write

datatype ('subj, 'obj, 'val) act = R 'subj 'obj | W 'subj 'obj 'val

datatype 'val out = Value 'val | Ok | Err

type_synonym ('obj, 'val) state = "('obj \<Rightarrow> 'val)"

locale BLP_Monitor =
  fixes sc :: "'subj \<Rightarrow> ('level :: lattice)"   -- \<open>subject clearance\<close>
    and oc :: "'obj \<Rightarrow> 'level"                 -- \<open>object classification\<close>
    and M :: "'subj \<Rightarrow> 'obj \<Rightarrow> perm set"       -- \<open>permission matrix\<close>
    and init :: "('obj, 'val) state"           -- \<open>initial state (assigning values to objects)\<close>
  assumes read_secure: "Read \<in> M s obj \<Longrightarrow> oc obj \<le> sc s"
      and write_secure: "Write \<in> M s obj \<Longrightarrow> sc s \<le> oc obj"
begin

primrec step :: "('obj, 'val) state
              \<Rightarrow> ('subj, 'obj, 'val) act
              \<Rightarrow> ('obj, 'val) state"
where
  "step s (R subj obj) = s"
| "step s (W subj obj val) = (if Write \<in> M subj obj
                              then s(obj := val)
                              else s)"

primrec out :: "('obj, 'val) state
             \<Rightarrow> ('subj, 'obj, 'val) act
             \<Rightarrow> ('val) out"
where
  "out s (R subj obj) = (if Read \<in> M subj obj
                         then Value (s obj)
                         else Err)"
| "out s (W subj obj val) = (if Write \<in> M subj obj
                             then Ok
                             else Err)"

text \<open>The initial state and the step and output functions above define
an automaton: a Bell/LaPadula reference monitor.\<close>

sublocale Automaton init step out .

end

end
