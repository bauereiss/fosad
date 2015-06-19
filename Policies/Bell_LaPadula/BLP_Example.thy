theory BLP_Example
imports BLP_RM
begin

datatype subj = Maps | Chat | SysL | SysH

datatype obj = Contacts | Internet | GPS | Files

datatype level = Lo | Hi

primrec sc :: "subj \<Rightarrow> level" where
  "sc Maps = Hi"
| "sc Chat = Lo"
| "sc SysL = Lo"
| "sc SysH = Hi"

primrec oc :: "obj \<Rightarrow> level" where
  "oc Contacts = Lo"
| "oc Internet = Lo"
| "oc GPS = Hi"
| "oc Files = Lo"

fun M :: "subj \<Rightarrow> obj \<Rightarrow> perm set" where
  "M Chat Contacts = {Read, Write}"
| "M Chat Internet = {Read, Write}"
| "M Chat GPS = {}"
| "M Chat Files = {Read, Write}"
| "M Maps GPS = {Read}"
| "M Maps Files = {Read}"
| "M Maps _ = {}"
| "M SysL GPS = {}"
| "M SysL _ = {Read, Write}"
| "M SysH GPS = {Read, Write}"
| "M SysH _ = {Read}"

definition init :: "obj \<Rightarrow> nat" where "init obj = 0"

lemma [simp]: "\<And> l. l \<noteq> Hi \<longleftrightarrow> l = Lo" and 
      [simp]: "\<And> l. Hi \<noteq> l \<longleftrightarrow> Lo = l" and 
      [simp]: "\<And> l. l \<noteq> Lo \<longleftrightarrow> l = Hi" and 
      [simp]: "\<And> l. Lo \<noteq> l \<longleftrightarrow> Hi = l"
by (metis level.exhaust level.simps(2))+

lemma [dest]: "\<And> l A. \<lbrakk>l \<in> A; Lo \<notin> A\<rbrakk> \<Longrightarrow> l = Hi" and 
      [dest]: "\<And> l A. \<lbrakk>l \<in> A; Hi \<notin> A\<rbrakk> \<Longrightarrow> l = Lo"
by (metis level.exhaust)+

declare level.split[split]

instantiation level :: complete_lattice
begin
  definition top_level: "top \<equiv> Hi"
  definition bot_level: "bot \<equiv> Lo"
  definition inf_level: "inf l1 l2 \<equiv> if Lo \<in> {l1,l2} then Lo else Hi"
  definition sup_level: "sup l1 l2 \<equiv> if Hi \<in> {l1,l2} then Hi else Lo"
  definition less_eq_level: "less_eq l1 l2 \<equiv> (l1 = Lo \<or> l2 = Hi)"
  definition less_level: "less l1 l2 \<equiv> l1 = Lo \<and> l2 = Hi"
  definition Inf_level: "Inf L \<equiv> if Lo \<in> L then Lo else Hi"
  definition Sup_level: "Sup L \<equiv> if Hi \<in> L then Hi else Lo"
instance
  proof qed (auto simp: top_level bot_level inf_level sup_level
                        less_eq_level less_level Inf_level Sup_level)
end

lemma [simp]: "Lo \<le> Hi" using less_eq_level by auto

interpretation BLP_Monitor sc oc M init
proof
  fix subj obj
  assume "Read \<in> M subj obj"
  then show "oc obj \<le> sc subj"
    by (cases subj; cases obj; simp)
next
  fix subj obj
  assume "Write \<in> M subj obj"
  then show "sc subj \<le> oc obj"
    by (cases subj; cases obj; simp)
qed

lemma "FP = {(Lo, Lo), (Lo, Hi), (Hi, Hi)}"
unfolding FP_def
by (auto simp add: less_eq_level)

thm dom.simps
thm monitor_secure

end
