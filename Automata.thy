section {* Basic automata *}

theory Automata
imports Main
begin

locale Automaton =
  fixes s0 :: "'state"
    and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'state"
    and out :: "'state \<Rightarrow> 'act \<Rightarrow> 'out"
begin

primrec run :: "'state \<Rightarrow> 'act list \<Rightarrow> 'state" where
  "run s [] = s"
| "run s (a # \<alpha>) = run (step s a) \<alpha>"

end

end

