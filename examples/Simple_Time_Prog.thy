section \<open> Simple Time Programs \<close>

theory Simple_Time_Prog
  imports Simple_Time_Theory
begin

text \<open> A timed program type is created, corresponding to the healthy timed relations. \<close>

typedef 's tprog = "{P :: 's time_rel. P is HT}"
  using Delay_HT by blast

setup_lifting type_definition_tprog

text \<open> We can also show the other operators can be lifted to operate over the new type. \<close>

lift_definition Delay :: "nat \<Rightarrow> 's tprog" is "Simple_Time_Theory.Delay" by (simp add: Delay_HT)

lift_definition assigns_tprog :: "'s subst \<Rightarrow> 's tprog" is "assigns_trel" by (simp add: assigns_HT)

lift_definition seq_tprog :: "'s tprog \<Rightarrow> 's tprog \<Rightarrow> 's tprog" is "(;;)" by (simp add: HT_seq)

end