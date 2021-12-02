subsection \<open> Liberation \<close>

theory utp_liberate
  imports utp_unrest utp_rel
begin

definition liberate_pred :: "'s set \<Rightarrow> 's scene \<Rightarrow> 's set" where
"liberate_pred P x = {s. \<exists> s'. (s \<oplus>\<^sub>S s' on x) \<in> P}"

adhoc_overloading liberate liberate_pred

lemma liberate_expr_pred: "\<lbrakk>P\<rbrakk>\<^sub>P \\ x = \<lbrakk>P \\ x\<rbrakk>\<^sub>P"
  by (rel_auto add: liberate_pred_def)

lemma liberate_pred_unrest: "x \<sharp> (P::'a set) \<Longrightarrow> P \\ x = P"
  by (simp add: liberate_expr_pred unrest_liberate_iff unrest_pred_def utp_pred.pred_eq_iff)
  
end