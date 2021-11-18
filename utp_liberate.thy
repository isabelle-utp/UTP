subsection \<open> Liberation \<close>

theory utp_liberate
  imports utp_unrest utp_rel
begin

definition liberate_pred :: "'s set \<Rightarrow> 's scene \<Rightarrow> 's set" where
"liberate_pred P x = {s. \<exists> s'. (s \<oplus>\<^sub>S s' on x) \<in> P}"

adhoc_overloading liberate liberate_pred

lemma liberate_expr_pred: "\<lbrakk>P\<rbrakk>\<^sub>P \\ $x = \<lbrakk>P \\ $x\<rbrakk>\<^sub>P"
  by (rel_auto add: liberate_pred_def)
end