theory utp_unrest
  imports utp_pred
begin

definition [pred]: "unrest_pred x P = unrest_expr x \<lbrakk>P\<rbrakk>\<^sub>P"

adhoc_overloading unrest unrest_pred

lemma unrest_pred_expr [unrest]:
  "x \<sharp> P \<Longrightarrow> x \<sharp> (P)\<^sub>u"
  by pred_auto

lemma unrest_pred [unrest]: 
  fixes P Q :: "'a set"
  assumes "x \<sharp> P" "x \<sharp> Q"
  shows "x \<sharp> (P \<and> Q)" "x \<sharp> (P \<or> Q)" "x \<sharp> (P \<Rightarrow> Q)"
  using assms by pred_auto+

lemma unrest_true [unrest]: "x \<sharp> true_pred" 
  and unrest_false [unrest]: "x \<sharp> false_pred"
  by pred_auto+

end