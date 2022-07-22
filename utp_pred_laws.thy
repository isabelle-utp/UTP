section \<open> Predicate Laws \<close>

theory utp_pred_laws
  imports utp_pred
begin

interpretation pred_ba: boolean_algebra diff_pred not_pred conj_pred "(\<sqsupseteq>)" "(\<sqsupset>)"
  disj_pred false_pred true_pred
  by (unfold_locales; pred_auto add: sref_by_fun_def)

lemma pred_impl_laws [simp]: 
  "(true \<longrightarrow> P) = P" "(P \<longrightarrow> true) = true" "(false \<longrightarrow> P) = true" "(P \<longrightarrow> false) = (\<not> P)" "(P \<longrightarrow> P) = true"
  by pred_simp+

end