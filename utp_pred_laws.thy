section \<open> Predicate Laws \<close>

theory utp_pred_laws
  imports utp_pred
begin

lemma impl_neg_disj: "((P::'s pred) \<longrightarrow> (Q::'s pred)) = (\<not>P \<or> Q)"
  by (simp add: impl_pred_def fun_eq_iff conj_pred_def disj_pred_def not_pred_def)

lemma top_false: "\<top> = false"
  using ref_lattice.ccInf_empty by auto

lemma bot_true: "\<bottom> = true"
  using ref_lattice.Inf_UNIV by auto

lemma pred_impl_laws [simp]:
  "(true \<longrightarrow> P) = P" "(P \<longrightarrow> true) = true" "(false \<longrightarrow> P) = true" "(P \<longrightarrow> false) = (\<not> P)" "(P \<longrightarrow> P) = true"
  by pred_simp+

end