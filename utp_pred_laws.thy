section \<open> Predicate Laws \<close>

theory utp_pred_laws
  imports utp_pred
begin            

unbundle utp_lattice_syntax

lemma impl_neg_disj: "((P::'s pred) \<longrightarrow> (Q::'s pred)) = (\<not>P \<or> Q)"
  by (simp add: impl_pred_def fun_eq_iff conj_pred_def disj_pred_def not_pred_def)

lemma top_false: "\<top> = false"
  using ref_lattice.ccInf_empty by auto

lemma bot_true: "\<bottom> = true"
  using ref_lattice.Inf_UNIV by auto

lemma pred_impl_laws [simp]:
  "(true \<longrightarrow> P) = P" "(P \<longrightarrow> true) = true" "(false \<longrightarrow> P) = true" "(P \<longrightarrow> false) = (\<not> P)" "(P \<longrightarrow> P) = true"
  by pred_simp+

lemma not_SUP:
  fixes P :: "'i \<Rightarrow> '\<alpha> pred"
  shows "(\<not> (\<Sqinter> x\<in>A. P x)) = (\<Squnion> x\<in>A. \<not> P x)"
  by pred_simp

lemma not_INF:
  fixes P :: "'i \<Rightarrow> '\<alpha> pred"
  shows "(\<not> (\<Squnion> x\<in>A. P x)) = (\<Sqinter> x\<in>A. \<not> P x)"
  by pred_simp

lemma ex_pred_simps [simp]:
  "(\<exists> x \<Zspot> true) = true" "(\<exists> x \<Zspot> false) = false"
  by (pred_auto+)

lemma conj_INF_dist: 
  fixes P :: "'s pred"
  assumes "I \<noteq> {}"
  shows "(P \<and> (\<Squnion> i\<in>I. F i)) = (\<Squnion> i\<in>I. P \<and> F i)"
  using assms by pred_auto

lemma conj_SUP_dist:
  fixes P :: "'s pred"
  shows "(P \<and> (\<Sqinter> i\<in>I. F i)) = (\<Sqinter> i\<in>I. P \<and> F i)"
  by pred_auto

lemma disj_SUP_dist:
  fixes P :: "'s pred"
  assumes "I \<noteq> {}"
  shows "(P \<or> (\<Sqinter> i\<in>I. F i)) = (\<Sqinter> i\<in>I. P \<or> F i)"
  using assms by pred_auto

lemma cond_SUP_dist: "(\<Sqinter> i\<in>I. F i) \<triangleleft> b \<triangleright> (\<Sqinter> i\<in>I. G i) = (\<Sqinter> i\<in>I. F i \<triangleleft> b \<triangleright> G i)"
  by (pred_simp add: image_image)

lemma INFs_combine:
  fixes P :: "'i \<Rightarrow> 'j \<Rightarrow> 'a pred"
  shows "(\<Squnion>i\<in>I. \<Squnion>j\<in>J. P i j) = (\<Squnion>(i,j)\<in>I\<times>J. P i j)"
  by pred_auto

lemma SUPs_combine:
  fixes P :: "'i \<Rightarrow> 'j \<Rightarrow> 'a pred"
  shows "(\<Sqinter>i\<in>I. \<Sqinter>j\<in>J. P i j) = (\<Sqinter>(i,j)\<in>I\<times>J. P i j)"
  by pred_auto

end