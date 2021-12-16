subsection \<open> Liberation \<close>

theory utp_liberate
  imports utp_unrest utp_rel
begin

text \<open>There is some value for x that makes predicate P hold\<close>
definition liberate_pred :: "'s set \<Rightarrow> 's scene \<Rightarrow> 's set" where
[pred]: "liberate_pred P x = {s. \<exists> s'. (s \<oplus>\<^sub>S s' on x) \<in> P}"

adhoc_overloading liberate liberate_pred

lemma liberate_pred_in: "s \<in> (P \\ x) = (\<exists> s'. (s \<oplus>\<^sub>S s' on x) \<in> P)"
  by (simp add: liberate_pred_def)

lemma liberate_expr_pred: "\<lbrakk>P \\ x\<rbrakk>\<^sub>P = \<lbrakk>P\<rbrakk>\<^sub>P \\ x "
  by (rel_auto add: liberate_pred_def)

lemma liberate_pred_unrest: "x \<sharp> (P::'a set) \<Longrightarrow> P \\ x = P"
  by (simp add: liberate_expr_pred unrest_liberate_iff unrest_pred_def utp_pred.pred_eq_iff)

lemma unrest_liberate_pred: "a \<sharp> (P :: 'a set) \\ a"
  by pred_auto

lemma unrest_liberate_pred_iff: "(a \<sharp> (P :: 'a set)) \<longleftrightarrow> (P \\ a = P)"
  by (pred_auto, metis (full_types) scene_override_overshadow_left)

lemma liberate_pred_none [simp]: "P \\ \<emptyset> = (P :: 'a set)"
  by pred_auto

lemma liberate_pred_idem [simp]: "(P :: 'a set) \\ a \\ a = P \\ a"
  by pred_auto

lemma liberate_commute_pred [simp]: "a \<bowtie>\<^sub>S b \<Longrightarrow> (P :: 'a set) \\ a \\ b = P \\ b \\ a"
  using scene_override_commute_indep by (pred_auto, fastforce+)

lemma liberate_empty [simp]: "{} \\ a = {}"
  by pred_simp

lemma liberate_univ [simp]: "UNIV \\ a = UNIV"
  by pred_simp

lemma liberate_disj_pred [simp]: "(P \<union> Q) \\ a = (P \\ a \<union> Q \\ a)"
  by pred_auto

end