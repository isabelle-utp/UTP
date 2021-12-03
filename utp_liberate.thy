subsection \<open> Liberation \<close>

theory utp_liberate
  imports utp_unrest utp_rel
begin

definition liberate_pred :: "'s set \<Rightarrow> 's scene \<Rightarrow> 's set" where
[pred]: "liberate_pred P x = {s. \<exists> s'. (s \<oplus>\<^sub>S s' on x) \<in> P}"

adhoc_overloading liberate liberate_pred

lemma liberate_expr_pred: "\<lbrakk>P\<rbrakk>\<^sub>P \\ x = \<lbrakk>P \\ x\<rbrakk>\<^sub>P"
  by (rel_auto add: liberate_pred_def)

lemma liberate_pred_unrest: "x \<sharp> (P::'a set) \<Longrightarrow> P \\ x = P"
  by (simp add: liberate_expr_pred unrest_liberate_iff unrest_pred_def utp_pred.pred_eq_iff)

lemma liberate_lens_pred [expr_simps]:
  "mwb_lens x \<Longrightarrow> P \\ $x = (\<lambda>s. \<exists>s'. P (s \<triangleleft>\<^bsub>x\<^esub> s'))"
  by (simp add: liberate_expr_def)

lemma liberate_lens': "mwb_lens x \<Longrightarrow> P \\ $x = (\<lambda>s. \<exists>v. P (put\<^bsub>x\<^esub> s v))"
  by (auto simp add: liberate_expr_def lens_defs fun_eq_iff)
     (metis mwb_lens_weak weak_lens.put_get)

lemma liberate_as_subst: "vwb_lens x \<Longrightarrow> e \\ $x = (\<exists> v. e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)\<^sub>e"
  by (expr_simp, metis vwb_lens.put_eq)

lemma unrest_liberate_pred: "a \<sharp> (P :: 'a set) \\ a"
  by pred_auto

lemma unrest_liberate_iff: "(a \<sharp> (P :: 'a set)) \<longleftrightarrow> (P \\ a = P)"
  by (pred_auto, metis (full_types) scene_override_overshadow_left)

lemma liberate_none_pred [simp]: "P \\ \<emptyset> = (P :: 'a set)"
  by pred_auto

lemma liberate_idem_pred [simp]: "(P :: 'a set) \\ a \\ a = P \\ a"
  by pred_auto

lemma liberate_commute_pred [simp]: "a \<bowtie>\<^sub>S b \<Longrightarrow> (P :: 'a set) \\ a \\ b = P \\ b \\ a"
  using scene_override_commute_indep by (pred_auto, fastforce+)

lemma liberate_false_pred [simp]: "{} \\ a = {}"
  by pred_simp

lemma liberate_disj_pred [simp]: "(P \<union> Q) \\ a = (P \\ a \<union> Q \\ a)"
  by pred_auto

end