section \<open> UTP Predicates \<close>

theory utp_pred
    imports "Z_Toolkit.Z_Toolkit" "Shallow-Expressions.Shallow_Expressions"
begin

subsection \<open> Core Definitions \<close>

type_synonym 's pred = "(bool, 's) expr"

text \<open> Convert a set-based representation (e.g. a binary relation) into a predicate. \<close>

definition set_pred :: "'s set \<Rightarrow> ('s \<Rightarrow> bool)" ("\<lbrakk>_\<rbrakk>\<^sub>P") where
[expr_defs]: "\<lbrakk>P\<rbrakk>\<^sub>P = [\<lambda> s. s \<in> P]\<^sub>e"

expr_ctr set_pred

text \<open> Convert a predicate into a set-based representation. \<close>

definition pred_set :: "('s \<Rightarrow> bool) \<Rightarrow> 's set" ("\<lbrakk>_\<rbrakk>\<^sub>u") where
[expr_defs]: "pred_set = Collect"

syntax "_pred_set" :: "logic \<Rightarrow> logic" ("'(_')\<^sub>u")
translations "(p)\<^sub>u" == "CONST pred_set (p)\<^sub>e"

subsection \<open> Proof Strategy \<close>

text \<open> The proof strategy converts a set-based representation into a predicate, and then uses the
  @{method expr_auto} tactic to try and prove the resulting conjecture. \<close>

named_theorems pred

method pred_simp = (simp add: pred usubst_eval unrest)
method pred_auto = (pred_simp; expr_auto)

lemma pred_eq_iff [pred]: "P = Q \<longleftrightarrow> \<lbrakk>P\<rbrakk>\<^sub>P = \<lbrakk>Q\<rbrakk>\<^sub>P"
  by (metis Collect_mem_eq SEXP_def set_pred_def)

lemma pred_leq_iff [pred]: "P \<subseteq> Q \<longleftrightarrow> \<lbrakk>P\<rbrakk>\<^sub>P \<le> \<lbrakk>Q\<rbrakk>\<^sub>P"
  by (auto simp add: set_pred_def)

subsection \<open> Operators \<close>

abbreviation "true \<equiv> (True)\<^sub>e"
abbreviation "false \<equiv> (False)\<^sub>e"

lemma pred_empty [pred]: "\<lbrakk>{}\<rbrakk>\<^sub>P = false"
  by (simp add: set_pred_def)

lemma pred_UNIV [pred]: "\<lbrakk>UNIV\<rbrakk>\<^sub>P = true"
  by (simp add: set_pred_def)

lemma pred_Un [pred]: "\<lbrakk>P \<union> Q\<rbrakk>\<^sub>P = (\<lbrakk>P\<rbrakk>\<^sub>P \<or> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_Union [pred]: "\<lbrakk>\<Union> i \<in> I. P i\<rbrakk>\<^sub>P = (SUP i \<in> \<guillemotleft>I\<guillemotright>. \<lbrakk>P i\<rbrakk>\<^sub>P)\<^sub>e"
  by (auto simp add: set_pred_def expr_defs)

lemma pred_Int [pred]: "\<lbrakk>P \<inter> Q\<rbrakk>\<^sub>P = (\<lbrakk>P\<rbrakk>\<^sub>P \<and> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_Inter [pred]: "\<lbrakk>\<Inter> i \<in> I. P i\<rbrakk>\<^sub>P = (INF i \<in> \<guillemotleft>I\<guillemotright>. \<lbrakk>P i\<rbrakk>\<^sub>P)\<^sub>e"
  by (auto simp add: set_pred_def expr_defs)

lemma pred_Compl [pred]: "\<lbrakk>- P\<rbrakk>\<^sub>P = (\<not> \<lbrakk>P\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_set [pred]: "\<lbrakk>\<lbrakk>P\<rbrakk>\<^sub>u\<rbrakk>\<^sub>P = P"
  by (simp add: pred_set_def set_pred_def SEXP_def)

end
