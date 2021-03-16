section \<open> UTP Predicates \<close>

theory utp_pred
    imports "Z_Toolkit.Z_Toolkit" "Shallow-Expressions.Shallow_Expressions" "Total_Recall.Total_Recall"
begin

subsection \<open> Core Definitions \<close>

consts
  utrue  :: "'p" ("true")
  ufalse :: "'p" ("false")

named_theorems pred
named_theorems pred_defs
named_theorems pred_transfer

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

definition [pred]: "true_pred = UNIV"
definition [pred]: "false_pred = {}"

adhoc_overloading utrue true_pred and utrue True
adhoc_overloading ufalse false_pred and ufalse False

purge_notation conj (infixr "\<and>" 35) and disj (infixr "\<or>" 30) and Not ("\<not> _" [40] 40)

consts 
  uconj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<and>" 35)
  udisj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<or>" 30)
  unot  :: "'a \<Rightarrow> 'a" ("\<not> _" [40] 40)

definition [pred]: "conj_pred = (\<inter>)"
definition [pred]: "disj_pred = (\<union>)"
definition [pred]: "not_pred = (uminus :: 'a set \<Rightarrow> 'a set)"

definition impl_rel (infixr "\<Rightarrow>" 25) where
[pred]: "impl_rel P Q = (- P) \<union> Q"

definition iff_rel (infixr "\<Leftrightarrow>" 25) where
[pred]: "iff_rel P Q = ((P \<Rightarrow> Q) \<and> (Q \<Rightarrow> P))"

adhoc_overloading 
  uconj conj and uconj conj_pred and
  udisj disj and udisj disj_pred and
  unot Not and unot not_pred

subsection \<open> Refinement \<close>

definition ref_by :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
[pred]: "P \<sqsubseteq> Q = (Q \<subseteq> P)"

definition sref_by :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
[pred]: "P \<sqsubset> Q = (Q \<subset> P)"

lemma refined_by_trans [trans]: "\<lbrakk> P \<sqsubseteq> Q; Q \<sqsubseteq> R \<rbrakk> \<Longrightarrow> P \<sqsubseteq> R"
  by (simp add: ref_by_def)

interpretation order "(\<sqsubseteq>)" "(\<sqsubset>)"
  by (unfold_locales, simp_all add: pred less_le_not_le)

subsection \<open> Proof Strategy \<close>

text \<open> The proof strategy converts a set-based representation into a predicate, and then uses the
  @{method expr_auto} tactic to try and prove the resulting conjecture. \<close>

method pred_simp uses add = (simp add: add pred_transfer pred usubst_eval unrest)
method pred_auto uses add = (pred_simp add: add; (expr_auto add: relcomp_unfold)?)
                                                        
lemma pred_eq_iff [pred_transfer]: "P = Q \<longleftrightarrow> \<lbrakk>P\<rbrakk>\<^sub>P = \<lbrakk>Q\<rbrakk>\<^sub>P"
  by (metis Collect_mem_eq SEXP_def set_pred_def)

lemma pred_ref_iff [pred_transfer]: "P \<sqsubseteq> Q \<longleftrightarrow> `\<lbrakk>Q\<rbrakk>\<^sub>P \<longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>P`"
  by (auto simp add: set_pred_def taut_def ref_by_def)

subsection \<open> Operators \<close>

lemma pred_empty [pred]: "\<lbrakk>{}\<rbrakk>\<^sub>P = (False)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_UNIV [pred]: "\<lbrakk>UNIV\<rbrakk>\<^sub>P = (True)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_Un [pred]: "\<lbrakk>P \<union> Q\<rbrakk>\<^sub>P = (\<lbrakk>P\<rbrakk>\<^sub>P \<or> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_Union [pred]: "\<lbrakk>\<Union> i \<in> I. P i\<rbrakk>\<^sub>P = (SUP i \<in> \<guillemotleft>I\<guillemotright>. \<lbrakk>P i\<rbrakk>\<^sub>P)\<^sub>e"
  by (auto simp add: expr_defs)

lemma pred_Int [pred]: "\<lbrakk>P \<inter> Q\<rbrakk>\<^sub>P = (\<lbrakk>P\<rbrakk>\<^sub>P \<and> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_Inter [pred]: "\<lbrakk>\<Inter> i \<in> I. P i\<rbrakk>\<^sub>P = (INF i \<in> \<guillemotleft>I\<guillemotright>. \<lbrakk>P i\<rbrakk>\<^sub>P)\<^sub>e"
  by (auto simp add: expr_defs)

lemma pred_Compl [pred]: "\<lbrakk>- P\<rbrakk>\<^sub>P = (\<not> \<lbrakk>P\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_set [pred]: "\<lbrakk>\<lbrakk>P\<rbrakk>\<^sub>u\<rbrakk>\<^sub>P = P"
  by (simp add: pred_set_def set_pred_def SEXP_def)

end
