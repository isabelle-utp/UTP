section \<open> UTP Predicates \<close>

theory utp_pred
    imports "Z_Toolkit.Z_Toolkit" "Shallow-Expressions.Shallow_Expressions"
begin
                    
unbundle Expression_Syntax Z_Syntax

subsection \<open> Core Definitions \<close>

consts
  utrue  :: "'p" ("true")
  ufalse :: "'p" ("false")

named_theorems pred and pred_core and pred_transfer

text \<open> Convert a set-based representation (e.g. a binary relation) into a predicate. \<close>

definition set_pred :: "'s set \<Rightarrow> ('s \<Rightarrow> bool)" ("\<lbrakk>_\<rbrakk>\<^sub>P") where
[expr_defs]: "\<lbrakk>P\<rbrakk>\<^sub>P = [\<lambda> s. s \<in> P]\<^sub>e"

expr_ctr set_pred

text \<open> Convert a predicate into a set-based representation. \<close>

definition pred_set :: "('s \<Rightarrow> bool) \<Rightarrow> 's set" ("\<lbrakk>_\<rbrakk>\<^sub>u") where
[expr_defs]: "pred_set = Collect"

syntax "_pred_set" :: "logic \<Rightarrow> logic" ("'(_')\<^sub>u")
translations "(p)\<^sub>u" == "CONST pred_set (p)\<^sub>e"

definition [pred_core]: "true_pred = UNIV"
definition [pred_core]: "false_pred = {}"

adhoc_overloading utrue true_pred and utrue True
adhoc_overloading ufalse false_pred and ufalse False

consts 
  uconj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  udisj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" 
  unot  :: "'a \<Rightarrow> 'a" 

bundle UTP_Logic_Syntax
begin

no_notation conj (infixr "\<and>" 35) and disj (infixr "\<or>" 30) and Not ("\<not> _" [40] 40)
notation uconj (infixr "\<and>" 35) and udisj (infixr "\<or>" 30) and unot ("\<not> _" [40] 40)

end

unbundle UTP_Logic_Syntax

definition [pred_core]: "conj_pred = (\<inter>)"
definition [pred_core]: "disj_pred = (\<union>)"
definition [pred_core]: "not_pred = (uminus :: 'a set \<Rightarrow> 'a set)"
definition [pred_core]: "diff_pred = (minus :: 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set)"

adhoc_overloading 
  uconj conj and uconj conj_pred and
  udisj disj and udisj disj_pred and
  unot Not and unot not_pred

definition impl_pred (infixr "\<Rightarrow>" 25) where
[pred_core]: "impl_pred P Q = (- P) \<union> Q"

definition iff_pred (infixr "\<Leftrightarrow>" 25) where
[pred_core]: "iff_pred P Q = ((P \<Rightarrow> Q) \<and> (Q \<Rightarrow> P))"

subsection \<open> Refinement \<close>

instantiation set :: (type) refine
begin

definition ref_by_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
[pred_core]: "P \<sqsubseteq> Q = (Q \<subseteq> P)"

definition sref_by_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
[pred_core]: "P \<sqsubset> Q = (Q \<subset> P)"

instance
  by (intro_classes, unfold_locales, auto simp add: pred_core)

end

interpretation ref_order: order "(\<sqsubseteq>) :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool" "(\<sqsubset>)"
  by (unfold_locales, simp_all add: pred_core less_le_not_le)

interpretation ref_lattice: complete_lattice "\<Union>" "\<Inter>" "(\<union>)" "(\<sqsubseteq>)" "(\<sqsubset>)" "(\<inter>)" "UNIV" "{}"
  by (unfold_locales, auto simp add: pred_core)

syntax
  "_mu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu> _ \<bullet> _" [0, 10] 10)
  "_nu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu> _ \<bullet> _" [0, 10] 10)

notation gfp ("\<mu>")
notation lfp ("\<nu>")

translations
  "\<nu> X \<bullet> P" == "CONST lfp (\<lambda> X. P)"
  "\<mu> X \<bullet> P" == "CONST gfp (\<lambda> X. P)"

subsection \<open> Proof Strategy \<close>

text \<open> The proof strategy converts a set-based representation into a predicate, and then uses the
  @{method expr_auto} tactic to try and prove the resulting conjecture. \<close>

method pred_simp uses add = (simp add: add pred_transfer pred_core pred usubst_eval unrest)
method pred_auto uses add = (pred_simp add: add; (expr_auto add: relcomp_unfold)?)
                                                        
lemma pred_eq_iff [pred_transfer]: "P = Q \<longleftrightarrow> \<lbrakk>P\<rbrakk>\<^sub>P = \<lbrakk>Q\<rbrakk>\<^sub>P"
  by (metis Collect_mem_eq SEXP_def set_pred_def)

lemma pred_ref_iff [pred_transfer]: "P \<sqsubseteq> Q \<longleftrightarrow> `\<lbrakk>Q\<rbrakk>\<^sub>P \<longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>P`"
  by (auto simp add: set_pred_def taut_def pred_core)

subsection \<open> Operators \<close>

lemma pred_empty [pred_core]: "\<lbrakk>{}\<rbrakk>\<^sub>P = (False)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_UNIV [pred_core]: "\<lbrakk>UNIV\<rbrakk>\<^sub>P = (True)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_Un [pred_core]: "\<lbrakk>P \<union> Q\<rbrakk>\<^sub>P = (\<lbrakk>P\<rbrakk>\<^sub>P \<or> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_Union [pred_core]: "\<lbrakk>\<Union> i \<in> I. P i\<rbrakk>\<^sub>P = (SUP i \<in> \<guillemotleft>I\<guillemotright>. \<lbrakk>P i\<rbrakk>\<^sub>P)\<^sub>e"
  by (auto simp add: expr_defs)

lemma pred_Int [pred_core]: "\<lbrakk>P \<inter> Q\<rbrakk>\<^sub>P = (\<lbrakk>P\<rbrakk>\<^sub>P \<and> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_conj [pred_core]: "\<lbrakk>P \<and> Q\<rbrakk>\<^sub>P = (\<lbrakk>P\<rbrakk>\<^sub>P \<and> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: pred_core)

lemma pred_disj [pred_core]: "\<lbrakk>P \<or> Q\<rbrakk>\<^sub>P = (\<lbrakk>P\<rbrakk>\<^sub>P \<or> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: pred_core)

lemma pred_Inter [pred_core]: "\<lbrakk>\<Inter> i \<in> I. P i\<rbrakk>\<^sub>P = (INF i \<in> \<guillemotleft>I\<guillemotright>. \<lbrakk>P i\<rbrakk>\<^sub>P)\<^sub>e"
  by (auto simp add: expr_defs)

lemma pred_Compl [pred_core]: "\<lbrakk>- P\<rbrakk>\<^sub>P = (\<not> \<lbrakk>P\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: set_pred_def)

lemma pred_not [pred_core]: "\<lbrakk>\<not> P\<rbrakk>\<^sub>P = (\<not> \<lbrakk>P\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: not_pred_def set_pred_def)

lemma pred_impl [pred_core]: "\<lbrakk>P \<Rightarrow> Q\<rbrakk>\<^sub>P = (\<lbrakk>P\<rbrakk>\<^sub>P \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
  by (simp add: pred_core)

lemma pred_iff [pred_core]: "\<lbrakk>P \<Leftrightarrow> Q\<rbrakk>\<^sub>P = (\<lbrakk>P\<rbrakk>\<^sub>P \<longleftrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
  by (auto simp add: pred_core)

lemma pred_set [pred_core]: "\<lbrakk>\<lbrakk>P\<rbrakk>\<^sub>u\<rbrakk>\<^sub>P = P"
  by (simp add: pred_set_def set_pred_def SEXP_def)

subsection \<open> Laws \<close>

lemma true_false_pred_expr [simp]: "(true)\<^sub>u = true" "(false)\<^sub>u = false"
  by (simp_all add: SEXP_def pred_set_def true_pred_def false_pred_def)

interpretation pred_ba: boolean_algebra diff_pred not_pred conj_pred "(\<sqsupseteq>)" "(\<sqsupset>)"
  disj_pred false_pred true_pred
  by (unfold_locales; pred_auto)

lemma pred_impl_laws [simp]: 
  "(true \<Rightarrow> P) = P" "(P \<Rightarrow> true) = true" "(false \<Rightarrow> P) = true" "(P \<Rightarrow> false) = (\<not> P)" "(P \<Rightarrow> P) = true"
  by pred_simp+

text \<open> In accordance with \cite{hoare1998} we turn the lattice operators upside down \<close>
bundle utp_lattice_syntax
begin

notation
  bot ("\<top>") and
  top ("\<bottom>") and
  inf  (infixl "\<squnion>" 70) and
  sup  (infixl "\<sqinter>" 65) and
  Inf  ("\<Squnion> _" [900] 900) and
  Sup  ("\<Sqinter> _" [900] 900)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)

end

end
