subsection \<open> UTP Relations \<close>

theory utp_rel
  imports utp_pred
begin

type_synonym ('s\<^sub>1, 's\<^sub>2) rpred = "('s\<^sub>1 \<times> 's\<^sub>2) pred"

subsection \<open> Operators \<close>

notation Id ("II")

definition assigns :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> 's\<^sub>1 \<leftrightarrow> 's\<^sub>2" ("\<langle>_\<rangle>") where
  "assigns \<sigma> = pfun_graph (fun_pfun \<sigma>)"

definition seq_pred :: "('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>2, 's\<^sub>3) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>3) rpred" (infixr ";;" 75) where
[expr_defs]: "seq_pred P Q = (\<lambda> (s\<^sub>1, s\<^sub>2). (s\<^sub>1, s\<^sub>2) \<in> \<lbrakk>P\<rbrakk>\<^sub>u O \<lbrakk>Q\<rbrakk>\<^sub>u)"

subsection \<open> Predicate Semantics \<close>

lemma pred_assigns: "\<lbrakk>\<langle>\<sigma>\<rangle>\<rbrakk>\<^sub>P (s, s') = (s' = \<sigma> s)"
  by (simp add: expr_defs assigns_def pfun_entries_pabs pfun_graph_pabs)

lemma pred_assigns' [pred]: "\<lbrakk>\<langle>\<sigma>\<rangle>\<rbrakk>\<^sub>P = ($\<^bold>v\<^sup>> = \<sigma>\<^sup><)\<^sub>e"
  by (auto simp add: expr_defs assigns_def lens_defs pfun_entries_pabs pfun_graph_pabs prod.case_eq_if)

lemma pred_relcomp_seq [pred]: "\<lbrakk>P O Q\<rbrakk>\<^sub>P = (\<lbrakk>P\<rbrakk>\<^sub>P ;; \<lbrakk>Q\<rbrakk>\<^sub>P)"
  by (auto simp add: expr_defs)

subsection \<open> Algebraic Laws \<close>

lemma seq_pred: "(P ;; Q) = (\<exists> s\<^sub>0. P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>)\<^sub>e"
  by (expr_auto)

lemma seq_var: "vwb_lens x \<Longrightarrow> (P ;; Q) = (SUP v. (P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk>)\<^sub>e ;; (Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup><\<rbrakk>)\<^sub>e)"
  by (expr_simp add: prod.case_eq_if relcomp_unfold, metis vwb_lens_wb wb_lens.get_put)

lemma "($x\<^sup>< = $x\<^sup>>)\<^sub>u \<^bold>; ($x\<^sup>< = $x\<^sup>>)\<^sub>u = ($x\<^sup>< = $x\<^sup>>)\<^sub>u"
  by (pred_auto)

lemma "\<langle>id\<rangle> = II"
  by (pred_auto)

lemma "\<langle>\<sigma>\<rangle> \<^bold>; \<langle>\<rho>\<rangle> = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>"
  by (pred_auto)


end