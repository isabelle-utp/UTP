subsection \<open> Weakest Liberal Preconditions \<close>

theory utp_wlp
  imports utp_rel_laws utp_hoare
begin

named_theorems wp

definition wlp_pred :: "('s\<^sub>1,'s\<^sub>2)urel \<Rightarrow> ('s\<^sub>2 \<Rightarrow> bool) \<Rightarrow> ('s\<^sub>1 \<Rightarrow> bool)" where
[pred]: "wlp_pred Q r = pre (\<not> (Q ;; ((\<not> r\<^sup><)\<^sub>e)) :: ('s\<^sub>1,'s\<^sub>2)urel)"

expr_ctr wlp_pred

syntax
  "_wlp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "wlp" 60)

translations
  "_wlp Q r" == "CONST wlp_pred Q (r)\<^sub>e"

lemma wlp_seq [wp]: "(P ;; Q) wlp b = P wlp (Q wlp b)"
  by (pred_auto)

lemma wlp_assigns [wp]: "\<langle>\<sigma>\<rangle>\<^sub>a wlp b = (\<sigma> \<dagger> b)\<^sub>e"
  by pred_auto

lemma wlp_true [wp]: "p wlp True = (True)\<^sub>e"
  by pred_auto

lemma wlp_conj [wp]: "(P wlp (b \<and> c))\<^sub>e = ((P wlp b)\<^sub>e \<and> (P wlp c)\<^sub>e)"
  by (pred_auto)

theorem wlp_cond [wp]: "((P \<^bold>\<lhd> b \<^bold>\<rhd> Q) wlp r)  =((b \<longrightarrow> P  wlp r) \<and> ((\<not> b) \<longrightarrow> Q wlp r))\<^sub>e"
  by pred_auto

theorem wlp_skip_r [wp]: "II wlp r = r"
  by pred_auto

theorem wlp_abort [wp]:
  assumes"r \<noteq> (True)\<^sub>e"
  shows      
  "true wlp r =( False)\<^sub>e"
  using assms by pred_auto

lemma wlp_nd_assign [wp]: "(x := * ) wlp b = (\<forall> v. [x\<leadsto>v] \<dagger> b)\<^sub>e"
  by pred_auto

theorem wlp_choice [wp]: "(P \<sqinter> Q) wlp R = (P wlp R \<and> Q wlp R)\<^sub>e"
  by (pred_auto)

theorem wlp_choice' [wp]: "(P \<or> Q) wlp R = (P wlp R \<and> Q wlp R)\<^sub>e"
  by (pred_auto)

lemma wlp_UINF_ind [wp]: "(\<Sqinter> i . P(i)) wlp b = (\<forall> i . P(i) wlp b)\<^sub>e"
  by (pred_auto)

lemma wlp_USUP_pre [wp]:
  shows "P wlp (\<forall> i  . Q(i)) = (\<forall> i. P wlp Q(i))\<^sub>e"
  by (pred_auto; blast)

lemma wlp_test [wp]: "(\<questiondown>b? wlp c)\<^sub>e = (b \<longrightarrow> c)\<^sub>e"
  by (pred_auto)

(*
lemma wlp_rel_aext_unrest [wp]: "(\<lbrakk> vwb_lens a; a \<sharp> b \<rbrakk> \<longrightarrow> a:[P]\<^sup>+ wlp b)\<^sub>e = ((P wlp false) \<up>\<^sub>p a \<or> b)\<^sub>e"
  by (rel_simp, metis mwb_lens_def vwb_lens_def weak_lens.put_get)


lemma wlp_rel_aext_usedby [wp]: "\<lbrakk> vwb_lens a; a \<natural> b \<rbrakk> \<Longrightarrow> a:[P]\<^sup>+ wlp b = (P wlp (b \<restriction>\<^sub>e a)) \<oplus>\<^sub>p a"
  by (pred_auto, metis mwb_lens_def vwb_lens_mwb weak_lens.put_get)
 
lemma wlp_gcmd [wp]:
 "((b \<longrightarrow> P) wlp c)\<^sub>e = (b \<longrightarrow> P wlp c)\<^sub>e"
  by (simp add: rgcmd_def wp)



theorem wlp_hoare_link:
  "({p\<^bold>}Q\<^bold>{r\<^bold>} ,`p \<longrightarrow> Q wlp r`)urel"
  by pred_auto


text \<open> We can use the above theorem as a means to discharge Hoare triples with the following tactic \<close>

method hoare_wlp_auto uses defs = (simp add: wlp_hoare_link wp unrest usubst defs; pred_auto)

text \<open> If two programs have the same weakest precondition for any postcondition then the programs
  are the same. \<close>

theorem wlp_eq_intro: "\<lbrakk> \<And> r. P wlp r = Q wlp r \<rbrakk> \<longrightarrow> P = Q"
  by (pred_auto robust, fastforce+)
*)

end