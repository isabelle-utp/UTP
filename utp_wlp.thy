subsection \<open> Weakest Liberal Preconditions \<close>

theory utp_wlp
  imports utp_rel_laws utp_hoare
begin

lemma wlp_assigns [wp]: "\<langle>\<sigma>\<rangle>\<^sub>a wlp b = (\<sigma> \<dagger> b)\<^sub>e"
  by pred_auto

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

lemma wlp_star [wp]: "P\<^sup>\<star> wlp b = (\<forall>i. P \<^bold>^ i wlp b)\<^sub>e"
  by (simp add: ustar_def wp)

(*
lemma wlp_rel_aext_unrest [wp]: "(\<lbrakk> vwb_lens a; a \<sharp> b \<rbrakk> \<longrightarrow> a:[P]\<^sup>+ wlp b)\<^sub>e = ((P wlp false) \<up>\<^sub>p a \<or> b)\<^sub>e"
  by (rel_simp, metis mwb_lens_def vwb_lens_def weak_lens.put_get)


lemma wlp_rel_aext_usedby [wp]: "\<lbrakk> vwb_lens a; a \<natural> b \<rbrakk> \<Longrightarrow> a:[P]\<^sup>+ wlp b = (P wlp (b \<restriction>\<^sub>e a)) \<oplus>\<^sub>p a"
  by (pred_auto, metis mwb_lens_def vwb_lens_mwb weak_lens.put_get)
 
lemma wlp_gcmd [wp]:
 "((b \<longrightarrow> P) wlp c)\<^sub>e = (b \<longrightarrow> P wlp c)\<^sub>e"
  by (simp add: rgcmd_def wp)
*)

text \<open> We can use the above theorems as a means to discharge Hoare triples with the following proof method \<close>

method hoare_wlp_auto uses defs = (simp add: wlp_hoare_link wp unrest usubst defs; pred_auto)

text \<open> If two programs have the same weakest precondition for any postcondition then the programs
  are the same. \<close>

theorem wlp_eq_intro: "\<lbrakk> \<And> r. P wlp r = Q wlp r \<rbrakk> \<Longrightarrow> P = Q"
  by (pred_auto, fastforce+)

end