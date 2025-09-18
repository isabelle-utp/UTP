section \<open> Weakest Preconditions \<close>

theory utp_wp
  imports utp_assertional utp_rel_prog
begin

lemma wp_assigns [wp]: "\<langle>\<sigma>\<rangle>\<^sub>a wp b = (\<sigma> \<dagger> b)\<^sub>e"
  by pred_auto

lemma wp_nd_assign [wp]: "(x := * ) wp b = (\<exists> v. [x\<leadsto>v] \<dagger> b)\<^sub>e"
  by pred_auto

theorem wp_choice [wp]: "(P \<sqinter> Q) wp R = (P wp R \<or> Q wp R)\<^sub>e"
  by (pred_auto)

theorem wp_choice' [wp]: "(P \<or> Q) wp R = (P wp R \<or> Q wp R)\<^sub>e"
  by (pred_auto)

lemma wp_UINF_ind [wp]: "(\<Sqinter> i . P(i)) wp b = (\<exists> i . P(i) wp b)\<^sub>e"
  by (pred_auto)

lemma wp_test [wp]: "(\<questiondown>b? wp c)\<^sub>e = (b \<and> c)\<^sub>e"
  by (pred_auto)

lemma wp_star [wp]: "P\<^sup>\<star> wp b = (\<exists>i. P \<^bold>^ i wp b)\<^sub>e"
  by (simp add: ustar_def wp)

lemma wp_while: 
  "(while_top B C) wp P = 
    (\<lambda> s. \<exists> s'. ((s = s' \<or> 
                 (\<exists>xs. xs \<noteq> [] \<and> (\<forall> i<length xs. B ((s # xs) ! i)
                   \<and> C ((s # xs) ! i, xs ! i)) \<and> s' = last xs))
                   \<and> \<not> B s' \<and> P s'))"
  by (simp add: while_chain_form wp_pred_def pre_def, pred_auto)

end