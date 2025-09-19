subsection \<open> Hoare Logic \<close>

theory utp_hoare
imports utp_assertional utp_rel_prog utp_wp
begin              

subsection \<open> Sequence Laws \<close>

lemma seq_hoare_r: "\<lbrakk> \<^bold>{p\<^bold>}Q\<^sub>1\<^bold>{s\<^bold>} ; \<^bold>{s\<^bold>}Q\<^sub>2\<^bold>{r\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{r\<^bold>}"
  by (pred_auto)

lemma seq_thoare_r: "\<lbrakk> H[p]Q\<^sub>1[s] ; H[s]Q\<^sub>2[r] \<rbrakk> \<Longrightarrow> H[p]Q\<^sub>1 ;; Q\<^sub>2[r]"
  by (pred_auto, meson)

lemma seq_hoare_invariant [hoare_safe]: "\<lbrakk> \<^bold>{p\<^bold>}Q\<^sub>1\<^bold>{p\<^bold>} ; \<^bold>{p\<^bold>}Q\<^sub>2\<^bold>{p\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{p\<^bold>}"
  using seq_hoare_r by blast

lemma seq_hoare_stronger_pre_1 [hoare_safe]: 
  "\<lbrakk> \<^bold>{p \<and> q\<^bold>}Q\<^sub>1\<^bold>{p \<and> q\<^bold>} ; \<^bold>{p \<and> q\<^bold>}Q\<^sub>2\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p \<and> q\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{q\<^bold>}"
  using seq_hoare_r by blast

lemma seq_hoare_stronger_pre_2 [hoare_safe]: 
  "\<lbrakk> \<^bold>{p \<and> q\<^bold>}Q\<^sub>1\<^bold>{p \<and> q\<^bold>} ; \<^bold>{p \<and> q\<^bold>}Q\<^sub>2\<^bold>{p\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p \<and> q\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{p\<^bold>}"
  using seq_hoare_r by blast
    
lemma seq_hoare_inv_r_2 [hoare]: "\<lbrakk> \<^bold>{p\<^bold>}Q\<^sub>1\<^bold>{q\<^bold>} ; \<^bold>{q\<^bold>}Q\<^sub>2\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{q\<^bold>}"
  using seq_hoare_r by blast

lemma seq_hoare_inv_r_3 [hoare]: "\<lbrakk> \<^bold>{p\<^bold>}Q\<^sub>1\<^bold>{p\<^bold>} ; \<^bold>{p\<^bold>}Q\<^sub>2\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{q\<^bold>}"
  using seq_hoare_r by blast

subsection \<open> Assignment Laws \<close>

lemma assigns_hoare_r [hoare_safe]: "`p \<longrightarrow> \<sigma> \<dagger> q` \<Longrightarrow> \<^bold>{p\<^bold>}\<langle>\<sigma>\<rangle>\<^sub>a\<^bold>{q\<^bold>}"
  by pred_auto

lemma assigns_thoare_r [hoare_safe]: "`p \<longrightarrow> \<sigma> \<dagger> q` \<Longrightarrow> H[p]\<langle>\<sigma>\<rangle>\<^sub>a[q]"
  by pred_auto

lemma assigns_backward_hoare_r: 
  "\<^bold>{\<sigma> \<dagger> p\<^bold>}\<langle>\<sigma>\<rangle>\<^sub>a\<^bold>{p\<^bold>}"
  by pred_auto

lemma assigns_backward_thoare_r: 
  "H[\<sigma> \<dagger> p]\<langle>\<sigma>\<rangle>\<^sub>a[p]"
  by pred_auto

lemma assign_floyd_hoare_r:
  assumes "vwb_lens x"
  shows "\<^bold>{p\<^bold>} x := e \<^bold>{\<exists> v . p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> $x = e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<^bold>}"
  using assms
  by (pred_auto, metis lens_override_def lens_override_idem)

lemma assign_floyd_thoare_r:
  assumes "vwb_lens x"
  shows "H[p] x := e [\<exists> v . p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> $x = e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>]"
  using assms
  by (pred_auto, metis lens_override_def lens_override_idem)

lemma assigns_init_hoare [hoare_safe]:
  "\<lbrakk> vwb_lens x; $x \<sharp> p; $x \<sharp> v; \<^bold>{$x = v \<and> p\<^bold>}S\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}(x := v) ;; S\<^bold>{q\<^bold>}"
  by pred_auto (metis mwb_lens_weak vwb_lens_mwb weak_lens.put_get)

lemma assigns_init_hoare_general [hoare_safe]:
  "\<lbrakk> vwb_lens x; \<And> x\<^sub>0. \<^bold>{$x = v\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> p\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>\<^bold>}S\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}x := v ;; S\<^bold>{q\<^bold>}"
  by (rule seq_hoare_r, rule assign_floyd_hoare_r, simp, pred_auto)

lemma assigns_init_thoare_general [hoare_safe]:
  "\<lbrakk> vwb_lens x; \<And> x\<^sub>0. H[$x = v\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<and> p\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>]S[q] \<rbrakk> \<Longrightarrow> H[p] x := v ;; S [q]"
  by (rule seq_thoare_r, rule assign_floyd_thoare_r, simp, pred_auto)

lemma assigns_final_hoare [hoare_safe]:
  "\<^bold>{p\<^bold>}S\<^bold>{\<sigma> \<dagger> q\<^bold>} \<Longrightarrow> \<^bold>{p\<^bold>}S ;; \<langle>\<sigma>\<rangle>\<^sub>a\<^bold>{q\<^bold>}"
  by (pred_auto)

lemma assigns_final_thoare [hoare_safe]:
  "H[p]S[\<sigma> \<dagger> q] \<Longrightarrow> H[p]S ;; \<langle>\<sigma>\<rangle>\<^sub>a[q]"
  by (pred_auto)

lemma skip_hoare_r [hoare_safe]: "\<^bold>{p\<^bold>}II\<^bold>{p\<^bold>}"
  by pred_auto

lemma skip_thoare_r [hoare_safe]: "H[p]II[p]"
  by pred_auto

lemma skip_hoare_impl_r [hoare_safe]: "`p \<longrightarrow> q` \<Longrightarrow> \<^bold>{p\<^bold>}II\<^bold>{q\<^bold>}"
  by pred_auto  

lemma skip_thoare_impl_r [hoare_safe]: "`p \<longrightarrow> q` \<Longrightarrow> H[p]II[q]"
  by pred_auto  

subsection \<open> Conditional Laws \<close>

lemma cond_hoare_r [hoare_safe]: "\<lbrakk> \<^bold>{b \<and> p\<^bold>}S\<^bold>{q\<^bold>} ; \<^bold>{\<not>b \<and> p\<^bold>}T\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}S \<lhd> b \<rhd> T\<^bold>{q\<^bold>}"
  by pred_auto

lemma cond_thoare_r [hoare_safe]: "\<lbrakk> H[b \<and> p] S [q] ; H[\<not>b \<and> p]T[q] \<rbrakk> \<Longrightarrow> H[p]S \<lhd> b \<rhd> T[q]"
  by (pred_auto, blast)

lemma cond_hoare_r_wp: 
  assumes "\<^bold>{p'\<^bold>}S\<^bold>{q\<^bold>}" and "\<^bold>{p''\<^bold>}T\<^bold>{q\<^bold>}"
  shows "\<^bold>{(b \<and> p') \<sqinter> (\<not>b \<and> p'')\<^bold>} S \<lhd> b \<rhd> T \<^bold>{q\<^bold>}"
  using assms by pred_auto

lemma cond_hoare_r_sp:
  assumes "\<^bold>{(b \<and> p)\<^bold>}S\<^bold>{q\<^bold>}" and "\<^bold>{\<not>b \<and> p\<^bold>}T\<^bold>{s\<^bold>}"
  shows "\<^bold>{p\<^bold>}S \<lhd> b \<rhd> T\<^bold>{q \<or> s\<^bold>}"
  using assms by pred_auto

lemma hoare_ndet [hoare_safe]: 
  assumes "\<^bold>{p\<^bold>}P\<^bold>{q\<^bold>}" "\<^bold>{p\<^bold>}Q\<^bold>{q\<^bold>}"
  shows "\<^bold>{p\<^bold>}(P \<sqinter> Q)\<^bold>{q\<^bold>}"
  using assms by (pred_auto)

lemma thoare_ndet [hoare_safe]: 
  assumes "H[p]P[q]" "H[p]Q[q]"
  shows "H[p](P \<sqinter> Q)[q]"
  using assms by (pred_auto)

lemma hoare_disj [hoare_safe]: 
  assumes "\<^bold>{p\<^bold>}P\<^bold>{q\<^bold>}" "\<^bold>{p\<^bold>}Q\<^bold>{q\<^bold>}"
  shows "\<^bold>{p\<^bold>}(P \<sqinter> Q)\<^bold>{q\<^bold>}"
  using assms by (pred_auto)

lemma hoare_UINF [hoare_safe]:
  assumes "\<And>i. i \<in> A \<Longrightarrow> \<^bold>{p\<^bold>}P(i)\<^bold>{q\<^bold>}"
  shows "\<^bold>{p\<^bold>}(\<Sqinter> {P(i)|i. i\<in>A})\<^bold>{q\<^bold>}"
  by (pred_auto assms: assms)

subsection \<open> Recursion Laws \<close>

lemma nu_hoare_r_partial: 
  assumes induct_step: "\<And>P st. \<^bold>{p\<^bold>}P\<^bold>{q\<^bold>} \<Longrightarrow> \<^bold>{p\<^bold>}F P\<^bold>{q\<^bold>}"   
  shows "\<^bold>{p\<^bold>}\<nu> F\<^bold>{q\<^bold>}"
  using assms
  unfolding hoare_r_def pred_ref_iff_le
  by (rule lfp_lowerbound, pred_auto)

lemma mu_hoare_r:
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<^bold>{p \<and> (e,\<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright>\<^bold>}P\<^bold>{q\<^bold>} \<Longrightarrow> \<^bold>{p \<and> e = \<guillemotleft>st\<guillemotright>\<^bold>}F P\<^bold>{q\<^bold>}"   
  shows "\<^bold>{p\<^bold>}\<mu> F \<^bold>{q\<^bold>}"
  unfolding hoare_r_def
proof (rule mu_rec_total_utp_rule[OF WF M , of _ e ], goal_cases)
  case (1 st)
  then show ?case 
    using induct_step[unfolded hoare_r_def, of st "(p\<^sup>< \<and> (e\<^sup><, \<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright> \<longrightarrow> q\<^sup>>)\<^sub>e"]
      by subst_eval
qed

lemma mu_hoare_r':
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<And> st P. \<^bold>{p \<and> (e,\<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright>\<^bold>} P \<^bold>{q\<^bold>} \<Longrightarrow> \<^bold>{p \<and> e = \<guillemotleft>st\<guillemotright>\<^bold>} F P \<^bold>{q\<^bold>}" 
  assumes I0: "`p' \<longrightarrow> p`"  
  shows "\<^bold>{p'\<^bold>} \<mu> F \<^bold>{q\<^bold>}"
  using I0 M WF assms(3) mu_hoare_r pre_str_hoare_r by blast

subsection \<open> Iteration Rules \<close>

lemma iter_hoare_r [hoare_safe]: "\<^bold>{P\<^bold>}S\<^bold>{P\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>}S\<^sup>\<star>\<^bold>{P\<^bold>}"
  by (rel_auto add: Collect_mono_iff, metis rtrancl_induct)

lemma iter_hoare_r_iff: "\<^bold>{P\<^bold>}S\<^sup>\<star>\<^bold>{P\<^bold>} \<longleftrightarrow> \<^bold>{P\<^bold>}S\<^bold>{P\<^bold>}"
  by (rel_auto add: Collect_mono_iff, metis rtrancl_induct) 

lemma star_hoare_r [hoare_safe]: 
  "\<lbrakk> \<^bold>{I\<^bold>}S\<^bold>{I\<^bold>}; `P \<longrightarrow> I`; `I \<longrightarrow> Q` \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>}S\<^sup>\<star>\<^bold>{Q\<^bold>}"
  by (rel_auto add: Collect_mono_iff, metis rtrancl_induct)

lemma while_hoare_r [hoare_safe]:
  assumes "\<^bold>{p \<and> b\<^bold>}S\<^bold>{p\<^bold>}"
  shows "\<^bold>{p\<^bold>}while b do S od\<^bold>{\<not>b \<and> p\<^bold>}"
proof (simp add: while_top_def hoare_r_def assms)
  have "(p\<^sup>< \<longrightarrow> (\<not> b \<and> p)\<^sup>>)\<^sub>e \<sqsubseteq> S ;; (p\<^sup>< \<longrightarrow> (\<not> b \<and> p)\<^sup>>)\<^sub>e \<lhd> b \<rhd> II"
    using assms by pred_auto
  then show "(p\<^sup>< \<longrightarrow> (\<not> b \<and> p)\<^sup>>)\<^sub>e \<sqsubseteq> (\<nu> X \<bullet> S ;; X \<lhd> b \<rhd> II)"
    by (simp add: pred_ref_iff_le lfp_lowerbound)
qed

text \<open> While loops with invariant decoration \<close>

definition while_inv :: "(bool, 's) expr \<Rightarrow> (bool, 's) expr \<Rightarrow> 's hrel \<Rightarrow> 's hrel" where
"while_inv b p P = while_top b P"

definition while_inv_bot :: "(bool, 's) expr \<Rightarrow> (bool, 's) expr \<Rightarrow> 's hrel \<Rightarrow> 's hrel" where
"while_inv_bot b p P = while_bot b P"

syntax
  "_while_inv_top" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("while\<^sup>\<top> _ invr _ do _ od")
  "_while_inv_top" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("while _ invr _ do _ od")
  "_while_inv_bot" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("while\<^sub>\<bottom> _ invr _ do _ od")

translations
  "_while_inv_top b I P" == "CONST while_inv (b)\<^sub>e (I)\<^sub>e P"
  "_while_inv_bot b I P" == "CONST while_inv_bot (b)\<^sub>e (I)\<^sub>e P"

lemma while_invr_hoare_r [hoare_safe]:
  assumes "\<^bold>{p \<and> b\<^bold>}S\<^bold>{p\<^bold>}" "`pre' \<longrightarrow> p`" "`(\<not>b \<and> p) \<longrightarrow> post'`"
  shows "\<^bold>{pre'\<^bold>}while b invr p do S od\<^bold>{post'\<^bold>}"
  unfolding while_inv_def using assms while_hoare_r hoare_r_conseq by blast

lemma while_r_minimal_partial:
  assumes seq_step: "`p \<longrightarrow> invar`"
  assumes induct_step: "\<^bold>{invar \<and> b\<^bold>} C \<^bold>{invar\<^bold>}"  
  shows "\<^bold>{p\<^bold>}while b do C od\<^bold>{\<not>b \<and> invar\<^bold>}"
  using induct_step pre_str_hoare_r seq_step while_hoare_r by blast

lemma approx_chain: 
  "(\<Sqinter>n::nat. ((p \<and> v < \<guillemotleft>n\<guillemotright>)\<^sup><)\<^sub>e) = (p\<^sup><)\<^sub>e"
  by (pred_auto)

text \<open> Total correctness law for Hoare logic, based on constructive chains. This is limited to
  variants that have naturals numbers as their range. \<close>
    
lemma while_term_hoare_r:
  assumes "\<And> z::nat. \<^bold>{p \<and> b \<and> v = \<guillemotleft>z\<guillemotright>\<^bold>}S\<^bold>{p \<and> v < \<guillemotleft>z\<guillemotright>\<^bold>}"
  shows "\<^bold>{p\<^bold>}while\<^sub>\<bottom> b do S od\<^bold>{\<not>b \<and> p\<^bold>}"
proof -
  have "((p\<^sup><)\<^sub>e \<longrightarrow> ((\<not> b \<and> p)\<^sup>>)\<^sub>e) \<sqsubseteq> (\<mu> X \<bullet> S ;; X \<lhd> b \<rhd> II)"
  proof (rule mu_refine_intro)
    from assms show "((p\<^sup><)\<^sub>e \<longrightarrow> ((\<not> b \<and> p)\<^sup>>)\<^sub>e) \<sqsubseteq> S ;; ((p\<^sup><)\<^sub>e \<longrightarrow> ((\<not> b \<and> p)\<^sup>>)\<^sub>e) \<lhd> b \<rhd> II"
      by pred_auto
    let ?E = "\<lambda> n. ((p \<and> v < \<guillemotleft>n\<guillemotright>)\<^sup><)\<^sub>e"
    show "((p\<^sup><)\<^sub>e \<and> (\<mu> X \<bullet> S ;; X \<lhd> b \<rhd> II)) = ((p\<^sup><)\<^sub>e \<and> (\<nu> X \<bullet> S ;; X \<lhd> b \<rhd> II))"
    proof (rule constr_fp_uniq[where E="?E"])
      show "mono (\<lambda>X. S ;; X \<lhd> b \<rhd> II)"
        by (rule cond_seqr_mono)
      from assms show "constr (\<lambda>X. S ;; X \<lhd> b \<rhd> II) ?E"
        apply (auto simp add: hoare_meaning intro!: constrI chainI)
          apply (pred_auto)
         apply (pred_auto)
        apply (pred_simp)
        apply (metis less_SucE order_less_trans)
        done
      show "(\<Sqinter>n::nat. ?E n) = (p\<^sup><)\<^sub>e"
        by pred_auto
    qed
  qed
  thus ?thesis
    by (simp add: while_bot_def hoare_r_def impl_pred_def, simp add: SEXP_def)
qed

text \<open> While loops with invariant and variant decoration -- total correctness \<close>

definition while_vrt :: "(bool, 's) expr \<Rightarrow> (bool, 's) expr \<Rightarrow> (nat, 's) expr \<Rightarrow> 's hrel \<Rightarrow> 's hrel"
  where "while_vrt b p v P = while_bot b P"

syntax
  "_while_vrt" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("while _ invr _ vrt _ do _ od")

translations
  "_while_vrt b I V P" == "CONST while_vrt (b)\<^sub>e (I)\<^sub>e (V)\<^sub>e P"

lemma while_vrt_hoare_r [hoare_safe]:
  assumes "\<And> z::nat. \<^bold>{p \<and> b \<and> v = \<guillemotleft>z\<guillemotright>\<^bold>}S\<^bold>{p \<and> v < \<guillemotleft>z\<guillemotright>\<^bold>}" "`p' \<longrightarrow> p`" "`(\<not>b \<and> p) \<longrightarrow> q'`"
  shows "\<^bold>{p'\<^bold>}while b invr p vrt v do S od\<^bold>{q'\<^bold>}"
  apply (rule hoare_r_conseq[OF _ assms(2) assms(3)])
  apply (simp add: while_vrt_def)
  apply (rule while_term_hoare_r[where v="v", OF assms(1)]) 
  done
  
text \<open> General total correctness law based on well-founded induction \<close>

lemma while_wf_hoare_r:
  assumes WF: "wf R"
  assumes I0: "`p' \<longrightarrow> p`"
  assumes induct_step:"\<And> st. \<^bold>{b \<and> p \<and> e = \<guillemotleft>st\<guillemotright>\<^bold>}Q\<^bold>{p \<and> (e, \<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright>\<^bold>}"
  assumes PHI:"`(\<not>b \<and> p) \<longrightarrow> q'`"  
  shows "\<^bold>{p'\<^bold>}while\<^sub>\<bottom> b invr p do Q od\<^bold>{q'\<^bold>}"
  unfolding hoare_r_def while_inv_bot_def while_bot_def
proof (rule pre_weak_rel[of _ "p\<^sup><" ], goal_cases)
  case 1
  from I0 show ?case by expr_auto
next
  case 2
  have "(p\<^sup>< \<longrightarrow> q'\<^sup>>)\<^sub>e \<sqsubseteq> (\<mu> X \<bullet> Q ;; X \<lhd> b \<rhd> II)"
  proof (rule mu_rec_total_utp_rule[where e=e, OF WF])
    show "mono (\<lambda>X. Q ;; X \<lhd> b \<rhd> II)"
      by (simp add: cond_seqr_mono)
    have induct_step': "\<Sqinter> st. ((b \<and> p \<and> e = \<guillemotleft>st\<guillemotright>)\<^sup>< \<longrightarrow> (p \<and> (e,\<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright>)\<^sup>>)\<^sub>e \<sqsubseteq> Q"
      using induct_step by pred_auto  
    with PHI
    show "\<And> st. (p\<^sup>< \<and> e\<^sup>< = \<guillemotleft>st\<guillemotright> \<longrightarrow> q'\<^sup>>)\<^sub>e \<sqsubseteq> Q ;; (p\<^sup>< \<and> (e\<^sup><, \<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright> \<longrightarrow> q'\<^sup>>)\<^sub>e \<lhd> b \<rhd> II"
      by (pred_auto, (metis (mono_tags, lifting) SEXP_apply hoare_rel_r_def induct_step)+)
  qed
  then show ?case by simp
qed

lemma while_thoare_r [hoare_safe]:
  fixes V :: "'s \<Rightarrow> 'a::wellorder"
  assumes "\<And> z. H[P \<and> B \<and> V = \<guillemotleft>z\<guillemotright>] S [P \<and> V < \<guillemotleft>z\<guillemotright>]"
  shows "H[P] while B do S od [\<not> B \<and> P]"
proof -
  from assms have "\<^bold>{P \<and> B\<^bold>} S \<^bold>{P\<^bold>}"
    by (auto simp add: hoare_rel_r_def thoare_rel_r_alt_def)
  hence partial: "\<^bold>{P\<^bold>} while B do S od \<^bold>{\<not> B \<and> P\<^bold>}"
    using while_hoare_r by blast
  from assms have S_term: "`B \<and> P \<longrightarrow> pre S`"
    by (simp add: pre_def thoare_rel_r_def)
  have wS_term: "`P \<longrightarrow> (while B do S od) wp True`"
  proof (rule tautI, simp, rule impI)
    fix s
    assume P: "P s"
    show "(while B do S od wp True) s"
    proof (cases "B s")
      case False
      then show ?thesis
        by (force simp add: wp_while)
    next
      case True
      with P have "\<exists> xs. xs \<noteq> [] \<and> (\<forall> i<length xs. B ((s # xs) ! i) \<and> S ((s # xs) ! i, xs ! i)) \<and> \<not> B(last xs) \<and> P (last xs)"
      proof (induct "V(s)" arbitrary: s rule: less_induct)
        case less
        with assms(1) obtain s' where s': "S (s, s')" "P s'" "V s' < V s"
          by (force simp add: pred)
        show ?case
        proof (cases "B s'")
          case False
          then show ?thesis
            by (metis add.right_neutral add_Suc_right last_single_element less.prems(2) less_Suc0 list.size(3,4) not_Cons_self2 nth_Cons_0 s'(1,2))
        next
          case True
          obtain xs where xs:"xs \<noteq> []" "\<forall> i<length xs. B ((s' # xs) ! i) \<and> S ((s' # xs) ! i, xs ! i)" "\<not> B(last xs)" "P (last xs)"
            using True less.hyps s'(2,3) by blast
          show ?thesis 
          proof
            show "\<not> (s' # xs) = [] \<and> (\<forall>i. i < length (s' # xs) \<longrightarrow> B ((s # s' # xs) ! i) \<and> S ((s # s' # xs) ! i, (s' # xs) ! i)) \<and> \<not> B (last (s' # xs)) \<and> P (last (s' # xs))"
              using less.prems(2) less_Suc_eq_0_disj s'(1) xs(1,2,3,4) by force
          qed
        qed
      qed

      then show ?thesis
        by (auto simp add: wp_while)
    qed
  qed
  show ?thesis
    using partial thoare_rel_r_alt_def wS_term by blast
qed

subsection \<open> Verification Condition Generation \<close>

method vcg =  (auto intro!: hoare_safe; expr_taut; auto)

end