theory utp_hoare
imports utp_rel_laws
begin

text \<open>Hoare triples\<close>

definition hoare_r :: "('s \<Rightarrow> bool) \<Rightarrow> 's hrel \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
[pred]: "hoare_r p Q r = ((p\<^sup>< \<longrightarrow> r\<^sup>>)\<^sub>e \<sqsubseteq> Q)"

syntax 
  "_hoare_r" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>{_\<^bold>}/ _/ \<^bold>{_\<^bold>}")
  "_hoare_r" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("H{_}/ _/ {_}")

translations "_hoare_r P S Q" == "CONST hoare_r (P)\<^sub>e S (Q)\<^sub>e"


named_theorems hoare and hoare_safe

lemma hoare_meaning: "H{p}Q{r} = (\<forall> s s'. p s \<squnion> Q (s, s') \<longrightarrow> r s')"
  by (pred_auto)

lemma hoare_alt_def: "\<^bold>{b\<^bold>}P\<^bold>{c\<^bold>} = (P ;; \<questiondown>c? \<sqsubseteq> \<questiondown>b? ;; P)"
  by (pred_auto)

lemma hoare_assume: "\<^bold>{P\<^bold>}S\<^bold>{Q\<^bold>} \<Longrightarrow> \<questiondown>P? ;; S = \<questiondown>P? ;; S ;; \<questiondown>Q?"
  by (pred_auto)

lemma hoare_pre_assume_1: "\<^bold>{b \<squnion> c\<^bold>}P\<^bold>{d\<^bold>} = \<^bold>{c\<^bold>}\<questiondown>b? ;; P\<^bold>{d\<^bold>}"
  by (pred_auto)

lemma hoare_pre_assume_2: "\<^bold>{b \<squnion> c\<^bold>}P\<^bold>{d\<^bold>} = \<^bold>{b\<^bold>}\<questiondown>c? ;; P\<^bold>{d\<^bold>}"
  by pred_auto
                               
lemma hoare_test [hoare_safe]: "`p \<squnion> b \<longrightarrow> q` \<Longrightarrow> \<^bold>{p\<^bold>}\<questiondown>b?\<^bold>{q\<^bold>}"
  by pred_auto

lemma hoare_gcmd [hoare_safe]: "\<^bold>{p \<squnion> b\<^bold>}P\<^bold>{q\<^bold>} \<Longrightarrow> \<^bold>{p\<^bold>}\<questiondown>b? ;; P\<^bold>{q\<^bold>}"
  by pred_auto

lemma hoare_r_conj [hoare_safe]: "\<lbrakk> \<^bold>{p\<^bold>}Q\<^bold>{r\<^bold>}; \<^bold>{p\<^bold>}Q\<^bold>{s\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}Q\<^bold>{r \<squnion> s\<^bold>}"
  by pred_auto

lemma hoare_r_weaken_pre [hoare]:
  "\<^bold>{p\<^bold>}Q\<^bold>{r\<^bold>} \<Longrightarrow> \<^bold>{p \<squnion> q\<^bold>}Q\<^bold>{r\<^bold>}"
  "\<^bold>{q\<^bold>}Q\<^bold>{r\<^bold>} \<Longrightarrow> \<^bold>{p \<squnion> q\<^bold>}Q\<^bold>{r\<^bold>}"
  by pred_auto+

lemma pre_str_hoare_r:
  assumes "`p\<^sub>1 \<longrightarrow> p\<^sub>2`" and "\<^bold>{p\<^sub>2\<^bold>}C\<^bold>{q\<^bold>}"
  shows "\<^bold>{p\<^sub>1\<^bold>}C\<^bold>{q\<^bold>}"
  using assms by pred_auto
    
lemma post_weak_hoare_r:
  assumes "\<^bold>{p\<^bold>}C\<^bold>{q\<^sub>2\<^bold>}" and "`q\<^sub>2 \<longrightarrow> q\<^sub>1`"
  shows "\<^bold>{p\<^bold>}C\<^bold>{q\<^sub>1\<^bold>}" 
  using assms by pred_auto

lemma hoare_r_conseq: "\<lbrakk> \<^bold>{p\<^sub>2\<^bold>}S\<^bold>{q\<^sub>2\<^bold>}; `p\<^sub>1 \<longrightarrow> p\<^sub>2`; `q\<^sub>2 \<longrightarrow> q\<^sub>1` \<rbrakk> \<Longrightarrow> \<^bold>{p\<^sub>1\<^bold>}S\<^bold>{q\<^sub>1\<^bold>}"
  by pred_auto

lemma hoare_r_cut:
  assumes "\<^bold>{b\<^bold>}P\<^bold>{b\<^bold>}" "\<^bold>{b \<squnion> c\<^bold>}P\<^bold>{c\<^bold>}"
  shows "\<^bold>{b \<squnion> c\<^bold>}P\<^bold>{b \<squnion> c\<^bold>}"
  using assms by pred_auto

lemma hoare_r_cut_simple: 
  assumes "\<^bold>{b\<^bold>}P\<^bold>{b\<^bold>}" "\<^bold>{c\<^bold>}P\<^bold>{c\<^bold>}"
  shows "\<^bold>{b \<squnion> c\<^bold>}P\<^bold>{b \<squnion> c\<^bold>}"
  using assms by pred_auto

lemma hoare_oracle: "\<^bold>{p\<^bold>}false\<^bold>{q\<^bold>}"
  by (simp add: hoare_r_def)

subsection \<open> Sequence Laws \<close>

lemma seq_hoare_r: "\<lbrakk> \<^bold>{p\<^bold>}Q\<^sub>1\<^bold>{s\<^bold>} ; \<^bold>{s\<^bold>}Q\<^sub>2\<^bold>{r\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{r\<^bold>}"
  by (rel_force)
 
lemma seq_hoare_invariant [hoare_safe]: "\<lbrakk> \<^bold>{p\<^bold>}Q\<^sub>1\<^bold>{p\<^bold>} ; \<^bold>{p\<^bold>}Q\<^sub>2\<^bold>{p\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{p\<^bold>}"
  by (rel_force)

lemma seq_hoare_stronger_pre_1 [hoare_safe]: 
  "\<lbrakk> \<^bold>{p \<squnion> q\<^bold>}Q\<^sub>1\<^bold>{p \<squnion> q\<^bold>} ; \<^bold>{p \<squnion> q\<^bold>}Q\<^sub>2\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p \<squnion> q\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{q\<^bold>}"
  using seq_hoare_r by blast

lemma seq_hoare_stronger_pre_2 [hoare_safe]: 
  "\<lbrakk> \<^bold>{p \<squnion> q\<^bold>}Q\<^sub>1\<^bold>{p \<squnion> q\<^bold>} ; \<^bold>{p \<squnion> q\<^bold>}Q\<^sub>2\<^bold>{p\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p \<squnion> q\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{p\<^bold>}"
  using seq_hoare_r by blast
    
lemma seq_hoare_inv_r_2 [hoare]: "\<lbrakk> \<^bold>{p\<^bold>}Q\<^sub>1\<^bold>{q\<^bold>} ; \<^bold>{q\<^bold>}Q\<^sub>2\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{q\<^bold>}"
  using seq_hoare_r by blast

lemma seq_hoare_inv_r_3 [hoare]: "\<lbrakk> \<^bold>{p\<^bold>}Q\<^sub>1\<^bold>{p\<^bold>} ; \<^bold>{p\<^bold>}Q\<^sub>2\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}Q\<^sub>1 ;; Q\<^sub>2\<^bold>{q\<^bold>}"
  using seq_hoare_r by blast

subsection \<open> Assignment Laws \<close>

lemma assigns_hoare_r [hoare_safe]: "`p \<longrightarrow> \<sigma> \<dagger> q` \<Longrightarrow> \<^bold>{p\<^bold>}\<langle>\<sigma>\<rangle>\<^sub>a\<^bold>{q\<^bold>}"
  by pred_auto
  
lemma assigns_backward_hoare_r: 
  "\<^bold>{\<sigma> \<dagger> p\<^bold>}\<langle>\<sigma>\<rangle>\<^sub>a\<^bold>{p\<^bold>}"
  by pred_auto

lemma assign_floyd_hoare_r:
  assumes "vwb_lens x"
  shows "\<^bold>{p\<^bold>} x := e \<^bold>{\<exists> v . p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<squnion> $x = e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>\<^bold>}"
  using assms
  by (pred_auto, metis lens_override_def lens_override_idem)

lemma assigns_init_hoare [hoare_safe]:
  "\<lbrakk> vwb_lens x; $x \<sharp> p; $x \<sharp> v; \<^bold>{$x = v \<squnion> p\<^bold>}S\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}(x := v) ;; S\<^bold>{q\<^bold>}"
  by pred_auto

lemma assigns_init_hoare_general:
  "\<lbrakk> vwb_lens x; \<Sqinter> x\<^sub>0. \<^bold>{$x = v\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk> \<squnion> p\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/x\<rbrakk>\<^bold>}S\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}x := v ;; S\<^bold>{q\<^bold>}"
  by (rule seq_hoare_r, rule assign_floyd_hoare_r, simp, pred_auto)

lemma assigns_final_hoare [hoare_safe]:
  "\<^bold>{p\<^bold>}S\<^bold>{\<sigma> \<dagger> q\<^bold>} \<Longrightarrow> \<^bold>{p\<^bold>}S ;; \<langle>\<sigma>\<rangle>\<^sub>a\<^bold>{q\<^bold>}"
  by (pred_auto)

lemma skip_hoare_r [hoare_safe]: "\<^bold>{p\<^bold>}II\<^bold>{p\<^bold>}"
  by pred_auto

lemma skip_hoare_impl_r [hoare_safe]: "`p \<longrightarrow> q` \<Longrightarrow> \<^bold>{p\<^bold>}II\<^bold>{q\<^bold>}"
  by pred_auto  

subsection \<open> Conditional Laws \<close>

lemma cond_hoare_r [hoare_safe]: "\<lbrakk> \<^bold>{b \<squnion> p\<^bold>}S\<^bold>{q\<^bold>} ; \<^bold>{\<not>b \<squnion> p\<^bold>}T\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}S \<^bold>\<lhd> b \<^bold>\<rhd> T\<^bold>{q\<^bold>}"
  unfolding cond_def by rel_simp pred_auto

lemma cond_hoare_r_wp: 
  assumes "\<^bold>{p'\<^bold>}S\<^bold>{q\<^bold>}" and "\<^bold>{p''\<^bold>}T\<^bold>{q\<^bold>}"
  shows "\<^bold>{(b \<squnion> p') \<sqinter> (\<not>b \<squnion> p'')\<^bold>} S \<^bold>\<lhd> b \<^bold>\<rhd> T \<^bold>{q\<^bold>}"
  using assms unfolding cond_def by rel_simp pred_auto

lemma cond_hoare_r_sp:
  assumes "\<^bold>{(b \<squnion> p)\<^bold>}S\<^bold>{q\<^bold>}" and "\<^bold>{\<not>b \<squnion> p\<^bold>}T\<^bold>{s\<^bold>}"
  shows "\<^bold>{p\<^bold>}S \<^bold>\<lhd> b \<^bold>\<rhd> T\<^bold>{q \<sqinter> s\<^bold>}"
  using assms unfolding cond_def by rel_simp pred_auto

lemma hoare_ndet [hoare_safe]: 
  assumes "\<^bold>{p\<^bold>}P\<^bold>{q\<^bold>}" "\<^bold>{p\<^bold>}Q\<^bold>{q\<^bold>}"
  shows "\<^bold>{p\<^bold>}(P \<sqinter> Q)\<^bold>{q\<^bold>}"
  using assms by (pred_auto)

lemma hoare_disj [hoare_safe]: 
  assumes "\<^bold>{p\<^bold>}P\<^bold>{q\<^bold>}" "\<^bold>{p\<^bold>}Q\<^bold>{q\<^bold>}"
  shows "\<^bold>{p\<^bold>}(P \<sqinter> Q)\<^bold>{q\<^bold>}"
  using assms by (pred_auto)

lemma hoare_UINF [hoare_safe]:
  assumes "\<Sqinter>i. i \<in> A \<Longrightarrow> \<^bold>{p\<^bold>}P(i)\<^bold>{q\<^bold>}"
  shows "\<^bold>{p\<^bold>}(\<Sqinter> {P(i)|i. i\<in>A})\<^bold>{q\<^bold>}"
  using assms by (pred_auto, meson hoare_meaning)


subsection \<open> Recursion Laws \<close>

lemma nu_hoare_r_partial: 
  assumes induct_step: "\<Sqinter>P st. \<^bold>{p\<^bold>}P\<^bold>{q\<^bold>} \<Longrightarrow> \<^bold>{p\<^bold>}F P\<^bold>{q\<^bold>}"   
  shows "\<^bold>{p\<^bold>}\<nu> F\<^bold>{q\<^bold>}"
  using induct_step by (pred_auto add: lfp_lowerbound)

lemma mu_hoare_r:
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<Sqinter> st P. \<^bold>{p \<squnion> (e,\<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright>\<^bold>}P\<^bold>{q\<^bold>} \<Longrightarrow> \<^bold>{p \<squnion> e = \<guillemotleft>st\<guillemotright>\<^bold>}F P\<^bold>{q\<^bold>}"   
  shows "\<^bold>{p\<^bold>}\<mu> F \<^bold>{q\<^bold>}"
  unfolding hoare_r_def
proof (rule mu_rec_total_utp_rule[OF WF M , of _ e ], goal_cases)
  case (1 st)
  then show ?case 
    using induct_step[unfolded hoare_r_def, of st "(p\<^sup>< \<squnion> (e\<^sup><, \<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright> \<longrightarrow> q\<^sup>>)\<^sub>u"]
      by (simp add: usubst)
qed
    \<Sqinter>
lemma mu_hoare_r':
  assumes WF: "wf R"
  assumes M:"mono F"  
  assumes induct_step:
    "\<Sqinter> st P. \<^bold>{p \<squnion> (e,\<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright>\<^bold>} P \<^bold>{q\<^bold>} \<Longrightarrow> \<^bold>{p \<squnion> e = \<guillemotleft>st\<guillemotright>\<^bold>} F P \<^bold>{q\<^bold>}" 
  assumes I0: "`p' \<longrightarrow> p`"  
  shows "\<^bold>{p'\<^bold>} \<mu> F \<^bold>{q\<^bold>}"
  using I0 M WF assms(3) mu_hoare_r pre_str_hoare_r by blast

subsection \<open> Iteration Rules \<close>

lemma iter_hoare_r [hoare_safe]: "\<^bold>{P\<^bold>}S\<^bold>{P\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>}S\<^sup>\<star>\<^bold>{P\<^bold>}"
   using rtrancl_induct by (pred_auto, fastforce)

lemma while_hoare_r [hoare_safe]:
  assumes "\<^bold>{p \<squnion> b\<^bold>}S\<^bold>{p\<^bold>}"
  shows "\<^bold>{p\<^bold>}while b do S od\<^bold>{\<not>b \<squnion> p\<^bold>}"
proof (simp add: while_top_def hoare_r_def assms)
  have "(p\<^sup>< \<longrightarrow> (\<not> b \<squnion> p)\<^sup>>)\<^sub>u \<sqsubseteq> S ;; (p\<^sup>< \<longrightarrow> (\<not> b \<squnion> p)\<^sup>>)\<^sub>u \<^bold>\<lhd> b \<^bold>\<rhd> II"
    using assms by pred_auto
  then show "(p\<^sup>< \<longrightarrow> (\<not> b \<squnion> p)\<^sup>>)\<^sub>u \<sqsubseteq> (\<nu> X \<bullet> S ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: lfp_lowerbound ref_by_set_def)
qed

lemma while_invr_hoare_r [hoare_safe]:
  assumes "\<^bold>{p \<squnion> b\<^bold>}S\<^bold>{p\<^bold>}" "`pre' \<longrightarrow> p`" "`(\<not>b \<squnion> p) \<longrightarrow> post'`"
  shows "\<^bold>{pre'\<^bold>}while b invr p do S od\<^bold>{post'\<^bold>}"
  unfolding while_inv_def using assms while_hoare_r hoare_r_conseq by blast

lemma while_r_minimal_partial:
  assumes seq_step: "`p \<longrightarrow> invar`"
  assumes induct_step: "\<^bold>{invar \<squnion> b\<^bold>} C \<^bold>{invar\<^bold>}"  
  shows "\<^bold>{p\<^bold>}while b do C od\<^bold>{\<not>b \<squnion> invar\<^bold>}"
  using induct_step pre_str_hoare_r seq_step while_hoare_r by blast

(*lemma approx_chain: 
  "(\<Sqinter>n::nat. \<lceil>p \<squnion> v <\<^sub>u \<guillemotleft>n\<guillemotright>\<rceil>\<^sub><) = \<lceil>p\<rceil>\<^sub><"
  by (pred_auto)*)

text \<open> Total correctness law for Hoare logic, based on constructive chains. This is limited to
  variants that have naturals numbers as their range. \<close>
    
lemma while_term_hoare_r:
  assumes "\<Sqinter> z::nat. \<^bold>{p \<squnion> b \<squnion> v = \<guillemotleft>z\<guillemotright>\<^bold>}S\<^bold>{p \<squnion> v < \<guillemotleft>z\<guillemotright>\<^bold>}"
  shows "\<^bold>{p\<^bold>}while\<^sub>\<bottom> b do S od\<^bold>{\<not>b \<squnion> p\<^bold>}"
proof -
  have "((p\<^sup><)\<^sub>u \<Rightarrow> ((\<not> b \<squnion> p)\<^sup>>)\<^sub>u) \<sqsubseteq> (\<mu> X \<bullet> S ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II)"
  proof (rule mu_refine_intro)
    from assms show "((p\<^sup><)\<^sub>u \<Rightarrow> ((\<not> b \<squnion> p)\<^sup>>)\<^sub>u) \<sqsubseteq> S ;; ((p\<^sup><)\<^sub>u \<Rightarrow> ((\<not> b \<squnion> p)\<^sup>>)\<^sub>u) \<^bold>\<lhd> b \<^bold>\<rhd> II"
      by (pred_auto; smt (z3) hoare_meaning)+
    let ?E = "\<lambda> n. \<lbrakk>(p \<squnion> v < \<guillemotleft>n\<guillemotright>)\<^sup><\<rbrakk>\<^sub>u"
    show "((p\<^sup><)\<^sub>u \<squnion> (\<mu> X \<bullet> S ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II)) = ((p\<^sup><)\<^sub>u \<squnion> (\<nu> X \<bullet> S ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II))"
    proof (rule constr_fp_uniq[where E="?E"])
      show "mono (\<lambda>X. S ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II)"
        by (rule cond_seqr_mono)
      show "constr (\<lambda>X. S ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II) ?E"
        apply (rule constrI, rule chainI)
          apply (pred_auto)+
        by (smt (verit, del_insts) assms hoare_meaning less_Suc_eq order_less_trans)+
    qed pred_auto (* Couldn't pattern match last goal *)
  qed
  thus ?thesis
    by (pred_auto add: while_bot_def)
qed

lemma while_vrt_hoare_r [hoare_safe]:
  assumes "\<Sqinter> z::nat. \<^bold>{p \<squnion> b \<squnion> v = \<guillemotleft>z\<guillemotright>\<^bold>}S\<^bold>{p \<squnion> v < \<guillemotleft>z\<guillemotright>\<^bold>}" "`p' \<longrightarrow> p`" "`(\<not>b \<squnion> p) \<longrightarrow> q'`"
  shows "\<^bold>{p'\<^bold>}while b invr p vrt v do S od\<^bold>{q'\<^bold>}"
  apply (rule hoare_r_conseq[OF _ assms(2) assms(3)])
  apply (simp add: while_vrt_def)
  apply (rule while_term_hoare_r[where v="v", OF assms(1)]) 
  done
  
text \<open> General total correctness law based on well-founded induction \<close>

lemma while_wf_hoare_r:
  assumes WF: "wf R"
  assumes I0: "`p' \<longrightarrow> p`"
  assumes induct_step:"\<Sqinter> st. \<^bold>{b \<squnion> p \<squnion> e = \<guillemotleft>st\<guillemotright>\<^bold>}Q\<^bold>{p \<squnion> (e, \<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright>\<^bold>}"
  assumes PHI:"`(\<not>b \<squnion> p) \<longrightarrow> q'`"  
  shows "\<^bold>{p'\<^bold>}while\<^sub>\<bottom> b invr p do Q od\<^bold>{q'\<^bold>}"
  unfolding hoare_r_def while_inv_bot_def while_bot_def
proof (rule pre_weak_rel[of _ "p\<^sup><" ], goal_cases)
  case 1
  from I0 show ?case by expr_auto
next
  case 2
  have "(p\<^sup>< \<longrightarrow> q'\<^sup>>)\<^sub>u \<sqsubseteq> (\<mu> X \<bullet> Q ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II)"
  proof (rule mu_rec_total_utp_rule[where e=e, OF WF])
    show "mono (\<lambda>X. Q ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II)"
      by (simp add: cond_seqr_mono)
    have induct_step': "\<Sqinter> st. ((b \<squnion> p \<squnion> e = \<guillemotleft>st\<guillemotright>)\<^sup>< \<longrightarrow> (p \<squnion> (e,\<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright>)\<^sup>>)\<^sub>u \<sqsubseteq> Q"
      using induct_step by pred_auto  
    with PHI
    show "\<Sqinter>st. (p\<^sup>< \<squnion> e\<^sup>< = \<guillemotleft>st\<guillemotright> \<longrightarrow> q'\<^sup>>)\<^sub>u \<sqsubseteq> Q ;; (p\<^sup>< \<squnion> (e\<^sup><, \<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright> \<longrightarrow> q'\<^sup>>)\<^sub>u \<^bold>\<lhd> b \<^bold>\<rhd> II"
      apply pred_auto
      by (smt (z3) hoare_meaning induct_step)+
  qed
  then show ?case by simp
qed


subsection \<open> Frame Rules \<close>

text \<open> Frame rule: If starting $S$ in a state satisfying $p establishes q$ in the final state, then
  we can insert an invariant predicate $r$ when $S$ is framed by $a$, provided that $r$ does not
  refer to variables in the frame, and $q$ does not refer to variables outside the frame. \<close>

(* TODO - Fix all these metis proofs *)

lemma frame_hoare_r:
  assumes "idem_scene a" "a \<sharp> r" "-a \<sharp> q" "\<^bold>{p\<^bold>}P\<^bold>{q\<^bold>}"
  shows "\<^bold>{p \<squnion> r\<^bold>}a:[P]\<^bold>{q \<squnion> r\<^bold>}"
  using assms
  apply (pred_auto)
   apply (metis (mono_tags, lifting) Product_Type.Collect_case_prodD frame_def fst_conv hoare_meaning snd_conv)
  by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD frame_def fst_eqD scene_equiv_def scene_override_commute snd_eqD)

lemma frame_strong_hoare_r [hoare_safe]: 
  assumes "idem_scene a" "a \<sharp> r" "-a \<sharp> q" "\<^bold>{p \<squnion> r\<^bold>}S\<^bold>{q\<^bold>}"
  shows "\<^bold>{p \<squnion> r\<^bold>}a:[S]\<^bold>{q \<squnion> r\<^bold>}"
  using assms apply (pred_auto)
   apply (metis (mono_tags, lifting) SEXP_def hoare_meaning rel_frame set_pred_def)
  by (metis SEXP_def rel_frame scene_equiv_def scene_override_commute set_pred_def)

lemma frame_hoare_r' [hoare_safe]: 
  assumes "idem_scene a" "a \<sharp> r" "-a \<sharp> q" "\<^bold>{r \<squnion> p\<^bold>}S\<^bold>{q\<^bold>}"
  shows "\<^bold>{r \<squnion> p\<^bold>}a:[S]\<^bold>{r \<squnion> q\<^bold>}"
  using assms apply (pred_auto)
   apply (metis SEXP_def rel_frame scene_equiv_def scene_override_commute set_pred_def)
  by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD frame_def fst_conv hoare_meaning snd_conv)

lemma antiframe_hoare_r:
  assumes "idem_scene a" "-a \<sharp> r" "a \<sharp> q" "\<^bold>{p\<^bold>}P\<^bold>{q\<^bold>}"  
  shows "\<^bold>{p \<squnion> r\<^bold>} (-a):[P] \<^bold>{q \<squnion> r\<^bold>}"
  using assms apply (pred_auto)
   apply (metis (mono_tags, lifting) Product_Type.Collect_case_prodD frame_def fst_conv hoare_meaning snd_conv)
  by (metis (full_types) SEXP_def rel_frame scene_equiv_def scene_override_commute set_pred_def)
    
lemma antiframe_strong_hoare_r:
  assumes "idem_scene a" "-a \<sharp> r" "a \<sharp> q" "\<^bold>{p \<squnion> r\<^bold>}P\<^bold>{q\<^bold>}"  
  shows "\<^bold>{p \<squnion> r\<^bold>} (-a):[P] \<^bold>{q \<squnion> r\<^bold>}"
  using assms  apply (pred_auto)
   apply (metis (mono_tags, lifting) Product_Type.Collect_case_prodD frame_def fst_conv hoare_meaning snd_conv)
  by (metis (full_types) SEXP_def rel_frame scene_equiv_def scene_override_commute set_pred_def)


lemma nmods_invariant:
  assumes "S nmods a" "-a \<sharp> p"
  shows "\<^bold>{p\<^bold>}S\<^bold>{p\<^bold>}"
  using assms apply pred_auto
  by (metis Healthy_def SEXP_def rel_frame scene_equiv_def scene_override_commute set_pred_def)

(*
lemma hoare_r_ghost:
  assumes "vwb_lens x" "x \<sharp> p" "x \<sharp> q" "S nuses x" "\<^bold>{p\<^bold>}x := e;; S\<^bold>{q\<^bold>}"
  shows "\<^bold>{p\<^bold>}S\<^bold>{q\<^bold>}" 
proof -
  have "\<^bold>{p\<^bold>}x := e;; rrestr x S\<^bold>{q\<^bold>}"
    by (simp add: Healthy_if assms(4) assms(5))
  with assms(1-3) have "\<^bold>{p\<^bold>}rrestr x S\<^bold>{q\<^bold>}"
    by (rel_simp,metis mwb_lens.put_put vwb_lens_mwb)
  thus ?thesis
    by (simp add: Healthy_if assms(4))
qed *)

end