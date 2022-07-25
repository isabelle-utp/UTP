section \<open> Fixed-points and Recursion \<close>

theory utp_recursion
  imports utp_pred_laws
begin

subsection \<open> Syntax \<close>

syntax
  "_utp_mu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu> _ \<bullet> _" [0, 10] 10)
  "_utp_nu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu> _ \<bullet> _" [0, 10] 10)

notation lfp ("\<nu>")
notation gfp ("\<mu>")

translations
  "\<nu> X \<bullet> P" == "CONST lfp (\<lambda> X. P)"
  "\<mu> X \<bullet> P" == "CONST gfp (\<lambda> X. P)"

text \<open> The mu and nu operators correspond to the greatest and least fixed-points of the refinement lattice. \<close>

lemma lfp_is_ref_gfp: "lfp = ref_lattice.gfp"
  by (simp add: lfp_def ref_lattice.gfp_def fun_eq_iff pred_ref_iff_le)

lemma gfp_is_ref_lfp: "gfp = ref_lattice.lfp"
  by (simp add: gfp_def ref_lattice.lfp_def fun_eq_iff pred_ref_iff_le)

subsection \<open> Fixed-point Laws \<close>
  
lemma mu_id: "(\<mu> X \<bullet> X) = true"
  by (simp add: gfp_eqI mono_def predicate1I true_pred_def)

lemma mu_const: "(\<mu> X \<bullet> P) = P"
  by (simp add: gfp_const)

lemma nu_id: "(\<nu> X \<bullet> X) = false"
  by (simp add: SEXP_def antisym false_pred_def lfp_lowerbound predicate1I)

lemma nu_const: "(\<nu> X \<bullet> P) = P"
  by (simp add: lfp_const)

lemma mu_refine_intro:
  fixes C :: "'s pred"
  assumes "(C \<longrightarrow> S) \<sqsubseteq> F(C \<longrightarrow> S)" "(C \<and> \<mu> F) = (C \<and> \<nu> F)"
  shows "(C \<longrightarrow> S) \<sqsubseteq> \<mu> F"
proof -
  from assms have "(C \<longrightarrow> S) \<sqsubseteq> \<nu> F"
    using lfp_lowerbound by (auto simp add: pred_ref_iff_le)
  with assms show ?thesis
    by (pred_auto)
qed

subsection \<open> Obtaining Unique Fixed-points \<close>
    
text \<open> Obtaining termination proofs via approximation chains. Theorems and proofs adapted
  from Chapter 2, page 63 of the UTP book~\cite{Hoare&98}.  \<close>

type_synonym 'a chain = "nat \<Rightarrow> 'a pred"

definition chain :: "'a chain \<Rightarrow> bool" where
  "chain Y = ((Y 0 = false) \<and> (\<forall> i. Y (Suc i) \<sqsubseteq> Y i))"

lemma chain0 [simp]: "chain Y \<Longrightarrow> Y 0 = false"
  by (simp add:chain_def)

lemma chainI:
  assumes "Y 0 = false" "\<And> i. Y (Suc i) \<sqsubseteq> Y i"
  shows "chain Y"
  using assms by (auto simp add: chain_def)

lemma chainE:
  assumes "chain Y" "\<And> i. \<lbrakk> Y 0 = false; Y (Suc i) \<sqsubseteq> Y i \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: chain_def)

lemma L274:
  fixes X :: "'s pred"
  assumes "\<forall> n. ((E n \<and> X) = (E n \<and> Y))"
  shows "(\<Sqinter> (range E) \<and> X) = (\<Sqinter> (range E) \<and> Y)"
  using assms by (pred_auto)

text \<open> Constructive chains \<close>

definition constr ::
  "('a pred \<Rightarrow> 'a pred) \<Rightarrow> 'a chain \<Rightarrow> bool" where
"constr F E \<longleftrightarrow> chain E \<and> (\<forall> X n. ((F(X) \<and> E(n + 1)) = (F(X \<and> E(n)) \<and> E (n + 1))))"

lemma constrI:
  assumes "chain E" "\<And> X n. ((F(X) \<and> E(n + 1)) = (F(X \<and> E(n)) \<and> E (n + 1)))"
  shows "constr F E"
  using assms by (auto simp add: constr_def)

text \<open> This lemma gives a way of showing that there is a unique fixed-point when
        the predicate function can be built using a constructive function F
        over an approximation chain E \<close>

lemma chain_pred_terminates:
  assumes "constr F E" "mono F"
  shows "(\<Sqinter> (range E) \<and> \<mu> F) = (\<Sqinter> (range E) \<and> \<nu> F)"
proof -
  from assms have "\<forall> n. (E n \<and> \<mu> F) = (E n \<and> \<nu> F)"
  proof (rule_tac allI)
    fix n
    from assms show "(E n \<and> \<mu> F) = (E n \<and> \<nu> F)"
    proof (induct n)
      case 0 thus ?case by (simp add: constr_def)
    next
      case (Suc n)
      note hyp = this
      thus ?case
      proof -
        have "(E (n + 1) \<and> \<mu> F) = (E (n + 1) \<and> F (\<mu> F))"
          using gfp_unfold[OF hyp(3), THEN sym] by (simp add: constr_def)
        also from hyp have "... = (E (n + 1) \<and> F (E n \<and> \<mu> F))"
          by (metis constr_def pred_ba.inf.commute)
        also from hyp have "... = (E (n + 1) \<and> F (E n \<and> \<nu> F))"
          by simp
        also from hyp have "... = (E (n + 1) \<and> \<nu> F)"
          by (metis (no_types, lifting) constr_def lfp_fixpoint pred_ba.inf_commute)
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
  thus ?thesis
    using L274 by blast
qed

theorem constr_fp_uniq:
  assumes "constr F E" "mono F" "\<Sqinter> (range E) = C"
  shows "(C \<and> \<mu> F) = (C \<and> \<nu> F)"
  using assms chain_pred_terminates by blast
    
subsection \<open> Noetherian Induction Instantiation\<close>
      
text \<open> Contribution from Yakoub Nemouchi.The following generalization was used by Tobias Nipkow
        and Peter Lammich  in \emph{Refine\_Monadic} \<close>

lemma  wf_fixp_uinduct_pure_ueq_gen:     
  assumes fixp_unfold: "fp B = B (fp B)"
  and              WF: "wf R"
  and     induct_step:
          "\<And>f st. \<lbrakk>\<And>st'. (st',st) \<in> R  \<Longrightarrow> (((p \<and> e\<^sup>< = \<guillemotleft>st'\<guillemotright>) \<longrightarrow> q)\<^sub>e \<sqsubseteq> f)\<rbrakk>
               \<Longrightarrow> fp B = f \<Longrightarrow>((p \<and> e\<^sup>< = \<guillemotleft>st\<guillemotright>) \<longrightarrow> q)\<^sub>e \<sqsubseteq> (B f)"
        shows "((p \<longrightarrow> q)\<^sub>e \<sqsubseteq> fp B)"  
proof -  
  { fix st
    have "((p \<and> e\<^sup>< = \<guillemotleft>st\<guillemotright>) \<longrightarrow> q)\<^sub>e \<sqsubseteq> (fp B)" 
    using WF proof (induction rule: wf_induct_rule)
      case (less x)
      hence "(p \<and> e\<^sup>< = \<guillemotleft>x\<guillemotright> \<longrightarrow> q)\<^sub>e \<sqsubseteq> B (fp B)"
        by (rule induct_step, auto)
      then show ?case
        using fixp_unfold by metis
    qed
  }
  thus ?thesis
    by (simp add: pred_refine_iff) 
qed
  
text \<open> The next lemma shows that using substitution also work. However it is not that generic
        nor practical for proof automation ... \<close>

lemma refine_usubst_to_ueq:
  "vwb_lens E \<Longrightarrow> (p \<longrightarrow> q)\<^sub>e\<lbrakk>\<guillemotleft>st'\<guillemotright>/E\<rbrakk> \<sqsubseteq> f\<lbrakk>\<guillemotleft>st'\<guillemotright>/E\<rbrakk> = (((p \<and> $E = \<guillemotleft>st'\<guillemotright>) \<longrightarrow> q)\<^sub>e \<sqsubseteq> f)"
  oops

text \<open> By instantiation of @{thm wf_fixp_uinduct_pure_ueq_gen} with @{term \<mu>} and lifting of the 
        well-founded relation we have ... \<close>

lemma mu_rec_total_pure_rule: 
  assumes WF: "wf R"
  and     M: "mono B"  
  and     induct_step:
          "\<And> f st.  \<lbrakk>(p \<and> (e\<^sup><,\<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright> \<longrightarrow> q)\<^sub>e \<sqsubseteq> f\<rbrakk>
               \<Longrightarrow> \<mu> B = f \<Longrightarrow> (p \<and> e\<^sup>< = \<guillemotleft>st\<guillemotright> \<longrightarrow> q)\<^sub>e \<sqsubseteq> (B f)"
        shows "(p \<longrightarrow> q)\<^sub>e \<sqsubseteq> \<mu> B"  
proof (rule wf_fixp_uinduct_pure_ueq_gen[where fp=\<mu> and p=p and B=B and R=R and e=e])
  show "\<mu> B = B (\<mu> B)"
    by (simp add: M def_gfp_unfold)
  show "wf R"
    by (fact WF)
  show "\<And>f st. (\<And>st'. (st', st) \<in> R \<Longrightarrow> (p \<and> e\<^sup>< = \<guillemotleft>st'\<guillemotright> \<longrightarrow> q)\<^sub>e \<sqsubseteq> f) \<Longrightarrow> 
                \<mu> B = f \<Longrightarrow> 
                (p \<and> e\<^sup>< = \<guillemotleft>st\<guillemotright> \<longrightarrow> q)\<^sub>e \<sqsubseteq> B f"
    apply (rule induct_step) oops

lemma nu_rec_total_pure_rule: 
  assumes WF: "wf R"
  and     M: "mono B"  
  and     induct_step:
          "\<And> f st.  \<lbrakk>(p \<and> (e\<^sup><,\<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright> \<longrightarrow> q)\<^sub>e \<sqsubseteq> f\<rbrakk>
               \<Longrightarrow> \<nu> B = f \<Longrightarrow> (p \<and> e\<^sup>< = \<guillemotleft>st\<guillemotright> \<longrightarrow> q)\<^sub>e \<sqsubseteq> (B f)"
        shows "(p \<longrightarrow> q)\<^sub>e \<sqsubseteq> \<nu> B"  
proof (rule wf_fixp_uinduct_pure_ueq_gen[where fp=\<nu> and p=p and B=B and R=R and e=e])
  show "\<nu> B = B (\<nu> B)"
    by (simp add: M def_lfp_unfold)
  show "wf R"
    by (fact WF)
  show "\<And>f st. (\<And>st'. (st', st) \<in> R \<Longrightarrow> (p \<and> e\<^sup>< = \<guillemotleft>st'\<guillemotright> \<longrightarrow> q)\<^sub>e \<sqsubseteq> f) \<Longrightarrow> 
                \<nu> B = f \<Longrightarrow> 
                (p \<and> e\<^sup>< = \<guillemotleft>st\<guillemotright> \<longrightarrow> q)\<^sub>e \<sqsubseteq> B f"
    oops

(*
text \<open>Since @{term "B (p \<and> (E\<^sup><,\<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright> \<longrightarrow> q)\<^sub>e \<sqsubseteq> B (\<mu> B)"} and 
      @{term "mono B"}, thus,  @{thm mu_rec_total_pure_rule} can be expressed as follows\<close>
  
lemma mu_rec_total_utp_rule: 
  assumes WF: "wf R"
    and     M: "mono B"  
    and     induct_step:
    "\<And>st. (p \<and> e\<^sup>< = \<guillemotleft>st\<guillemotright> \<longrightarrow> q)\<^sub>u \<sqsubseteq> (B ((p \<and> (e\<^sup><,\<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright> \<longrightarrow> q))\<^sub>u)"
  shows "(p \<longrightarrow> q)\<^sub>u \<sqsubseteq> \<mu> B"  
proof (rule mu_rec_total_pure_rule[where R=R and e=e], simp_all add: assms)
  show "\<And>f st. (p \<and> (e\<^sup><, \<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright> \<longrightarrow> q)\<^sub>u \<sqsubseteq> f \<Longrightarrow> \<mu> B = f \<Longrightarrow> (p \<and> e\<^sup>< = \<guillemotleft>st\<guillemotright> \<longrightarrow> q)\<^sub>u \<sqsubseteq> B f"
    using M induct_step monoD order_subst2 by (simp add: ref_by_set_def, blast)
qed

lemma nu_rec_total_utp_rule: 
  assumes WF: "wf R"
    and     M: "mono B"  
    and     induct_step:
    "\<And>st. (p \<and> e\<^sup>< = \<guillemotleft>st\<guillemotright> \<longrightarrow> q)\<^sub>u \<sqsubseteq> (B ((p \<and> (e\<^sup><,\<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright> \<longrightarrow> q))\<^sub>u)"
  shows "(p \<longrightarrow> q)\<^sub>u \<sqsubseteq> \<nu> B" 
proof (rule nu_rec_total_pure_rule[where R=R and e=e], simp_all add: assms)
  show "\<And>f st. (p \<and> (e\<^sup><, \<guillemotleft>st\<guillemotright>) \<in> \<guillemotleft>R\<guillemotright> \<longrightarrow> q)\<^sub>u \<sqsubseteq> f \<Longrightarrow> \<nu> B = f \<Longrightarrow> (p \<and> e\<^sup>< = \<guillemotleft>st\<guillemotright> \<longrightarrow> q)\<^sub>u \<sqsubseteq> B f"
    using M induct_step monoD order_subst2 by (simp add: ref_by_set_def, blast)
qed
*)

end