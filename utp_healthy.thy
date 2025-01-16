section \<open> Healthiness Conditions \<close>

theory utp_healthy
  imports utp_pred_laws utp_recursion
begin

subsection \<open> Main Definitions \<close>

text \<open> We collect closure laws for healthiness conditions in the following theorem attribute. \<close>

named_theorems closure

type_synonym 'a health = "'a pred \<Rightarrow> 'a pred"

text \<open> A predicate $P$ is healthy, under healthiness function $H$, if $P$ is a fixed-point of $H$. \<close>

definition Healthy :: "'\<alpha> pred \<Rightarrow> '\<alpha> health \<Rightarrow> bool" (infix "is" 30)
  where [pred]: "P is H \<equiv> (H P = P)"

lemma Healthy_def': "P is H \<longleftrightarrow> (H P = P)"
  unfolding Healthy_def by auto

lemma Healthy_if: "P is H \<Longrightarrow> (H P = P)"
  unfolding Healthy_def by auto

lemma Healthy_intro: "H(P) = P \<Longrightarrow> P is H"
  by (simp add: Healthy_def)

abbreviation Healthy_carrier :: "'\<alpha> health \<Rightarrow> '\<alpha> pred set" ("\<lbrakk>_\<rbrakk>\<^sub>H")
where "\<lbrakk>H\<rbrakk>\<^sub>H \<equiv> {P. P is H}"

lemma Healthy_carrier_image:
  "A \<subseteq> \<lbrakk>\<H>\<rbrakk>\<^sub>H \<Longrightarrow> \<H> ` A = A"
    by (auto simp add: image_def, (metis Healthy_if mem_Collect_eq subsetCE)+)

lemma Healthy_carrier_Collect: "A \<subseteq> \<lbrakk>H\<rbrakk>\<^sub>H \<Longrightarrow> A = {H(P) | P. P \<in> A}"
  by (simp add: Healthy_carrier_image Setcompr_eq_image)

lemma Healthy_func:
  "\<lbrakk> F \<in> \<lbrakk>\<H>\<^sub>1\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<H>\<^sub>2\<rbrakk>\<^sub>H; P is \<H>\<^sub>1 \<rbrakk> \<Longrightarrow> F(P) = \<H>\<^sub>2(F(P))"
  by (metis Healthy_if PiE mem_Collect_eq)

lemma Healthy_comp:
  "\<lbrakk> P is \<H>\<^sub>1; P is \<H>\<^sub>2 \<rbrakk> \<Longrightarrow> P is \<H>\<^sub>1 \<circ> \<H>\<^sub>2"
  by (simp add: Healthy_def)
    
lemma Healthy_apply_closed:
  assumes "F \<in> \<lbrakk>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>H\<rbrakk>\<^sub>H" "P is H"
  shows "F(P) is H"
  using assms by auto

lemma Healthy_set_image_member:
  "\<lbrakk> P \<in> F ` A; \<And> x. F x is H \<rbrakk> \<Longrightarrow> P is H"
  by blast

lemma Healthy_case_prod: 
  "\<lbrakk> \<And> x y. P x y is H \<rbrakk> \<Longrightarrow> case_prod P v is H"
  by (simp add: prod.case_eq_if)

lemma Healthy_SUPREMUM:
  "A \<subseteq> \<lbrakk>H\<rbrakk>\<^sub>H \<Longrightarrow> Sup (H ` A) = \<Sqinter> A"
  by (drule Healthy_carrier_image, presburger)

lemma Healthy_INFIMUM:
  "A \<subseteq> \<lbrakk>H\<rbrakk>\<^sub>H \<Longrightarrow> Inf (H ` A) = \<Squnion> A"
  by (drule Healthy_carrier_image, presburger)

lemma Healthy_nu [closure]:
  assumes "mono F" "F \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>H\<rbrakk>\<^sub>H"
  shows "\<nu> F is H"
  by (metis (mono_tags) Healthy_def Healthy_func assms eq_id_iff lfp_unfold)

lemma Healthy_mu [closure]:
  assumes "mono F" "F \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>H\<rbrakk>\<^sub>H"
  shows "\<mu> F is H"
  by (metis (mono_tags) Healthy_def Healthy_func assms eq_id_iff gfp_unfold)

lemma Healthy_subset_member: "\<lbrakk> A \<subseteq> \<lbrakk>H\<rbrakk>\<^sub>H; P \<in> A \<rbrakk> \<Longrightarrow> H(P) = P"
  using Healthy_if by blast
  
lemma is_Healthy_subset_member: "\<lbrakk> A \<subseteq> \<lbrakk>H\<rbrakk>\<^sub>H; P \<in> A \<rbrakk> \<Longrightarrow> P is H"
  by blast

subsection \<open> Properties of Healthiness Conditions \<close>

definition Idempotent :: "'\<alpha> health \<Rightarrow> bool" where
  [pred]: "Idempotent(H) \<longleftrightarrow> (\<forall> P. H(H(P)) = H(P))"

abbreviation Monotonic :: "'\<alpha> health \<Rightarrow> bool" where
  "Monotonic(H) \<equiv> mono H"

definition IMH :: "'\<alpha> health \<Rightarrow> bool" where
  [pred]: "IMH(H) \<longleftrightarrow> Idempotent(H) \<and> Monotonic(H)"

definition Antitone :: "'\<alpha> health \<Rightarrow> bool" where
  "Antitone(H) \<longleftrightarrow> (\<forall> P Q. Q \<sqsubseteq> P \<longrightarrow> (H(P) \<sqsubseteq> H(Q)))"

definition Conjunctive :: "'\<alpha> health \<Rightarrow> bool" where
  "Conjunctive(H) \<longleftrightarrow> (\<exists> Q. \<forall> P. H(P) = (P \<and> Q))"

definition FunctionalConjunctive :: "'\<alpha> health \<Rightarrow> bool" where
  "FunctionalConjunctive(H) \<longleftrightarrow> (\<exists> F. \<forall> P. H(P) = (P \<and> F(P)) \<and> Monotonic(F))"

definition WeakConjunctive :: "'\<alpha> health \<Rightarrow> bool" where
  "WeakConjunctive(H) \<longleftrightarrow> (\<forall> P. \<exists> Q. H(P) = (P \<and> Q))"

definition Disjunctuous :: "'\<alpha> health \<Rightarrow> bool" where
  [pred]: "Disjunctuous H = (\<forall> P Q. H(P \<or> Q) = (H(P) \<or> H(Q)))"

definition Continuous :: "'\<alpha> health \<Rightarrow> bool" where
  [pred]: "Continuous H = (\<forall> A. A \<noteq> {} \<longrightarrow> H (\<Sqinter> A) = \<Sqinter> (H ` A))"

lemma Healthy_Idempotent [closure]:
  "Idempotent H \<Longrightarrow> H(P) is H"
  by (simp add: Healthy_def Idempotent_def)

lemma Healthy_range: "Idempotent H \<Longrightarrow> range H = \<lbrakk>H\<rbrakk>\<^sub>H"
  by (auto simp add: image_def Healthy_if Healthy_Idempotent, metis Healthy_if)

lemma Idempotent_id [simp]: "Idempotent id"
  by (simp add: Idempotent_def)

lemma Idempotent_comp [intro]:
  "\<lbrakk> Idempotent f; Idempotent g; f \<circ> g = g \<circ> f \<rbrakk> \<Longrightarrow> Idempotent (f \<circ> g)"
  by (auto simp add: Idempotent_def comp_def, metis+)

lemma Idempotent_image: "Idempotent f \<Longrightarrow> f ` (f ` A) = (f ` A)"
  by (metis (mono_tags, lifting) Idempotent_def image_cong image_image)

named_theorems mono

lemma Monotonic_refine: "Monotonic F \<longleftrightarrow> (\<forall> P Q. P \<sqsubseteq> Q \<longrightarrow> F(P) \<sqsubseteq> F(Q))"
  by (metis monoE monoI pred_ref_iff_le)

lemma Monotonic_id [simp]: "Monotonic id"
  by (simp add: monoI)

lemma Monotonic_id' [mono]: 
  "mono (\<lambda> X. X)" 
  by (simp add: monoI)
    
lemma Monotonic_const [mono]:
  "Monotonic (\<lambda> x. c)"
  by (simp add: mono_def)
    
lemma Monotonic_comp [intro, mono]:
  "\<lbrakk> Monotonic f; Monotonic g \<rbrakk> \<Longrightarrow> Monotonic (f \<circ> g)"
  by (simp add: mono_def)

lemma Monotonic_sup [mono]:
  assumes "Monotonic P" "Monotonic Q"
  shows "Monotonic (\<lambda> X. P X \<sqinter> Q X)"
  using assms unfolding mono_def by (meson sup_mono)

lemma Monotonic_disj [mono]:
  assumes "Monotonic P" "Monotonic Q"
  shows "Monotonic (\<lambda> X. P(X) \<or> Q(X))"
  by (insert assms, simp add: disj_pred_def Monotonic_sup)

lemma Monotonic_cond:
  assumes "Monotonic P" "Monotonic Q"
  shows "Monotonic (\<lambda> X. P(X) \<triangleleft> b \<triangleright> Q(X))"
  by (insert assms, simp add: mono_def pred le_fun_def)
    
lemma Conjuctive_Idempotent:
  "Conjunctive(H) \<Longrightarrow> Idempotent(H)"
  by (auto simp add: Conjunctive_def Idempotent_def conj_pred_def)

lemma Conjunctive_Monotonic:
  "Conjunctive(H) \<Longrightarrow> Monotonic(H)"
  unfolding Conjunctive_def mono_def
  by (metis (no_types, opaque_lifting) conj_pred_def le_inf_iff order.trans order_refl)

lemma Conjunctive_conj:
  assumes "Conjunctive(HC)"
  shows "HC(P \<and> Q) = (HC(P) \<and> Q)"
  using assms unfolding Conjunctive_def
  by (metis conj_pred_def inf.commute inf_sup_aci(2))

lemma Conjunctive_distr_conj:
  assumes "Conjunctive(HC)"
  shows "HC(P \<and> Q) = (HC(P) \<and> HC(Q))"
  using assms unfolding Conjunctive_def
  by (metis Conjunctive_conj assms conj_pred_def inf.right_idem inf_sup_aci(2))

lemma Conjunctive_distr_disj:
  assumes "Conjunctive(HC)"
  shows "HC(P \<or> Q) = (HC(P) \<or> HC(Q))"
  using assms unfolding Conjunctive_def
  by (metis conj_pred_def disj_pred_def inf_sup_distrib2)

lemma Conjunctive_distr_cond:
  assumes "Conjunctive(HC)"
  shows "HC(P \<triangleleft> b \<triangleright> Q) = (HC(P) \<triangleleft> b \<triangleright> HC(Q))"
  using assms unfolding Conjunctive_def
  apply pred_simp
  by force
  
lemma FunctionalConjunctive_Monotonic:
  "FunctionalConjunctive(H) \<Longrightarrow> Monotonic(H)"
  unfolding FunctionalConjunctive_def
  by (smt (verit, del_insts) conj_pred_def dual_order.trans le_inf_iff mono_def order_refl)

lemma WeakConjunctive_Refinement:
  assumes "WeakConjunctive(HC)"
  shows "P \<sqsubseteq> HC(P)"
  using assms unfolding WeakConjunctive_def
  by (metis conj_pred_def inf1D1 pred_refine_iff)

lemma WeakCojunctive_Healthy_Refinement:
  assumes "WeakConjunctive(HC)" and "P is HC"
  shows "HC(P) \<sqsubseteq> P"
  using assms unfolding WeakConjunctive_def Healthy_def by simp

lemma WeakConjunctive_implies_WeakConjunctive:
  "Conjunctive(H) \<Longrightarrow> WeakConjunctive(H)"
  unfolding WeakConjunctive_def Conjunctive_def by pred_auto

lemma Disjunctuous_Monotonic: "Disjunctuous H \<Longrightarrow> Monotonic H"
  by (metis (no_types, lifting) Disjunctuous_def disj_pred_def le_iff_sup mono_def)

lemma ContinuousD [dest]: "\<lbrakk> Continuous H; A \<noteq> {} \<rbrakk> \<Longrightarrow> H (\<Sqinter> A) = (\<Sqinter> P\<in>A. H(P))"
  by (simp add: Continuous_def)

lemma Continuous_Disjunctous: "Continuous H \<Longrightarrow> Disjunctuous H"
  apply (auto simp add: Continuous_def Disjunctuous_def)
  by (metis SUP_insert Sup_insert cSup_singleton disj_pred_def insert_not_empty)

lemma Continuous_choice_dist: "Continuous H \<Longrightarrow> H(P \<sqinter> Q) = H(P) \<sqinter> H(Q)"
  using Continuous_Disjunctous Disjunctuous_def
  by (metis disj_pred_def)

lemma Continuous_Monotonic [closure]: "Continuous H \<Longrightarrow> Monotonic H"
  by (simp add: Continuous_Disjunctous Disjunctuous_Monotonic)

lemma Continuous_comp [intro]:
  "\<lbrakk> Continuous f; Continuous g \<rbrakk> \<Longrightarrow> Continuous (f \<circ> g)"
  unfolding Continuous_def by (simp, blast)

lemma Continuous_const [closure]: "Continuous (\<lambda> X. P)"
  by pred_auto

lemma Continuous_cond [closure]:
  assumes "Continuous F" "Continuous G"
  shows "Continuous (\<lambda> X. F(X) \<triangleleft> b \<triangleright> G(X))"
  by (pred_simp assms: assms, metis)

text \<open> Closure laws derived from continuity \<close>

lemma Sup_Continuous_closed [closure]:
  "\<lbrakk> Continuous H; \<And> i. i \<in> A \<Longrightarrow> P(i) is H; A \<noteq> {} \<rbrakk> \<Longrightarrow> (\<Sqinter> i\<in>A. P(i)) is H"
  by (drule ContinuousD[of H "P ` A"], auto) (metis (no_types, lifting) Healthy_def' SUP_cong image_image)

lemma Sup_mem_Continuous_closed_pair [closure]:
  assumes "Continuous H" "\<And> i j. (i, j) \<in> A \<Longrightarrow> P i j is H" "A \<noteq> {}"
  shows "(\<Sqinter> (i,j)\<in>A. P i j) is H"
  by (simp add: Sup_Continuous_closed assms split_beta)

lemma Sup_mem_Continuous_closed_triple:
  assumes "Continuous H" "\<And> i j k. (i, j, k) \<in> A \<Longrightarrow> P i j k is H" "A \<noteq> {}"
  shows "(\<Sqinter> (i,j,k)\<in>A. P i j k) is H"
  by (simp add: Sup_Continuous_closed assms split_beta)

lemma Sup_mem_Continuous_closed_quad:
  assumes "Continuous H" "\<And> i j k l. (i, j, k, l) \<in> A \<Longrightarrow> P i j k l is H" "A \<noteq> {}"
  shows "(\<Sqinter> (i,j,k,l)\<in>A. P i j k l) is H"
  by (simp add: Sup_Continuous_closed assms split_beta)

lemma Sup_mem_Continuous_closed_quint:
  assumes "Continuous H" "\<And> i j k l m. (i, j, k, l, m) \<in> A \<Longrightarrow> P i j k l m is H" "A \<noteq> {}"
  shows "(\<Sqinter> (i,j,k,l,m)\<in>A. P i j k l m) is H"
  by (simp add: Sup_Continuous_closed assms split_beta)

text \<open> All continuous functions are also Scott-continuous \<close>

lemma sup_continuous_Continuous [closure]: "Continuous F \<Longrightarrow> sup_continuous F"
  by (auto simp add: Continuous_def sup_continuous_def)

lemma Inf_healthy: "A \<subseteq> \<lbrakk>H\<rbrakk>\<^sub>H \<Longrightarrow> (\<Squnion> P\<in>A. F(P)) = (\<Squnion> P\<in>A. F(H(P)))"
  by (rule INF_cong, auto simp add: Healthy_subset_member)

lemma Sup_healthy: "A \<subseteq> \<lbrakk>H\<rbrakk>\<^sub>H \<Longrightarrow> (\<Sqinter> P\<in>A. F(P)) = (\<Sqinter> P\<in>A. F(H(P)))"
  by (rule SUP_cong, auto simp add: Healthy_subset_member)
  
end