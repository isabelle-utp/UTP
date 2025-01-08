section \<open> Weakest Prespecification \<close>

theory utp_wprespec
  imports "utp_wlp"
begin

no_notation Equiv_Relations.quotient (infixl "'/'/" 90)

definition wprespec :: "('a, 'c) urel \<Rightarrow> ('b, 'c) urel \<Rightarrow> ('a, 'b) urel" (infixl "'/'/" 70) where
[rel]: "wprespec Y K = (\<not> ((\<not> Y) ;; K\<^sup>-))"

lemma wprespec_alt_def: "(P // Q) = (\<not> Q ;; (\<not> P\<^sup>-))\<^sup>-"
  by (simp add: wprespec_def)

theorem wprespec: "R \<sqsubseteq> P ;; Q \<longleftrightarrow> R // Q \<sqsubseteq> P"
  by (pred_auto add: wprespec_def)

lemma wprespec1: "R \<sqsubseteq> (R // Q) ;; Q"
  by (simp add: wprespec)

lemma wprespec2: "(P ;; Q) // Q \<sqsubseteq> P"
  using wprespec by blast

lemma wprespec3: "R // Q \<sqsubseteq> II \<longleftrightarrow> R \<sqsubseteq> Q"
  by (metis seqr_left_unit wprespec)

lemma wprespec4: "Q // Q \<sqsubseteq> II"
  by (simp add: wprespec3)

lemma wprespec5 [wp]: "P // II = P"
  by (metis antisym ref_by_pred_is_leq seqr_right_unit wprespec1 wprespec2)

lemma wprespec6 [wp]: "(R \<and> S) // Q = ((R // Q) \<and> (S // Q))"
  by (rel_auto)
  
lemma wprespec6a [wp]: "(\<Squnion> n\<in>A. R(n)) // Q = (\<Squnion> n\<in>A. R(n) // Q)"
  by (rel_auto)

lemma wprespec7 [wp]: "R // (P \<or> Q) = ((R // P) \<and> (R // Q))"
  by (simp add: seqr_or_distr usubst wprespec_def)

lemma wprespec7a [wp]: "R // (\<Sqinter> i\<in>A. P(i)) = (\<Squnion> i\<in>A. R // P(i))"
  by (pred_auto add: wprespec_def)

lemma wprespec8 [wp]: "R // (P ;; Q)= R // Q // P"
  by (metis (no_types, lifting) pred_ba.order.eq_iff seqr_assoc wprespec wprespec wprespec wprespec1 wprespec1)

theorem wprespec9: "R // Q = \<Sqinter> {Y. R \<sqsubseteq> Y ;; Q}" (is "?lhs = ?rhs")
  by (metis (no_types, lifting) mem_Collect_eq ref_lattice.Inf_eqI wprespec wprespec1)

theorem wprespec10: "(R // Q) (s\<^sub>0, s) = (\<forall> s'. Q (s, s') \<longrightarrow> R (s\<^sub>0, s'))"
  by (pred_auto add: wprespec_def)

lemma wprespec12: "Q\<^sup>- = ((\<not>II) // (\<not>Q))"
  by (simp add: wprespec_def)

lemma wprespec13: "(\<not> (R // Q)) = (\<not>II) // ((\<not>Q) // (\<not>R))"
  by (pred_auto add: wprespec_def)

lemma wprespec17 [wp]: "R // \<langle>\<sigma>\<rangle>\<^sub>a = R ;; (II // \<langle>\<sigma>\<rangle>\<^sub>a)"
  apply (pred_auto add: wprespec_def)
  by metis

lemma wprespec17a [wp]: "II // \<langle>\<sigma>\<rangle>\<^sub>a = \<langle>\<sigma>\<rangle>\<^sub>a\<^sup>-"
  by (pred_auto add: wprespec_def)

theorem wlp_as_wprespec: "P wlp b = post ((b\<^sup>>) // P )"
  apply (simp add: post_def)
  by (pred_auto add: wprespec_def)

end
