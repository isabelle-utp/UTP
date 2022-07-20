section \<open> Weakest Prespecification \<close>

theory utp_wprespec
  imports "UTP2.utp" "UTP2.utp_wlp"
begin

named_theorems wp

text \<open>This notation is now used elsewhere for liberation in Shallow-Expression. So we need to 
give a type restriction explicitly. Or we need to change the notation. \<close>
definition wprespec :: "('b \<leftrightarrow> 'c) \<Rightarrow> ('a \<leftrightarrow> 'c) \<Rightarrow> ('a \<leftrightarrow> 'b)" (infixr "\\" 70) where
[rel]: "wprespec K Y = (\<not> ((\<not> Y) ;; K\<^sup>-))"

lemma wprespec_alt_def: "P \\ Q = (\<not> P ;; (\<not> Q\<^sup>-))\<^sup>-"
  by (rel_auto)

theorem wprespec: "R \<sqsubseteq> P ;; Q \<longleftrightarrow> Q \\ R \<sqsubseteq> P"
  by (rel_auto)

lemma wprespec1: "R \<sqsubseteq> (Q \\ R) ;; Q"
  by (simp add: wprespec)

lemma wprespec2: "Q \\ (P ;; Q) \<sqsubseteq> P"
  by (meson ref_order.order.eq_iff wprespec)

lemma wprespec3: "Q \\ R \<sqsubseteq> II \<longleftrightarrow> R \<sqsubseteq> Q"
  by (metis Id_O_R wprespec)

lemma wprespec4: "Q \\ Q \<sqsubseteq> II"
  by (simp add: wprespec3)

lemma wprespec5 [wp]: "II \\ P = P"
  by (metis R_O_Id ref_order.dual_order.antisym wprespec1 wprespec2)

lemma wprespec6 [wp]: "Q \\ (R \<and> S) = ((Q \\ R) \<and> (Q \\ S))"
  by (rel_auto)
  
lemma wprespec6a [wp]: "Q \\ (\<Inter> n\<in>A. R(n)) = (\<Inter> n\<in>A. Q \\ R(n))"
  by (rel_auto)

lemma wprespec6a' [wp]: "Q \\ (\<Squnion> n\<in>A. R(n)) = (\<Squnion> n\<in>A. Q \\ R(n))"
  by (rel_auto)

lemma wprespec7 [wp]: "(P \<or> Q) \\ R = ((P \\ R) \<and> (Q \\ R))"
  by (rel_auto)

lemma wprespec7a [wp]: "(\<Sqinter> i\<in>A. P(i)) \\ (R::('a \<leftrightarrow> 'b)) = (\<Squnion> i\<in>A. (P(i) \\ R))"
  by (rel_auto)

lemma wprespec7a' [wp]: "(\<Union> i\<in>A. P(i)) \\ (R::('a \<leftrightarrow> 'b)) = (\<Inter> i\<in>A. (P(i) \\ R))"
  by (rel_auto)

lemma wprespec8 [wp]: "(P ;; Q) \\ (R::('a \<leftrightarrow> 'b)) = P \\ Q \\ R"
  by (rel_auto)

theorem wprespec9: "Q \\ R = \<Sqinter> {Y. R \<sqsubseteq> Y ;; Q}" (is "?lhs = ?rhs")
proof (rule antisym)
  show "Q \\ R \<subseteq> \<Union> {Y. R \<sqsubseteq> Y ;; Q}"
    by (simp add: Union_upper wprespec1)
  show "\<Union> {Y. R \<sqsubseteq> Y ;; Q} \<subseteq> Q \\ R"
    by (metis Sup_least mem_Collect_eq ref_by_set_def wprespec)
qed

theorem wprespec10: "\<lbrakk>(Q \\ (R::('a \<leftrightarrow> 'b)))\<rbrakk>\<^sub>P (s\<^sub>0, s) = (\<forall> s'. \<lbrakk>Q\<rbrakk>\<^sub>P (s, s') \<longrightarrow> \<lbrakk>R\<rbrakk>\<^sub>P (s\<^sub>0, s'))"
  by (rel_auto)

lemma wprespec12: "Q\<^sup>- = ((\<not>Q) \\ (\<not>II))"
  by (rel_auto)

lemma wprespec13: "- (Q \\ R) = (-R \\ -Q) \\ -II"
  by (rel_auto)

lemma wprespec17 [wp]: "\<langle>\<sigma>\<rangle>\<^sub>a \\ R = R ;; (\<langle>\<sigma>\<rangle>\<^sub>a \\ II)"
  apply (rel_auto)
  by force

lemma wprespec17a [wp]: "\<langle>\<sigma>\<rangle>\<^sub>a \\ II = \<langle>\<sigma>\<rangle>\<^sub>a\<^sup>-"
  apply (rel_auto)
  by force

declare [[show_types]]

term "P wlp b"
term "((P::('a \<leftrightarrow> 'b)) \\ (b\<^sup>>)\<^sub>u)"
term "\<lbrakk>((P::('a \<leftrightarrow> 'b)) \\ (b\<^sup>>)\<^sub>u)\<rbrakk>\<^sub>P"
term "post ((P::('a \<leftrightarrow> 'b)) \\ (b\<^sup>>)\<^sub>u)"
theorem wlp_as_wprespec: "P wlp b = post ((P::('a \<leftrightarrow> 'b)) \\ (b\<^sup>>)\<^sub>u)"
  apply (simp add: post_def)
  by (rel_auto)

end
