section \<open> Relational Calculus Laws \<close>

theory utp_rel_laws
  imports 
    utp_rel
    utp_recursion
    utp_healthy
begin

section \<open> Conditional Laws \<close>

lemma rcond_idem [simp]: "P \<lhd> b \<rhd> P = P"
  by pred_auto

lemma rcond_sym: "P \<lhd> b \<rhd> Q = Q \<lhd> \<not>b \<rhd> P"
  by pred_auto

lemma rcond_assoc: "(P \<lhd> b \<rhd> Q) \<lhd> c \<rhd> R = P \<lhd> b \<and> c \<rhd> (Q \<lhd> c \<rhd> R)"
  by pred_auto

lemma rcond_distr: "P \<lhd> b \<rhd> (Q \<lhd> c \<rhd> R) = (P \<lhd> b \<rhd> Q) \<lhd> c \<rhd> (P \<lhd> b \<rhd> R)"
  by pred_auto

lemma rcond_true [simp]: "P \<lhd> True \<rhd> Q = P"
  by pred_auto

lemma rcond_false [simp]: "P \<lhd> False \<rhd> Q = Q"
  by pred_auto

lemma rcond_reach [simp]: "P \<lhd> b \<rhd> (Q \<lhd> b \<rhd> R) = P \<lhd> b \<rhd> R"
  by pred_auto

lemma rcond_disj [simp]: "P \<lhd> b \<rhd> (P \<lhd> c \<rhd> Q) = P \<lhd> b \<or> c \<rhd> Q"
  by pred_auto

lemma rcomp_rcond_left_distr:
  "(P \<lhd> b \<rhd> Q) ;; R = (P ;; R) \<lhd> b \<rhd> (Q ;; R) "
  by (pred_auto)

lemma rcond_seq_left_distr:
  "out\<alpha> \<sharp> b \<Longrightarrow> ((P \<triangleleft> b \<triangleright> Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright> (Q ;; R))"
  by (pred_auto, blast)

lemma rcond_seq_right_distr:
  "in\<alpha> \<sharp> b \<Longrightarrow> (P ;; (Q \<triangleleft> b \<triangleright> R)) = ((P ;; Q) \<triangleleft> b \<triangleright> (P ;; R))"
  by (pred_auto, blast)

text \<open> Alternative expression of conditional using assumptions and choice \<close>

lemma rcond_rassume_expand: "P \<lhd> b \<rhd> Q = (\<questiondown>b? ;; P) \<sqinter> (\<questiondown>(\<not> b)? ;; Q)"
  by pred_auto

lemma rcond_mono [mono]: "\<lbrakk> (P\<^sub>1 :: 's pred) \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<triangleleft> b \<triangleright> Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 \<triangleleft> b \<triangleright> Q\<^sub>2)"
  by pred_auto

lemma rcond_refine: "(P \<sqsubseteq> (Q \<triangleleft> b \<triangleright> R)) = (P \<sqsubseteq> (b \<and> Q)\<^sub>e \<and> (P \<sqsubseteq> ((\<not>b \<and> R)\<^sub>e)))"
  by pred_auto

section \<open> Precondition and Postcondition Laws \<close>
  
theorem precond_equiv:
  "P = (P ;; true) \<longleftrightarrow> (out\<alpha> \<sharp> P)"
  by (pred_auto)

theorem postcond_equiv:
  "P = (true ;; P) \<longleftrightarrow> (in\<alpha> \<sharp> P)"
  by (pred_auto)

theorem precond_left_zero:
  assumes "out\<alpha> \<sharp> p" "p \<noteq> false"
  shows "(true ;; p) = true"
  by (pred_auto assms: assms)

theorem feasible_iff_true_right_zero:
  "P ;; true = true \<longleftrightarrow> `\<exists> \<^bold>v\<^sup>> \<Zspot> P`"
  by pred_auto
   
subsection \<open> Sequential Composition Laws \<close>
    
lemma seqr_assoc: "(P ;; Q) ;; R = P ;; (Q ;; R)"
  by (pred_auto)

lemma seqr_left_unit [simp]:
  "II ;; P = P"
  by (pred_auto)

lemma seqr_right_unit [simp]:
  "P ;; II = P"
  by (pred_auto)

lemma seqr_left_zero [simp]:
  "false ;; P = false"
  by pred_auto

lemma seqr_right_zero [simp]:
  "P ;; false = false"
  by pred_auto

lemma seqr_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 ;; Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 ;; Q\<^sub>2)"
  by (pred_auto, blast)
    
lemma mono_seqr [mono]:
  "\<lbrakk> mono P; mono Q \<rbrakk> \<Longrightarrow> mono (\<lambda> X. P X ;; Q X)"
  by (pred_auto add: mono_def, blast)
  
lemma cond_seqr_mono [mono]: "mono (\<lambda>X. (P ;; X) \<lhd> b \<rhd> II)"
  by (pred_auto add: mono_def)

lemma mono_seqr_tail:
  assumes "mono F"
  shows "mono (\<lambda> X. P ;; F(X))"
  by (pred_auto assms: assms add: mono_def)

lemma seqr_liberate_left: "vwb_lens x \<Longrightarrow> ((P  \\ $x\<^sup><) ;; Q) = ((P ;; Q) \\ $x\<^sup><)"
  by (pred_auto)

lemma seqr_liberate_right: "vwb_lens x \<Longrightarrow> P ;; Q \\ $x\<^sup>> = (P ;; Q) \\ $x\<^sup>>"
  by pred_auto

lemma seqr_or_distl:
  "((P \<or> Q) ;; R) = ((P ;; R) \<or> (Q ;; R))"
  by (pred_auto)

lemma seqr_or_distr:
  "(P ;; (Q \<or> R)) = ((P ;; Q) \<or> (P ;; R))"
  by (pred_auto)

lemma seqr_and_distr_ufunc:
  "Functional P \<Longrightarrow> (P ;; (Q \<and> R)) = ((P ;; Q) \<and> (P ;; R))"
  by (rel_auto, metis single_valuedD)

lemma seqr_and_distl_uinj:
  "Injective R \<Longrightarrow> ((P \<and> Q) ;; R) = ((P ;; R) \<and> (Q ;; R))"
  by (rel_auto, auto simp add: injective_def)

lemma seqr_unfold:
  "(P ;;\<^sub>h Q) = (\<exists> v. P\<lbrakk>\<guillemotleft>v\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>v\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>)\<^sub>e"
  by pred_auto
      
lemma seqr_unfold_heterogeneous:
  "(P ;; Q) = (\<exists> v. (pre(P\<lbrakk>\<guillemotleft>v\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk>))\<^sup>< \<and> (post(Q\<lbrakk>\<guillemotleft>v\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>))\<^sup>>)\<^sub>e"
  by pred_auto

lemma seqr_middle: "vwb_lens x \<Longrightarrow> P ;; Q = (\<Sqinter> v. P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup><\<rbrakk>)"
  by (pred_auto, metis vwb_lens.put_eq)

lemma seqr_left_one_point:
  assumes "vwb_lens x"
  shows "(P \<and> ($x\<^sup>> = \<guillemotleft>v\<guillemotright>)\<^sub>e) ;; Q = P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup><\<rbrakk>"
  by (pred_auto assms: assms, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_right_one_point:
  assumes "vwb_lens x"
  shows "P ;; (($x\<^sup>< = \<guillemotleft>v\<guillemotright>)\<^sub>e \<and> Q) = P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup><\<rbrakk>"
  using assms
  by (pred_auto, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_left_one_point_true:
  assumes "vwb_lens x"
  shows "(P \<and> ($x\<^sup>>)\<^sub>e) ;; Q = P\<lbrakk>True/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>True/x\<^sup><\<rbrakk>"
  using assms
  by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma seqr_left_one_point_false:
  assumes "vwb_lens x"
  shows "((P \<and> \<not>($x\<^sup>>)\<^sub>e) ;; Q) = (P\<lbrakk>False/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>False/x\<^sup><\<rbrakk>)"
  using assms by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma seqr_right_one_point_true:
  assumes "vwb_lens x"
  shows "(P ;; (($x\<^sup><)\<^sub>e \<and> Q)) = (P\<lbrakk>True/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>True/x\<^sup><\<rbrakk>)"
  using assms by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma seqr_right_one_point_false:
  assumes "vwb_lens x"
  shows "(P ;; (\<not>($x\<^sup><)\<^sub>e \<and> Q)) = (P\<lbrakk>False/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>False/x\<^sup><\<rbrakk>)"
  using assms by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma seqr_insert_ident_left:
  assumes "vwb_lens x" "$x\<^sup>> \<sharp> P" "$x\<^sup>< \<sharp> Q"
  shows "((($x\<^sup>> = $x\<^sup><)\<^sub>e \<and> P) ;; Q) = (P ;; Q)"
  by (pred_auto assms: assms, meson vwb_lens_def wb_lens_weak weak_lens.put_get)

lemma seqr_insert_ident_right:
  assumes "vwb_lens x" "$x\<^sup>> \<sharp> P" "$x\<^sup>< \<sharp> Q"
  shows "(P ;; (($x\<^sup>> = $x\<^sup><)\<^sub>e \<and> Q)) = (P ;; Q)"
  by (pred_auto assms: assms, metis (no_types, opaque_lifting) vwb_lens_def wb_lens_def weak_lens.put_get)

lemma seq_var_ident_lift:
  assumes "vwb_lens x" "$x\<^sup>> \<sharp> P" "$x\<^sup>< \<sharp> Q"
  shows "((($x\<^sup>> = $x\<^sup><)\<^sub>e \<and> P) ;; (($x\<^sup>> = $x\<^sup><)\<^sub>e \<and> Q)) = (($x\<^sup>> = $x\<^sup><)\<^sub>e \<and> (P ;; Q))"
  by (pred_auto assms: assms, metis (no_types, lifting) vwb_lens_wb wb_lens_weak weak_lens.put_get)

lemma seqr_bool_split:
  assumes "vwb_lens x"
  shows "P ;; Q = (P\<lbrakk>True/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>True/x\<^sup><\<rbrakk> \<or> P\<lbrakk>False/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>False/x\<^sup><\<rbrakk>)"
  using assms apply (subst seqr_middle[of x], simp_all)
  apply pred_auto
  apply (metis (full_types))
  done

lemma cond_inter_var_split:
  assumes "vwb_lens x"
  shows "(P \<triangleleft> $x\<^sup>> \<triangleright> Q) ;; R = (P\<lbrakk>True/x\<^sup>>\<rbrakk> ;; R\<lbrakk>True/x\<^sup><\<rbrakk> \<or> Q\<lbrakk>False/x\<^sup>>\<rbrakk> ;; R\<lbrakk>False/x\<^sup><\<rbrakk>)"
proof -
  have "(P \<triangleleft> $x\<^sup>> \<triangleright> Q) ;; R = (((x\<^sup>>)\<^sub>e \<and> P) ;; R \<or> (\<not> (x\<^sup>>)\<^sub>e \<and> Q) ;; R)"
    by pred_auto
  also have "... = ((P \<and> (x\<^sup>>)\<^sub>e) ;; R \<or> (Q \<and> \<not>(x\<^sup>>)\<^sub>e) ;; R)"
    by (pred_auto)
  also have "... = (P\<lbrakk>True/x\<^sup>>\<rbrakk> ;; R\<lbrakk>True/x\<^sup><\<rbrakk> \<or> Q\<lbrakk>False/x\<^sup>>\<rbrakk> ;; R\<lbrakk>False/x\<^sup><\<rbrakk>)"
    apply (pred_auto add: seqr_left_one_point_true seqr_left_one_point_false assms)
    by (metis (full_types) assms vwb_lens_wb wb_lens.get_put)+
  finally show ?thesis .
qed

theorem seqr_pre_transfer: "in\<alpha> \<sharp> q \<Longrightarrow> ((P \<and> q) ;; R) = (P ;; (q\<^sup>- \<and> R))"
  by pred_auto

theorem seqr_pre_transfer':
  "((P \<and> (q\<^sup>>)\<^sub>e) ;; R) = (P ;; ((q\<^sup><)\<^sub>e \<and> R))"
  by (pred_auto)

theorem seqr_post_out: "in\<alpha> \<sharp> r \<Longrightarrow> (P ;; (Q \<and> r)) = ((P ;; Q) \<and> r)"
  by (pred_auto)

lemma seqr_post_var_out:
  shows "(P ;; (Q \<and> (x\<^sup>>)\<^sub>e)) = ((P ;; Q) \<and> (x\<^sup>>)\<^sub>e)"
  by (pred_auto)

theorem seqr_post_transfer: "out\<alpha> \<sharp> q \<Longrightarrow> (P ;; (q \<and> R)) = ((P \<and> q\<^sup>-) ;; R)"
  by (pred_auto)

lemma seqr_pre_out: "out\<alpha> \<sharp> p \<Longrightarrow> ((p \<and> Q) ;; R) = (p \<and> (Q ;; R))"
  by (pred_auto)

lemma seqr_pre_var_out:
  shows "(((x\<^sup><)\<^sub>e \<and> P) ;; Q) = ((x\<^sup><)\<^sub>e \<and> (P ;; Q))"
  by (pred_auto)

lemma seqr_true_lemma:
  "(P = (\<not> ((\<not> P) ;; true))) = (P = (P ;; true))"
  by (pred_auto)

lemma seqr_to_conj: "\<lbrakk> out\<alpha> \<sharp> P; in\<alpha> \<sharp> Q \<rbrakk> \<Longrightarrow> (P ;; Q) = (P \<and> Q)"
  by (pred_auto; blast)

lemma liberate_seq_unfold:
  "vwb_lens x \<Longrightarrow> $x \<sharp> Q \<Longrightarrow> (P \\ $x) ;; Q = (P ;; Q) \\ $x"
  apply (pred_auto)
  oops

(* The following laws are like HOL.ex_simps but for lenses *)

named_theorems pred_ex_simps

lemma ex_lens_split_conj_unrest [pred_ex_simps]:
  assumes "$x \<sharp> Q" "mwb_lens x"
  shows "(\<exists> x \<Zspot> P \<and> Q) = ((\<exists> x \<Zspot> P) \<and> Q)"
  using assms by pred_auto

lemma ex_lens_split_conj_unrest2 [pred_ex_simps]:
  assumes "$x \<sharp> P" "mwb_lens x"
  shows "(\<exists> x \<Zspot> P \<and> Q) = (P \<and> (\<exists> x \<Zspot> Q))"
  using assms by pred_auto

lemma ex_lens_split_disj_unrest  [pred_ex_simps]:
  assumes "$x \<sharp> Q" "mwb_lens x"
  shows "(\<exists> x \<Zspot> P \<or> Q) = ((\<exists> x \<Zspot> P) \<or> Q)"
  using assms by pred_auto

lemma ex_lens_split_disj_unrest2  [pred_ex_simps]:
  assumes "$x \<sharp> P" "mwb_lens x"
  shows "(\<exists> x \<Zspot> P \<or> Q) = (P \<or> (\<exists> x \<Zspot> Q))"
  using assms by pred_auto

lemma ex_lens_split_impl_unrest  [pred_ex_simps]:
  assumes "$x \<sharp> Q" "mwb_lens x"
  shows "(\<exists> x \<Zspot> P \<longrightarrow> Q) = ((\<forall> x \<Zspot> P) \<longrightarrow> Q)"
  using assms by pred_auto

lemma ex_lens_split_impl_unrest2  [pred_ex_simps]:
  assumes "$x \<sharp> P" "mwb_lens x"
  shows "(\<exists> x \<Zspot> P \<longrightarrow> Q) = (P \<longrightarrow> (\<exists> x \<Zspot> Q))"
  using assms by pred_auto

subsection \<open> Iterated Sequential Composition Laws \<close>
  
lemma iter_seqr_nil [simp]: "(;; i : [] \<bullet> P(i)) = II"
  by (simp add: seqr_iter_def)
    
lemma iter_seqr_cons [simp]: "(;; i : (x # xs) \<bullet> P(i)) = P(x) ;; (;; i : xs \<bullet> P(i))"
  by (simp add: seqr_iter_def)

subsection \<open> Quantale Laws \<close>

lemma seq_Sup_distl: "P ;; (\<Sqinter> A) = (\<Sqinter> Q\<in>A. P ;; Q)"
  by pred_auto

lemma seq_Sup_distr: "(\<Sqinter> A) ;; Q = (\<Sqinter> P\<in>A. P ;; Q)"
  by pred_auto

lemma seq_SUP_distl: "P ;; (\<Sqinter> Q\<in>A. F(Q)) = (\<Sqinter> Q\<in>A. P ;; F(Q))"
  by pred_auto

lemma seq_SUP_distr: "(\<Sqinter> P\<in>A. F(P)) ;; Q = (\<Sqinter> P\<in>A. F(P) ;; Q)"
  by pred_auto

subsection \<open> Skip Laws \<close>
    
lemma cond_skip: "out\<alpha> \<sharp> b \<Longrightarrow> (b \<and> II) = (II \<and> b\<^sup>-)"
  by (pred_auto)

lemma pre_skip_post: "((b\<^sup><)\<^sub>e \<and> II) = (II \<and> (b\<^sup>>)\<^sub>e)"
  by (pred_auto)

lemma skip_var:
  fixes x :: "(bool \<Longrightarrow> '\<alpha>)"
  shows "(($x\<^sup><)\<^sub>e \<and> II) = (II \<and> ($x\<^sup>>)\<^sub>e)"
  by (pred_auto)

lemma rel_expr_interp [rel]: "\<lbrakk>(p)\<^sub>e\<rbrakk>\<^sub>U = Collect p"
  by (simp add: pred_rel_def expr_defs)

lemma skip_r_unfold:
  "vwb_lens x \<Longrightarrow> II = (($x\<^sup>> = $x\<^sup><)\<^sub>e \<and> (\<exists> x\<^sup>< \<Zspot> \<exists> x\<^sup>> \<Zspot> II))"
  by (rel_auto, blast, metis vwb_lens.put_eq)  

lemma skip_r_alpha_eq:
  "II = (\<^bold>v\<^sup>< = \<^bold>v\<^sup>>)\<^sub>e"
  by (pred_auto)

subsection \<open> Assignment Laws \<close>

lemma assigns_skip: "\<langle>id\<rangle>\<^sub>a = II"
  by pred_auto

lemma assigns_comp: "\<langle>\<sigma>\<rangle>\<^sub>a ;; \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  by pred_auto

lemma assigns_cond: "\<langle>\<sigma>\<rangle>\<^sub>a \<lhd> b \<rhd> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<sigma> \<triangleleft> b \<triangleright> \<rho>\<rangle>\<^sub>a"
  by pred_auto  

text \<open>Extend the alphabet of a substitution\<close>

lemma assigns_subst: "(subst_aext \<sigma> fst\<^sub>L) \<dagger> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  by pred_auto

lemma assigns_r_comp: "(\<langle>\<sigma>\<rangle>\<^sub>a ;; P) = ((\<lambda> s. put\<^bsub>fst\<^sub>L\<^esub> s (\<sigma> (get\<^bsub>fst\<^sub>L\<^esub> s))) \<dagger> P)"
  by (pred_auto)

lemma assigns_r_feasible:
  "(\<langle>\<sigma>\<rangle>\<^sub>a ;; true) = true"
  by (pred_auto)

lemma assign_subst [usubst]:
  "\<lbrakk> vwb_lens x; vwb_lens y \<rbrakk> \<Longrightarrow>  [x\<^sup>> \<leadsto> u\<^sup><] \<dagger> (y := v) = (y, x) := ([x \<leadsto> u] \<dagger> v, u)"
  apply pred_auto
  oops

lemma assign_vacuous_skip:
  assumes "vwb_lens x"
  shows "(x := $x) = II"
  using assms by pred_auto

text \<open> The following law shows the case for the above law when $x$ is only mainly-well behaved. We
  require that the state is one of those in which $x$ is well defined using and assumption. \<close>

lemma assign_vacuous_assume:
  assumes "mwb_lens x"
  shows "\<questiondown>\<^bold>v \<in> \<guillemotleft>\<S>\<^bsub>x\<^esub>\<guillemotright>? ;; (x := $x) = \<questiondown>\<^bold>v \<in> \<guillemotleft>\<S>\<^bsub>x\<^esub>\<guillemotright>?"
  using assms by pred_auto

lemma assign_simultaneous:
  assumes "vwb_lens y" "x \<bowtie> y"
  shows "(x,y) := (e, $y) = (x := e)"
  using assms by pred_auto

lemma assigns_idem: "mwb_lens x \<Longrightarrow> (x,x) := (v,u) = (x := v)"
  by pred_auto

lemma assigns_r_conv:
  "bij f \<Longrightarrow> \<langle>f\<rangle>\<^sub>a\<^sup>- = \<langle>inv f\<rangle>\<^sub>a"
  by (pred_auto, simp_all add: bij_is_inj bij_is_surj surj_f_inv_f)

lemma assign_pred_transfer:
  assumes "vwb_lens x" "$x\<^sup>< \<sharp> b" "out\<alpha> \<sharp> b"
  shows "(b \<and> x := v) = (x := v \<and> b\<^sup>-)"
  using assms apply pred_auto oops
    
lemma assign_r_comp: "x := u ;; P = P\<lbrakk>u\<^sup></x\<^sup><\<rbrakk>"
  by pred_auto

lemma assign_test: "mwb_lens x \<Longrightarrow> (x := \<guillemotleft>u\<guillemotright> ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright>)"
  by pred_auto

lemma assign_twice: "\<lbrakk> mwb_lens x; $x \<sharp> f \<rbrakk> \<Longrightarrow> (x := e ;; x := f) = (x := f)"
  by pred_auto
 
lemma assign_commute:
  assumes "x \<bowtie> y" "$x \<sharp> f" "$y \<sharp> e" "vwb_lens x" "vwb_lens y"
  shows "(x := e ;; y := f) = (y := f ;; x := e)"
  using assms by (pred_auto add: lens_indep_comm)

lemma assign_cond:
  "(x := e ;; (P \<lhd> b \<rhd> Q)) = ((x := e ;; P) \<lhd> b\<lbrakk>e/x\<rbrakk> \<rhd> (x := e ;; Q))"
  by pred_auto

lemma assign_rcond:
  "(x := e ;; (P \<lhd> b \<rhd> Q)) = ((x := e ;; P) \<lhd> (b\<lbrakk>e/x\<rbrakk>) \<rhd> (x := e ;; Q))"
  by (pred_auto)

lemma assign_r_alt_def:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "x := v = II\<lbrakk>v\<^sup></x\<^sup><\<rbrakk>"
  by (pred_auto)

lemma assigns_r_func: "Functional \<langle>f\<rangle>\<^sub>a"
  unfolding Functional_def assigns_r_def single_valued_def pred_rel_def
  by simp

lemma assigns_r_injective: "inj f \<Longrightarrow> Injective \<langle>f\<rangle>\<^sub>a"
  unfolding Injective_def pred_rel_def injective_def 
  apply auto
    apply (metis Functional_def assigns_r_func pred_rel_def)
    apply (simp add: assigns_r_def injD)
  done

lemma assigns_r_swap_uinj:
  "\<lbrakk> vwb_lens x; vwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> Injective ((x,y) := ($y,$x))"
  using assigns_r_injective swap_subst_inj by blast

subsection \<open> Non-deterministic Assignment Laws \<close>

lemma ndet_assign_comp:
  "x \<bowtie> y \<Longrightarrow> x := * ;; y := * = (x,y) := *"
  by (pred_auto add: lens_indep.lens_put_comm)
  
lemma ndet_assign_assign:
  "\<lbrakk> vwb_lens x; $x \<sharp> e \<rbrakk> \<Longrightarrow> x := * ;; x := e = x := e"
  by pred_auto

lemma ndet_assign_refine:
  "x := * \<sqsubseteq> x := e"
  by pred_auto

subsection \<open> Converse Laws \<close>

lemma convr_invol [simp]: "p\<^sup>-\<^sup>- = p"
  by pred_auto

lemma not_convr [simp]: "(\<not> p)\<^sup>- = (\<not> p\<^sup>-)"
  by (pred_auto)

lemma disj_convr [simp]: "(p \<or> q)\<^sup>- = (q\<^sup>- \<or> p\<^sup>-)"
  by (pred_auto)

lemma conj_convr [simp]: "(p \<and> q)\<^sup>- = (q\<^sup>- \<and> p\<^sup>-)"
  by (pred_auto)

lemma seqr_convr [simp]: "(p ;; q)\<^sup>- = (q\<^sup>- ;; p\<^sup>-)"
  by (pred_auto)


lemma pre_convr [simp]: "p\<^sup><\<^sup>- = p\<^sup>>"
  by (pred_auto)

lemma post_convr [simp]: "p\<^sup>>\<^sup>- = p\<^sup><"
  by (pred_auto)

subsection \<open> Assertion and Assumption Laws \<close>
  
lemma assume_false: "\<questiondown>False? = false"
  by pred_auto
  
lemma assume_true: "\<questiondown>True? = II"
  by pred_auto
    
lemma assume_seq: "\<questiondown>b? ;; \<questiondown>c? = \<questiondown>b \<and> c?"
  by pred_auto

subsection \<open> While Loop Laws \<close>

theorem while_unfold:
  "while b do P od = ((P ;; while b do P od) \<lhd> b \<rhd> II)"
proof -
  have m:"mono (\<lambda>X. (P ;; X) \<lhd> b \<rhd> II)"
    by (simp add: cond_seqr_mono)
  have "(while b do P od) = (\<nu> X \<bullet> (P ;; X) \<lhd> b \<rhd> II)"
    by (simp add: while_top_def)
  also have "... = ((P ;; (\<nu> X \<bullet> (P ;; X) \<lhd> b \<rhd> II)) \<lhd> b \<rhd> II)"
    by (subst lfp_unfold, simp_all add: m)
  also have "... = ((P ;; while b do P od) \<lhd> b \<rhd> II)"
    by (simp add: while_top_def)
  finally show ?thesis .
qed

theorem while_false: "while False do P od = II"
  by (subst while_unfold, pred_auto)

theorem while_true: "while True do P od = false"
  apply (simp add: while_top_def alpha)
  apply (rule antisym)
  apply (rule lfp_lowerbound)
  apply (pred_auto)+
  done

theorem while_bot_unfold:
  "while\<^sub>\<bottom> b do P od = ((P ;; while\<^sub>\<bottom> b do P od) \<lhd> b \<rhd> II)"
proof -
  have m:"mono (\<lambda>X. (P ;; X) \<lhd> b \<rhd> II)"
    by (simp add: cond_seqr_mono)
  have "(while\<^sub>\<bottom> b do P od) = (\<mu> X \<bullet> (P ;; X) \<lhd> b \<rhd> II)"
    by (simp add: while_bot_def)
  also have "... = ((P ;; (\<mu> X \<bullet> (P ;; X) \<lhd> b \<rhd> II)) \<lhd> b \<rhd> II)"
    by (subst gfp_unfold, simp_all add: m)
  also have "... = ((P ;; while\<^sub>\<bottom> b do P od) \<lhd> b \<rhd> II)"
    by (simp add: while_bot_def)
  finally show ?thesis .
qed

theorem while_bot_false: "while\<^sub>\<bottom> False do P od = II"
  by (pred_auto add: while_bot_def gfp_const)

theorem while_bot_true: "while\<^sub>\<bottom> True do P od = (\<mu> X \<bullet> P ;; X)"
  by (simp add: while_bot_def alpha)

text \<open> An infinite loop with a feasible body corresponds to a program error (non-termination). \<close>

theorem while_infinite: "P ;; true = true \<Longrightarrow> while\<^sub>\<bottom> True do P od = true"
  apply (rule antisym)
   apply (simp add: true_pred_def)
    apply (pred_auto add: gfp_upperbound while_bot_true)
  apply (metis feasible_iff_true_right_zero gfp_upperbound order_refl while_bot_true)
  done

subsection \<open> Algebraic Properties \<close>

interpretation upred_semiring: semiring_1 
  where times = "(;;\<^sub>h)" and one = "skip" and zero = "false\<^sub>h" and plus = "Lattices.sup"
  by (unfold_locales; pred_auto+)

declare upred_semiring.power_Suc [simp del]

text \<open> We introduce the power syntax derived from semirings \<close>

unbundle utp_lattice_syntax

subsection \<open> Relational Power \<close>

lemma upower_interp [rel]: "\<lbrakk>P \<^bold>^ i\<rbrakk>\<^sub>U = \<lbrakk>P\<rbrakk>\<^sub>U ^^ i"
  by (induct i arbitrary: P)
     ((auto; pred_auto add: pred_rel_def), simp add: rel_interp(1) upred_semiring.power_Suc2)

lemma Sup_power_expand:
  fixes P :: "nat \<Rightarrow> 'a::complete_lattice"
  shows "P(0) \<sqinter> (\<Sqinter>i. P(i+1)) = (\<Sqinter>i. P(i))"
proof -
  have "UNIV = insert (0::nat) {1..}"
    by auto
  moreover have "(\<Sqinter>i. P(i)) = \<Sqinter> (P ` UNIV)"
    by (blast)
  moreover have "\<Sqinter> (P ` insert 0 {1..}) = P(0) \<sqinter> \<Sqinter> (P ` {1..})"
    by (simp)
  moreover have "\<Sqinter> (P ` {1..}) = (\<Sqinter>i. P(i+1))"
    by (simp add: atLeast_Suc_greaterThan greaterThan_0 image_image)
  ultimately show ?thesis
    by (simp only:)
qed

lemma Sup_upto_Suc: "(\<Sqinter>i\<in>{0..Suc n}. P \<^bold>^ i) = (\<Sqinter>i\<in>{0..n}. P \<^bold>^ i) \<sqinter> P \<^bold>^ Suc n"
proof -
  have "(\<Sqinter>i\<in>{0..Suc n}. P \<^bold>^ i) = (\<Sqinter>i\<in>insert (Suc n) {0..n}. P \<^bold>^ i)"
    by (simp add: atLeast0_atMost_Suc)
  also have "... = P \<^bold>^ Suc n \<sqinter> (\<Sqinter>i\<in>{0..n}. P \<^bold>^ i)"
    by (simp)
  finally show ?thesis
    by (simp add: Lattices.sup_commute)
qed

text \<open> The following two proofs are adapted from the AFP entry 
  \href{https://www.isa-afp.org/entries/Kleene_Algebra.shtml}{Kleene Algebra}. 
  See also~\cite{Armstrong2012,Armstrong2015}. \<close>

lemma upower_inductl: 
  assumes "Q \<sqsubseteq> ((P ;; Q) \<sqinter> R)"
  shows "Q \<sqsubseteq> P \<^bold>^ n ;; R"
proof (induct n)
  case 0
  with assms show ?case by rel_simp
next
  case (Suc n)
  with assms show ?case
    by (rel_transfer)
       (metis (no_types, lifting) O_assoc le_iff_sup relcomp_distrib relpow.simps(2) relpow_commute sup.coboundedI1)
qed

lemma upower_inductr:
  assumes "Q \<sqsubseteq> R \<sqinter> (Q ;; P)"
  shows "Q \<sqsubseteq> R ;; (P \<^bold>^ n)"
proof (induct n)
  case 0
  with assms show ?case by auto
next
  case (Suc n)
  with assms show ?case 
    by (rel_transfer)
       (metis (no_types, lifting) O_assoc le_supE relcomp_distrib2 relpow.simps(2) sup.order_iff)
qed

lemma SUP_atLeastAtMost_first:
  fixes P :: "nat \<Rightarrow> 'a::complete_lattice"
  assumes "m \<le> n"
  shows "(\<Sqinter>i\<in>{m..n}. P(i)) = P(m) \<sqinter> (\<Sqinter>i\<in>{Suc m..n}. P(i))"
  by (metis SUP_insert assms atLeastAtMost_insertL)

lemma upower_seqr_iter: "P \<^bold>^ n = (;; Q : replicate n P \<bullet> Q)"
  by (induct n, simp_all add: power.power.power_Suc)

subsection \<open> Relation Algebra Laws \<close>

theorem seqr_disj_cancel: "((P\<^sup>- ;; (\<not>(P ;; Q))) \<or> (\<not>Q)) = (\<not>Q)"
  by pred_auto

subsection \<open> Kleene Algebra Laws \<close>

lemma ustar_rep_eq [rel]: "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U = \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*"
proof 
  have "((a, b) \<in> \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*) \<Longrightarrow> (a,b) \<in> \<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U" for a b
    apply (induct rule: rtrancl.induct)
     apply (simp_all add: pred_rel_def ustar_def)
     apply (metis (full_types) power.power.power_0 prod.simps(2) skip_def)
    apply (metis (mono_tags, lifting) case_prodI upred_semiring.power_Suc2 utp_rel.seq_def)
    done
  then show "\<lbrakk>P\<rbrakk>\<^sub>U\<^sup>* \<subseteq> \<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U"
    by auto
next
  have "((a, b) \<in> \<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U) \<Longrightarrow> (a,b) \<in> \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*" for a b
    apply (simp add: ustar_def pred_rel_def)
    apply (metis mem_Collect_eq pred_rel_def rtrancl_power upower_interp)
    done
  then show "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U \<subseteq> \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*"
    by force
qed

theorem ustar_sub_unfoldl: "P\<^sup>\<star> \<sqsubseteq> II \<sqinter> (P;;P\<^sup>\<star>)"
  by rel_auto

theorem ustar_inductl:
  assumes "Q \<sqsubseteq> R" "Q \<sqsubseteq> P ;; Q"
  shows "Q \<sqsubseteq> P\<^sup>\<star> ;; R"
proof -
  have "P\<^sup>\<star> ;; R = (\<Sqinter> i. P \<^bold>^ i ;; R)"
    by (simp add: seq_SUP_distr ustar_def)
  also have "Q \<sqsubseteq> ..."
    by (simp add: assms ref_lattice.INF_greatest upower_inductl)
  finally show ?thesis .
qed

theorem ustar_inductr:
  assumes "Q \<sqsubseteq> R" "Q \<sqsubseteq> Q ;; P"
  shows "Q \<sqsubseteq> R ;; P\<^sup>\<star>"
proof -
  have "R ;; P\<^sup>\<star> = (\<Sqinter> i. R ;; P \<^bold>^ i)"
    by (simp add: seq_SUP_distl ustar_def)
  also have "Q \<sqsubseteq> ..."
    by (simp add: assms ref_lattice.INF_greatest upower_inductr)
  finally show ?thesis .
qed

lemma ustar_refines_nu: "(\<nu> X \<bullet> (P ;; X) \<sqinter> II) \<sqsubseteq> P\<^sup>\<star>"
proof (rule ustar_inductl[where R="II", simplified])
  show "(\<nu> X \<bullet> (P ;; X) \<sqinter> II) \<sqsubseteq> II"
    by (simp add: ref_by_pred_is_leq, metis le_supE lfp_greatest)
  show "(\<nu> X \<bullet> (P ;; X) \<sqinter> II) \<sqsubseteq> P ;; (\<nu> X \<bullet> (P ;; X) \<sqinter> II)" (is "?lhs \<sqsubseteq> ?rhs")
  proof -
    have "?lhs = (P ;; (\<nu> X \<bullet> (P ;; X) \<sqinter> II)) \<sqinter> II"
      by (rule lfp_unfold, simp add: mono)
    also have "... \<sqsubseteq> ?rhs" by simp
    finally show ?thesis .
  qed
qed

lemma ustar_as_nu: "P\<^sup>\<star> = (\<nu> X \<bullet> (P ;; X) \<sqinter> II)"
proof (rule ref_antisym)
  show "(\<nu> X \<bullet> (P ;; X) \<sqinter> II) \<sqsubseteq> P\<^sup>\<star>"
    by (simp add: ustar_refines_nu)
  show "P\<^sup>\<star> \<sqsubseteq> (\<nu> X \<bullet> (P ;; X) \<sqinter> II)"
    by (metis lfp_lowerbound pred_ref_iff_le sup_commute ustar_sub_unfoldl) 
qed

lemma ustar_unfoldl: "P\<^sup>\<star> = II \<sqinter> (P ;; P\<^sup>\<star>)"
  by (rel_auto, meson converse_rtranclE)

lemma nth_rtrancl_path:
"\<lbrakk> \<forall> i < length xs. R ((x # xs) ! i) (xs ! i); y = List.last (x # xs) \<rbrakk> \<Longrightarrow> rtrancl_path R x xs y"
  by (induct xs arbitrary: x y, auto simp add: rtrancl_path.base rtrancl_path.step)
     (metis Suc_less_eq nth_Cons_0 nth_Cons_Suc rtrancl_path.step zero_less_Suc)

lemma rtrancl_path_nth_iff: 
  "rtrancl_path R x xs y \<longleftrightarrow> ((\<forall> i < length xs. R ((x # xs) ! i) (xs ! i)) \<and> y = List.last (x # xs))"
  by (metis neq_Nil_conv nth_rtrancl_path rtrancl_path.cases rtrancl_path_last rtrancl_path_nth)

lemma ustar_pred: 
  "(P\<^sup>\<star>) (x, y) = (\<lambda> x y. P (x, y))\<^sup>*\<^sup>* x y"
proof -
  have "(P\<^sup>\<star>) (x, y) \<longleftrightarrow> (x, y) \<in> \<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U"
    by (simp add: pred_rel_def)
  also have "... = ((x, y) \<in> \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*)"
    by (simp add: ustar_rep_eq)
  also have "... = (\<lambda> x y. P (x, y))\<^sup>*\<^sup>* x y"
    by (simp add: Enum.rtranclp_rtrancl_eq pred_rel_def)
  finally show ?thesis .
qed

lemma ustar_chain_pred: 
  "P\<^sup>\<star> = (\<lambda> (a, b). a = b \<or> (\<exists> xs. xs \<noteq> [] \<and> (\<forall>i. i < length xs \<longrightarrow> P ((a # xs) ! i, xs ! i)) \<and> b = List.last xs))" 
  by (pred_simp add: ustar_pred, auto simp add: pred rtranclp_eq_rtrancl_path rtrancl_path_nth_iff)

lemma ustar_chain_pred': 
  "(P\<^sup>\<star>) (a, b) = (a = b \<or> (\<exists> xs. xs \<noteq> [] \<and> (\<forall>i. i < length xs \<longrightarrow> P ((a # xs) ! i, xs ! i)) \<and> b = List.last xs))"
  by (simp add: ustar_chain_pred)

text \<open> While loop can be expressed using Kleene star \<close>

lemma while_star_form:
  "while b do P od = (P \<lhd> b \<rhd> II)\<^sup>\<star> ;; \<questiondown>(\<not>b)?"
proof -
  have 1: "Continuous (\<lambda>X. P ;; X \<lhd> b \<rhd> II)"
    by (pred_auto)
  have "while b do P od = (\<Sqinter>i. ((\<lambda>X. P ;; X \<lhd> b \<rhd> II) ^^ i) false)"
    by (simp add: "1" sup_continuous_Continuous sup_continuous_lfp while_top_def top_false)
  also have "... = ((\<lambda>X. P ;; X \<lhd> b \<rhd> II) ^^ 0) false \<sqinter> (\<Sqinter>i. ((\<lambda>X. P ;; X \<lhd> b \<rhd> II) ^^ (i+1)) false)"
    by (subst Sup_power_expand, simp)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; X \<lhd> b \<rhd> II) ^^ (i+1)) false)"
    by (simp)
  also have "... = (\<Sqinter>i. (P \<lhd> b \<rhd> II)\<^bold>^i ;; (false \<lhd> b \<rhd> II))"
  proof (rule SUP_cong, simp_all)
    fix i
    show "P ;; ((\<lambda>X. P ;; X \<lhd> b \<rhd> II) ^^ i) false \<lhd> b \<rhd> II = (P \<lhd> b \<rhd> II) \<^bold>^ i ;; (false \<lhd> b \<rhd> II)"
    proof (induct i)
      case 0
      then show ?case by simp
    next
      case (Suc i)
      then show ?case
        by (simp add: upred_semiring.power_Suc)
           (metis (no_types, lifting) SEXP_def rcomp_rcond_left_distr rcond_reach seqr_assoc seqr_left_unit)
    qed
  qed
  also have "... = (\<Sqinter>i\<in>{0..}. (P \<lhd> b \<rhd> II)\<^bold>^i ;; \<questiondown>\<not>b?)"
    by (pred_auto)
  also have "... = (P \<lhd> b \<rhd> II)\<^sup>\<star> ;; \<questiondown>\<not>b?"
    by (simp add: seq_SUP_distr ustar_def)
  finally show ?thesis .
qed

lemma while_star_test_form:
  "while b do P od = (\<questiondown>b? ;; P)\<^sup>\<star> ;; \<questiondown>\<not>b?"
  apply (pred_auto add: while_star_form ustar_pred)
  apply (force elim:rtranclp_induct simp add: rtranclp.rtrancl_into_rtrancl)+
  done

lemma while_chain_form:
 "while b do P od = 
    (\<lambda> (s, s'). ((s = s' \<or> 
                  (\<exists>xs. xs \<noteq> [] \<and> (\<forall>i. i < length xs \<longrightarrow> b ((s # xs) ! i) \<and> P ((s # xs) ! i, xs ! i)) \<and> s' = List.last xs)) \<and>
                 \<not> b s'))"
  by (simp add: while_star_test_form, pred_simp add: ustar_chain_pred')


subsection \<open> Refinement Laws \<close>

lemma skip_r_refine: "(p \<longrightarrow> p) \<sqsubseteq> II"
  by pred_auto

lemma conj_refine_left: "(Q \<longrightarrow> (P :: 'a pred)) \<sqsubseteq> R \<Longrightarrow> P \<sqsubseteq> (Q \<and> R)"
  by pred_auto

lemma pre_weak_rel:
  assumes "`p \<longrightarrow> I`"
  and     "(I \<longrightarrow> q)\<^sub>e \<sqsubseteq> P"
  shows "(p \<longrightarrow> q)\<^sub>e \<sqsubseteq> P"
  using assms by pred_auto



lemma cond_refine_rel: 
  assumes "S \<sqsubseteq> (b\<^sup>< \<and> P)" "S \<sqsubseteq> ((\<not>b)\<^sup>< \<and> Q)"
  shows "S \<sqsubseteq> P \<lhd> b \<rhd> Q"
  using assms by (pred_auto)

lemma seq_refine_pred:
  assumes "(b\<^sup>< \<longrightarrow> s\<^sup>>) \<sqsubseteq> P" and "(s\<^sup>< \<longrightarrow> c\<^sup>>) \<sqsubseteq> Q"
  shows "(b\<^sup>< \<longrightarrow> c\<^sup>>) \<sqsubseteq> (P ;; Q)"
  using assms by pred_auto
    
lemma seq_refine_unrest:
  assumes "out\<alpha> \<sharp> b" "in\<alpha> \<sharp> c"
  assumes "(b \<longrightarrow> s\<^sup>>) \<sqsubseteq> P" and "(s\<^sup>< \<longrightarrow> c) \<sqsubseteq> Q"
  shows "(b \<longrightarrow> c) \<sqsubseteq> (P ;; Q)"
  using assms by (pred_simp, blast)
    
subsection \<open> Pre and Post Laws \<close>

named_theorems prepost

lemma pre_conv_post [prepost]:
  "pre(P\<^sup>-) = post(P)"
  by (pred_auto)

lemma post_conv_pre [prepost]:
  "post(P\<^sup>-) = pre(P)"
  by (pred_auto)  

lemma pre_skip [prepost]:
  "pre(II) = true"
  by (pred_auto)

lemma pre_assigns [prepost]:
  "pre(\<langle>\<sigma>\<rangle>\<^sub>a) = true"
  by (pred_auto)
   
lemma pre_miracle [prepost]:
  "pre(false) = false"
  by (pred_auto)

lemma pre_assume [prepost]:
  "pre(\<questiondown>b?) = b"
  by (pred_auto)
    
lemma pre_seq:
  "pre(P ;; Q) = pre(P ;; \<questiondown>pre(Q)?)"
  by (pred_auto)
    
lemma pre_disj [prepost]:
  "pre(P \<or> Q) = (pre(P) \<or> pre(Q))"
  by pred_auto

lemma pre_inf [prepost]:
  "pre(P \<sqinter> Q) = (pre(P) \<or> pre(Q))"
  by (pred_auto)

lemma assume_Pre [prepost]:
  "\<questiondown>pre(P)? ;; P = P"
  by (pred_auto)

end
