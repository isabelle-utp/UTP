section \<open> Relational Calculus Laws \<close>

theory utp_rel_laws
  imports 
    utp_rel
    utp_recursion
    utp_healthy
begin

section \<open> Conditional Laws \<close>

lemma cond_idem [simp]: "P \<lhd> b \<rhd> P = P"
  by pred_auto

lemma cond_sym: "P \<lhd> b \<rhd> Q = Q \<lhd> \<not>b \<rhd> P"
  by pred_auto

lemma cond_assoc: "(P \<lhd> b \<rhd> Q) \<lhd> c \<rhd> R = P \<lhd> b \<and> c \<rhd> (Q \<lhd> c \<rhd> R)"
  by pred_auto

lemma cond_distr: "P \<lhd> b \<rhd> (Q \<lhd> c \<rhd> R) = (P \<lhd> b \<rhd> Q) \<lhd> c \<rhd> (P \<lhd> b \<rhd> R)"
  by pred_auto

lemma cond_true [simp]: "P \<lhd> True \<rhd> Q = P"
  by pred_auto

lemma cond_false [simp]: "P \<lhd> False \<rhd> Q = Q"
  by pred_auto

lemma cond_reach [simp]: "P \<lhd> b \<rhd> (Q \<lhd> b \<rhd> R) = P \<lhd> b \<rhd> R"
  by pred_auto

lemma cond_disj [simp]: "P \<lhd> b \<rhd> (P \<lhd> c \<rhd> Q) = P \<lhd> b \<or> c \<rhd> Q"
  by pred_auto

lemma comp_rcond_left_distr:
  "(P \<^bold>\<lhd> b \<^bold>\<rhd> Q) ;; R = (P ;; R) \<^bold>\<lhd> b \<^bold>\<rhd> (Q ;; R) "
  by (pred_auto)

lemma cond_seq_left_distr:
  "out\<alpha> \<sharp> b \<Longrightarrow> ((P \<lhd> b \<rhd> Q) ;; R) = ((P ;; R) \<lhd> b \<rhd> (Q ;; R))"
  by (pred_auto, blast)

lemma cond_seq_right_distr:
  "in\<alpha> \<sharp> b \<Longrightarrow> (P ;; (Q \<lhd> b \<rhd> R)) = ((P ;; Q) \<lhd> b \<rhd> (P ;; R))"
  by (pred_auto, blast)

text \<open> Alternative expression of conditional using assumptions and choice \<close>

lemma rcond_rassume_expand: "P \<^bold>\<lhd> b \<^bold>\<rhd> Q = (\<questiondown>b? ;; P) \<sqinter> (\<questiondown>(\<not> b)? ;; Q)"
  by pred_auto

lemma rcond_mono [mono]: "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<^bold>\<lhd> b \<^bold>\<rhd> Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 \<^bold>\<lhd> b \<^bold>\<rhd> Q\<^sub>2)"
  by (pred_auto)

lemma rcond_refine: "(P \<sqsubseteq> (Q \<lhd> b \<rhd> R)) = (P \<sqsubseteq> (b \<and> Q)\<^sub>e \<and> (P \<sqsubseteq> ((\<not>b \<and> R)\<^sub>e)))"
  by (pred_auto)

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

(*theorem feasibile_iff_true_right_zero:
  "P ;; true = true \<longleftrightarrow> (\<exists> out\<alpha> \<bullet> P)\<^sub>e"
  oops*)
    
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
  
lemma cond_seqr_mono [mono]: "mono (\<lambda>X. (P ;; X) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
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
  shows "(P \<lhd> $x\<^sup>> \<rhd> Q) ;; R = (P\<lbrakk>True/x\<^sup>>\<rbrakk> ;; R\<lbrakk>True/x\<^sup><\<rbrakk> \<or> Q\<lbrakk>False/x\<^sup>>\<rbrakk> ;; R\<lbrakk>False/x\<^sup><\<rbrakk>)"
proof -
  have "(P \<lhd> $x\<^sup>> \<rhd> Q) ;; R = (((x\<^sup>>)\<^sub>e \<and> P) ;; R \<or> (\<not> (x\<^sup>>)\<^sub>e \<and> Q) ;; R)"
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

(*
lemma shEx_mem_lift_seq_1 [uquant_lift]:
  assumes "out\<alpha> \<sharp> A"
  shows "((\<^bold>\<exists> x \<in> A \<bullet> P x) ;; Q) = (\<^bold>\<exists> x \<in> A \<bullet> (P x ;; Q))"
  using assms by rel_blast

lemma shEx_lift_seq_2 [uquant_lift]:
  "(P ;; (\<^bold>\<exists> x \<bullet> Q x)) = (\<^bold>\<exists> x \<bullet> (P ;; Q x))"
  by pred_auto

lemma shEx_mem_lift_seq_2 [uquant_lift]:
  assumes "in\<alpha> \<sharp> A"
  shows "(P ;; (\<^bold>\<exists> x \<in> A \<bullet> Q x)) = (\<^bold>\<exists> x \<in> A \<bullet> (P ;; Q x))"
  using assms by rel_blast*)

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

(*
text \<open>Liberate currently doesn't work on relations - it expects a lens of type 'a instead of 'a \<times> 'a\<close>
lemma skip_r_unfold:
  "vwb_lens x \<Longrightarrow> II = (($x\<^sup>> = $x\<^sup><)\<^sub>e \<and> II \\ $x)"
  by (rel_simp, metis mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put)
*)

lemma skip_r_alpha_eq:
  "II = (\<^bold>v\<^sup>< = \<^bold>v\<^sup>>)\<^sub>e"
  by (pred_auto)

(*
lemma skip_ra_unfold:
  "II\<^bsub>x;y\<^esub> = ($x\<acute> =\<^sub>u $x \<and> II\<^bsub>y\<^esub>)"
  by (pred_auto)

lemma skip_res_as_ra:
  "\<lbrakk> vwb_lens y; x +\<^sub>L y \<approx>\<^sub>L 1\<^sub>L; x \<bowtie> y \<rbrakk> \<Longrightarrow> II\<restriction>\<^sub>\<alpha>x = II\<^bsub>y\<^esub>"
  apply (pred_auto)
   apply (metis (no_types, lifting) lens_indep_def)
  apply (metis vwb_lens.put_eq)
  done
*)

subsection \<open> Assignment Laws \<close>

lemma assigns_skip: "\<langle>id\<rangle>\<^sub>a = II"
  by pred_auto

lemma assigns_comp: "\<langle>\<sigma>\<rangle>\<^sub>a ;; \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  by pred_auto

lemma assigns_cond: "\<langle>\<sigma>\<rangle>\<^sub>a \<^bold>\<lhd> b \<^bold>\<rhd> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<sigma> \<triangleleft> b \<triangleright> \<rho>\<rangle>\<^sub>a"
  by pred_auto  

text \<open>Extend the alphabet of a substitution\<close>

definition subst_aext :: "'a subst \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'b subst"
  where [rel]: "subst_aext \<sigma> x = (\<lambda> s. put\<^bsub>x\<^esub> s (\<sigma> (get\<^bsub>x\<^esub> s)))"

lemma assigns_subst: "(subst_aext \<sigma> fst\<^sub>L) \<dagger> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  apply pred_auto
  by (simp_all add: utp_rel_laws.subst_aext_def)

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

(*
lemma assign_vacuous_assume:
  assumes "mwb_lens x"
  shows "[&\<^bold>v \<in> \<guillemotleft>\<S>\<^bsub>x\<^esub>\<guillemotright>]\<^sup>\<top> ;; (x := &x) = [&\<^bold>v \<in> \<guillemotleft>\<S>\<^bsub>x\<^esub>\<guillemotright>]\<^sup>\<top>"
  using assms by pred_auto *)

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
  assumes "$x\<^sup>< \<sharp> b" "out\<alpha> \<sharp> b"
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
  "(x := e ;; (P \<^bold>\<lhd> b \<^bold>\<rhd> Q)) = ((x := e ;; P) \<^bold>\<lhd> b\<lbrakk>e/x\<rbrakk> \<^bold>\<rhd> (x := e ;; Q))"
  by pred_auto

lemma assign_rcond:
  "(x := e ;; (P \<^bold>\<lhd> b \<^bold>\<rhd> Q)) = ((x := e ;; P) \<^bold>\<lhd> (b\<lbrakk>e/x\<rbrakk>) \<^bold>\<rhd> (x := e ;; Q))"
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
(*
lemma assigns_r_swap_uinj:
  "\<lbrakk> vwb_lens x; vwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> (x,y) := (y,x)"
  by (metis assigns_r_uinj pr_var_def swap_usubst_inj)

lemma assign_unfold:
  "vwb_lens x \<Longrightarrow> (x := v) = (x\<^sup>> = v\<^sup><)"
  apply (pred_auto, auto simp add: comp_def)
  using vwb_lens.put_eq by fastforce*)

subsection \<open> Non-deterministic Assignment Laws \<close>

(*
lemma ndet_assign_comp:
  "x \<bowtie> y \<Longrightarrow> x := * ;; y := * = (x,y) := *"
  by (pred_auto add: lens_indep.lens_put_comm)
  
lemma ndet_assign_assign:
  "\<lbrakk> vwb_lens x; $x \<sharp> e \<rbrakk> \<Longrightarrow> x := * ;; x := e = x := e"
  by pred_auto

lemma ndet_assign_refine:
  "x := * \<sqsubseteq> x := e"
  by pred_auto
*)

subsection \<open> Converse Laws \<close>

lemma convr_invol [simp]: "p\<^sup>-\<^sup>- = p"
  by pred_auto
(*
lemma lit_convr [simp]: "(\<guillemotleft>v\<guillemotright>)\<^sup>- = \<guillemotleft>v\<guillemotright>"
  by pred_auto

lemma uivar_convr [simp]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "($x\<^sup><)\<^sup>- = $x\<^sup>>"
  by pred_auto

lemma uovar_convr [simp]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "($x\<acute>)\<^sup>- = $x"
  by pred_auto

lemma uop_convr [simp]: "(uop f u)\<^sup>- = uop f (u\<^sup>-)"
  by (pred_auto)

lemma bop_convr [simp]: "(bop f u v)\<^sup>- = bop f (u\<^sup>-) (v\<^sup>-)"
  by (pred_auto)

lemma eq_convr [simp]: "(p = q)\<^sup>- = (p\<^sup>- = q\<^sup>-)"
  by (pred_auto)
*)

lemma not_convr [simp]: "(\<not> p)\<^sup>- = (\<not> p\<^sup>-)"
  by (pred_auto)


lemma disj_convr [simp]: "(p \<or> q)\<^sup>- = (q\<^sup>- \<or> p\<^sup>-)"
  by (pred_auto)

lemma conj_convr [simp]: "(p \<and> q)\<^sup>- = (q\<^sup>- \<and> p\<^sup>-)"
  by (pred_auto)

lemma seqr_convr [simp]: "(p ;; q)\<^sup>- = (q\<^sup>- ;; p\<^sup>-)"
  by (pred_auto)

(*
lemma pre_convr [simp]: "\<lceil>p\<rceil>\<^sub><\<^sup>- = \<lceil>p\<rceil>\<^sub>>"
  by (pred_auto)

lemma post_convr [simp]: "\<lceil>p\<rceil>\<^sub>>\<^sup>- = \<lceil>p\<rceil>\<^sub><"
  by (pred_auto)*)

subsection \<open> Assertion and Assumption Laws \<close>

(*
declare sublens_def [lens_defs del]
  
lemma assume_false: "\<questiondown>false? = false"
  by (pred_auto)
  
lemma assume_true: "\<questiondown>true? = II"
  by (pred_auto)
    
lemma assume_seq: "\<questiondown>b? ;; \<questiondown>c? = \<questiondown>b \<and> c?"
  by (pred_auto)

(*
lemma assert_false: "{false}\<^sub>\<bottom> = true"
  by (pred_auto)

lemma assert_true: "{true}\<^sub>\<bottom> = II"
  by (pred_auto)
    
lemma assert_seq: "{b}\<^sub>\<bottom> ;; {c}\<^sub>\<bottom> = {(b \<and> c)}\<^sub>\<bottom>"
  by (pred_auto)*)

subsection \<open> While Loop Laws \<close>

theorem while_unfold:
  "while b do P od = ((P ;; while b do P od) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
proof -
  have m:"mono (\<lambda>X. (P ;; X) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    unfolding mono_def by (meson equalityE rcond_mono ref_by_def relcomp_mono)
  have "(while b do P od) = (\<nu> X \<bullet> (P ;; X) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: while_top_def)
  also have "... = ((P ;; (\<nu> X \<bullet> (P ;; X) \<^bold>\<lhd> b \<^bold>\<rhd> II)) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (subst lfp_unfold, simp_all add: m)
  also have "... = ((P ;; while b do P od) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: while_top_def)
  finally show ?thesis .
qed

theorem while_false: "while (false)\<^sub>e do P od = II"
  by (subst while_unfold, pred_auto)

theorem while_true: "while (true)\<^sub>e do P od = false"
  apply (simp add: while_top_def alpha)
  apply (rule antisym)
  apply (rule lfp_lowerbound)
  apply (pred_auto)+
  done

theorem while_bot_unfold:
  "while\<^sub>\<bottom> b do P od = ((P ;; while\<^sub>\<bottom> b do P od) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
proof -
  have m:"mono (\<lambda>X. (P ;; X) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    unfolding mono_def by (meson equalityE rcond_mono ref_by_def relcomp_mono)
  have "(while\<^sub>\<bottom> b do P od) = (\<mu> X \<bullet> (P ;; X) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: while_bot_def)
  also have "... = ((P ;; (\<mu> X \<bullet> (P ;; X) \<^bold>\<lhd> b \<^bold>\<rhd> II)) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (subst gfp_unfold, simp_all add: m)
  also have "... = ((P ;; while\<^sub>\<bottom> b do P od) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: while_bot_def)
  finally show ?thesis .
qed

theorem while_bot_false: "while\<^sub>\<bottom> (false)\<^sub>e do P od = II"
  by (pred_auto add: while_bot_def gfp_const)

theorem while_bot_true: "while\<^sub>\<bottom> (true)\<^sub>e do P od = (\<mu> X \<bullet> P ;; X)"
  by (pred_auto add: while_bot_def)

text \<open> An infinite loop with a feasible body corresponds to a program error (non-termination). \<close>

theorem while_infinite: "P ;; true = true \<Longrightarrow> while\<^sub>\<bottom> (true)\<^sub>e do P od = true"
  apply (rule antisym)
   apply (simp add: true_pred_def)
    apply (pred_auto add: gfp_upperbound while_bot_true)
  done

subsection \<open> Algebraic Properties \<close>

interpretation upred_semiring: semiring_1 
  where times = "(;;)" and one = Id and zero = false_pred and plus = "Lattices.sup"
  by (unfold_locales; pred_auto+)

declare upred_semiring.power_Suc [simp del]

text \<open> We introduce the power syntax derived from semirings \<close>

text \<open> Set up transfer tactic for powers \<close>
unbundle utp_lattice_syntax

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
    sorry
  ultimately show ?thesis
    by simp
qed
*)
(*
lemma Sup_upto_Suc: "(\<Sqinter>i\<in>{0..Suc n}. P \<^bold>^ i) = (\<Sqinter>i\<in>{0..n}. P \<^bold>^ i) \<sqinter> P \<^bold>^ Suc n"
proof -
  have "(\<Sqinter>i\<in>{0..Suc n}. P \<^bold>^ i) = (\<Sqinter>i\<in>insert (Suc n) {0..n}. P \<^bold>^ i)"
    by (simp add: atLeast0_atMost_Suc)
  also have "... = P \<^bold>^ Suc n \<sqinter> (\<Sqinter>i\<in>{0..n}. P \<^bold>^ i)"
    by (simp)
  finally show ?thesis
    by (simp add: Lattices.sup_commute)
qed
*)

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

thm rel_transfer

thm inf_fun_def

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

subsection \<open> Omega \<close>

(*
definition uomega :: "'\<alpha> rel \<Rightarrow> '\<alpha> rel" ("_\<^sup>\<omega>" [999] 999) where
"P\<^sup>\<omega> = (\<mu> X \<bullet> P ;; X)"

subsection \<open> Relation Algebra Laws \<close>

theorem seqr_disj_cancel: "((P\<^sup>- ;; (\<not>(P ;; Q))) \<or> (\<not>Q)) = (\<not>Q)"
  by (pred_auto)
*)

subsection \<open> Kleene Algebra Laws \<close>

lemma ustar_rep_eq [rel]: "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U = \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*"
proof 
  have "((a, b) \<in> \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*) \<Longrightarrow> (a,b) \<in> \<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U" for a b
    apply (induct rule: rtrancl.induct)
     apply (simp_all add: pred_rel_def ustar_def)
     apply (metis (full_types) power.power.power_0 prod.simps(2) skip_def)
    by (metis (mono_tags, lifting) case_prodI upred_semiring.power_Suc2 utp_rel.seq_def)
  then show "\<lbrakk>P\<rbrakk>\<^sub>U\<^sup>* \<subseteq> \<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U"
    by auto
next
  have "((a, b) \<in> \<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U) \<Longrightarrow> (a,b) \<in> \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*" for a b
    apply (simp add: ustar_def pred_rel_def)
    by (metis mem_Collect_eq pred_rel_def rtrancl_power upower_interp)
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


text \<open> While loop can be expressed using Kleene star \<close>

(*
lemma while_star_form:
  "while b do P od = (P \<^bold>\<lhd> b \<^bold>\<rhd> II)\<^sup>\<star> ;; \<questiondown>(\<not>b)?"
proof -
  have 1: "Continuous (\<lambda>X. P ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (pred_auto)
  have "while b do P od = (\<Sqinter>i. ((\<lambda>X. P ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II) ^^ i) false)"
    by (simp add: "1" sup_continuous_Continuous sup_continuous_lfp while_top_def top_false)
  also have "... = ((\<lambda>X. P ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II) ^^ 0) false \<sqinter> (\<Sqinter>i. ((\<lambda>X. P ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II) ^^ (i+1)) false)"
    by (subst Sup_power_expand, simp)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II) ^^ (i+1)) false)"
    by (simp)
  also have "... = (\<Sqinter>i. (P \<^bold>\<lhd> b \<^bold>\<rhd> II)\<^bold>^i ;; (false \<^bold>\<lhd> b \<^bold>\<rhd> II))"
  proof (rule SUP_cong, simp_all)
    fix i
    show "P ;; ((\<lambda>X. P ;; X \<^bold>\<lhd> b \<^bold>\<rhd> II) ^^ i) false \<^bold>\<lhd> b \<^bold>\<rhd> II = (P \<^bold>\<lhd> b \<^bold>\<rhd> II) \<^bold>^ i ;; (false \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    proof (induct i)
      case 0
      then show ?case by simp
    next
      case (Suc i)
      then show ?case
        apply (simp only: upred_semiring.power_Suc)
    qed
  qed
  also have "... = (\<Sqinter>i\<in>{0..} \<bullet> (P \<^bold>\<lhd> b \<^bold>\<rhd> II)\<^bold>^i ;; [(\<not>b)]\<^sup>\<top>)"
    by (pred_auto)
  also have "... = (P \<^bold>\<lhd> b \<^bold>\<rhd> II)\<^sup>\<star> ;; [(\<not>b)]\<^sup>\<top>"
    by (metis seq_UINF_distr ustar_def)
  finally show ?thesis .
qed
*)
  
subsection \<open> Omega Algebra Laws \<close>

(*
lemma uomega_induct: "P ;; P\<^sup>\<omega> \<sqsubseteq> P\<^sup>\<omega>"
  by (metis gfp_unfold monoI ref_by_set_def relcomp_mono subset_refl uomega_def)

subsection \<open> Refinement Laws \<close>

lemma skip_r_refine: "(p \<Rightarrow> p) \<sqsubseteq> II"
  by pred_auto

lemma conj_refine_left: "(Q \<Rightarrow> P) \<sqsubseteq> R \<Longrightarrow> P \<sqsubseteq> (Q \<and> R)"
  by (pred_auto)

lemma pre_weak_rel:
  assumes "`p \<longrightarrow> I`"
  and     "(I \<longrightarrow> q)\<^sub>e \<sqsubseteq> P"
  shows "(p \<longrightarrow> q)\<^sub>e \<sqsubseteq> P"
  using assms by(pred_auto)
*)

(*
lemma cond_refine_rel: 
  assumes "S \<sqsubseteq> (\<lceil>b\<rceil>\<^sub>< \<and> P)" "S \<sqsubseteq> (\<lceil>\<not>b\<rceil>\<^sub>< \<and> Q)"
  shows "S \<sqsubseteq> P \<^bold>\<lhd> b \<^bold>\<rhd> Q"
  by (metis aext_not assms(1) assms(2) cond_def lift_rcond_def utp_pred_laws.le_sup_iff)

lemma seq_refine_pred:
  assumes "(\<lceil>b\<rceil>\<^sub>< \<Rightarrow> \<lceil>s\<rceil>\<^sub>>) \<sqsubseteq> P" and "(\<lceil>s\<rceil>\<^sub>< \<Rightarrow> \<lceil>c\<rceil>\<^sub>>) \<sqsubseteq> Q"
  shows "(\<lceil>b\<rceil>\<^sub>< \<Rightarrow> \<lceil>c\<rceil>\<^sub>>) \<sqsubseteq> (P ;; Q)"
  using assms by pred_auto
    
lemma seq_refine_unrest:
  assumes "out\<alpha> \<sharp> b" "in\<alpha> \<sharp> c"
  assumes "(b \<Rightarrow> \<lceil>s\<rceil>\<^sub>>) \<sqsubseteq> P" and "(\<lceil>s\<rceil>\<^sub>< \<Rightarrow> c) \<sqsubseteq> Q"
  shows "(b \<Rightarrow> c) \<sqsubseteq> (P ;; Q)"
  using assms by rel_blast 
    
subsection \<open> Preain and Postge Laws \<close>

named_theorems prepost

lemma Pre_conv_Post [prepost]:
  "Pre(P\<^sup>-) = Post(P)"
  by (pred_auto)

lemma Post_conv_Pre [prepost]:
  "Post(P\<^sup>-) = Pre(P)"
  by (pred_auto)  

lemma Pre_skip [prepost]:
  "Pre(II) = true"
  by (pred_auto)

lemma Pre_assigns [prepost]:
  "Pre(\<langle>\<sigma>\<rangle>\<^sub>a) = true"
  by (pred_auto)
   
lemma Pre_miracle [prepost]:
  "Pre(false) = false"
  by (pred_auto)

lemma Pre_assume [prepost]:
  "Pre([b]\<^sup>\<top>) = b"
  by (pred_auto)
    
lemma Pre_)seq:
  "Pre(P ;; Q) = Pre(P ;; [Pre(Q)]\<^sup>\<top>)"
  by (pred_auto)
    
lemma Pre_disj [prepost]:
  "Pre(P \<or> Q) = (Pre(P) \<or> Pre(Q))"
  by (pred_auto)

lemma Pre_inf [prepost]:
  "Pre(P \<sqinter> Q) = (Pre(P) \<or> Pre(Q))"
  by (pred_auto)

text \<open> If P uses on the variables in @{term a} and @{term Q} does not refer to the variables of
  @{term "$a\<acute>"} then we can distribute. \<close>

lemma Pre_conj_indep [prepost]: "\<lbrakk> {$a,$a\<acute>} \<natural> P; $a\<acute> \<sharp> Q; vwb_lens a \<rbrakk> \<Longrightarrow> Pre(P \<and> Q) = (Pre(P) \<and> Pre(Q))"
  by (pred_auto, metis lens_override_def lens_override_idem)

lemma assume_Pre [prepost]:
  "[Pre(P)]\<^sup>\<top> ;; P = P"
  by (pred_auto)
*)

end
