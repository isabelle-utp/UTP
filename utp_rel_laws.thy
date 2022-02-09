section \<open> Relational Calculus Laws \<close>

theory utp_rel_laws
  imports 
    utp_rel
    utp_recursion
    utp_liberate
begin

section \<open> Cond laws \<close>

lemma cond_idem [simp]: "P \<lhd> b \<rhd> P = P"
  by rel_auto

lemma cond_sym: "P \<lhd> b \<rhd> Q = Q \<lhd> \<not>b \<rhd> P"
  by rel_auto

lemma cond_assoc: "(P \<lhd> b \<rhd> Q) \<lhd> c \<rhd> R = P \<lhd> b \<and> c \<rhd> (Q \<lhd> c \<rhd> R)"
  by rel_auto

lemma cond_distr: "P \<lhd> b \<rhd> (Q \<lhd> c \<rhd> R) = (P \<lhd> b \<rhd> Q) \<lhd> c \<rhd> (P \<lhd> b \<rhd> R)"
  by rel_auto

lemma cond_true [simp]: "P \<lhd> true \<rhd> Q = P"
  by rel_auto

lemma cond_false [simp]: "P \<lhd> false \<rhd> Q = Q"
  by rel_auto

lemma cond_reach [simp]: "P \<lhd> b \<rhd> (Q \<lhd> b \<rhd> R) = P \<lhd> b \<rhd> R"
  by rel_auto

lemma cond_disj [simp]: "P \<lhd> b \<rhd> (P \<lhd> c \<rhd> Q) = P \<lhd> b \<or> c \<rhd> Q"
  by rel_auto

(* \<odot> stands for any truth-functional operator. Any way of writing this?
lemma cond_interchange: "(P \<odot> Q) \<lhd> b \<rhd> (R \<odot> S) = (P \<lhd> b \<rhd> R) \<odot> (Q \<lhd> b \<rhd> S)"
*)

lemma comp_rcond_left_distr:
  "(P \<^bold>\<lhd> b \<^bold>\<rhd> Q) \<Zcomp> R = (P \<Zcomp> R) \<^bold>\<lhd> b \<^bold>\<rhd> (Q \<Zcomp> R) "
  by (rel_auto)

lemma cond_seq_left_distr:
  "out\<alpha> \<sharp> b \<Longrightarrow> ((P \<lhd> b \<rhd> Q) \<Zcomp> R) = ((P \<Zcomp> R) \<lhd> b \<rhd> (Q \<Zcomp> R))"
  by (rel_auto, blast)

lemma cond_seq_right_distr:
  "in\<alpha> \<sharp> b \<Longrightarrow> (P \<Zcomp> (Q \<lhd> b \<rhd> R)) = ((P \<Zcomp> Q) \<lhd> b \<rhd> (P \<Zcomp> R))"
  by (rel_auto, blast)

text \<open> Alternative expression of conditional using assumptions and choice \<close>

lemma rcond_rassume_expand: "P \<^bold>\<lhd> b \<^bold>\<rhd> Q = (\<questiondown>b? \<Zcomp> P) \<union> (\<questiondown>(\<not> b)? \<Zcomp> Q)"
  by rel_auto

lemma rcond_mono:  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<^bold>\<lhd> b \<^bold>\<rhd> Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 \<^bold>\<lhd> b \<^bold>\<rhd> Q\<^sub>2)"
  by rel_auto

lemma rcond_refine: "(P \<sqsubseteq> (Q \<lhd> b \<rhd> R)) = (P \<sqsubseteq> ((b)\<^sub>u \<and> Q) \<and> (P \<sqsubseteq> ((\<not>b)\<^sub>u \<and> R)))"
  by rel_simp

section \<open> Precondition and Postcondition Laws \<close>
  
theorem precond_equiv:
  "P = (P \<Zcomp> true) \<longleftrightarrow> (out\<alpha> \<sharp> P)"
  by (rel_auto)

theorem postcond_equiv:
  "P = (true \<Zcomp> P) \<longleftrightarrow> (in\<alpha> \<sharp> P)"
  by (rel_auto)

theorem precond_left_zero:
  assumes "out\<alpha> \<sharp> p" "p \<noteq> false"
  shows "(true \<Zcomp> p) = true"
  using assms by (rel_auto)

(*theorem feasibile_iff_true_right_zero:
  "P \<Zcomp> true = true \<longleftrightarrow> (\<exists> out\<alpha> \<bullet> P)\<^sub>u"
  oops*)
    
subsection \<open> Sequential Composition Laws \<close>
    
lemma seqr_assoc: "(P \<Zcomp> Q) \<Zcomp> R = P \<Zcomp> (Q \<Zcomp> R)"
  by (rel_auto)

lemma seqr_left_zero [simp]:
  "false \<Zcomp> P = false"
  by pred_auto

lemma seqr_right_zero [simp]:
  "P \<Zcomp> false = false"
  by pred_auto

lemma seqr_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<Zcomp> Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 \<Zcomp> Q\<^sub>2)"
  unfolding ref_by_set_def by auto
    
lemma seqr_monotonic:
  "\<lbrakk> mono P; mono Q \<rbrakk> \<Longrightarrow> mono (\<lambda> X. P X \<Zcomp> Q X)"
  by (simp add: mono_def relcomp_mono)

lemma cond_seqr_mono: "mono (\<lambda>X. (P \<Zcomp> X) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
  unfolding mono_def by (meson equalityE rcond_mono ref_by_set_def relcomp_mono)

lemma mono_seqr_tail:
  assumes "mono F"
  shows "mono (\<lambda> X. P \<Zcomp> F(X))"
  apply (rule monoI)
  by (meson assms monoE relcomp_mono subset_eq)

lemma seqr_liberate_left: "vwb_lens x \<Longrightarrow> (((P :: 'a \<leftrightarrow> 'b) \\ $x\<^sup><) \<Zcomp> Q) = ((P \<Zcomp> Q) \\ $x\<^sup><)"
  by (rel_auto add: liberate_pred_def)

lemma seqr_liberate_right: "vwb_lens x \<Longrightarrow> P \<Zcomp> Q \\ $x\<^sup>> = (P \<Zcomp> Q) \\ $x\<^sup>>"
  by (rel_auto add: liberate_pred_def)

lemma seqr_or_distl:
  "((P \<or> Q) \<Zcomp> R) = ((P \<Zcomp> R) \<or> (Q \<Zcomp> R))"
  by (rel_auto)

lemma seqr_or_distr:
  "(P \<Zcomp> (Q \<or> R)) = ((P \<Zcomp> Q) \<or> (P \<Zcomp> R))"
  by (rel_auto)

lemma seqr_and_distr_ufunc:
  "functional P \<Longrightarrow> (P \<Zcomp> (Q \<and> R)) = ((P \<Zcomp> Q) \<and> (P \<Zcomp> R))"
  by (rel_auto; metis single_valuedD)

lemma seqr_and_distl_uinj:
  "injective R \<Longrightarrow> ((P \<and> Q) \<Zcomp> R) = ((P \<Zcomp> R) \<and> (Q \<Zcomp> R))"
  by (rel_auto add: injective_def)

(*
lemma seqr_unfold:
  "(P \<Zcomp> Q) = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>v\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>) \\ v"
  by (rel_auto)

lemma seqr_unfold_heterogeneous:
  "(P \<Zcomp> Q) = (pre(P\<lbrakk>\<guillemotleft>v\<guillemotright>//$v\<^sup>>\<rbrakk>))\<^sup>< \\ v\<^sup>< \<and> (post(Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$v\<rbrakk>))\<^sup>>)"
  by (rel_auto)

lemma seqr_middle:
  assumes "vwb_lens x"
  shows "(P \<Zcomp> Q) = (\<^bold>\<exists> v \<bullet> P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> \<Zcomp> Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  by (rel_auto', metis vwb_lens_wb wb_lens.source_stability)
*)

lemma seqr_left_one_point:
  assumes "vwb_lens x"
  shows "((P \<and> ($x\<^sup>> = \<guillemotleft>v\<guillemotright>)\<^sub>u) \<Zcomp> Q) = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk> \<Zcomp> Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup><\<rbrakk>)"
  using assms
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_right_one_point:
  assumes "vwb_lens x"
  shows "(P \<Zcomp> (($x\<^sup>< = \<guillemotleft>v\<guillemotright>)\<^sub>u \<and> Q)) = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk> \<Zcomp> Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup><\<rbrakk>)"
  using assms
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_left_one_point_true:
  assumes "vwb_lens x"
  shows "((P \<and> ($x\<^sup>>)\<^sub>u) \<Zcomp> Q) = (P\<lbrakk>true/x\<^sup>>\<rbrakk> \<Zcomp> Q\<lbrakk>true/x\<^sup><\<rbrakk>)"
  using assms
  by (rel_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma seqr_left_one_point_false:
  assumes "vwb_lens x"
  shows "((P \<and> \<not>($x\<^sup>>)\<^sub>u) \<Zcomp> Q) = (P\<lbrakk>false/x\<^sup>>\<rbrakk> \<Zcomp> Q\<lbrakk>false/x\<^sup><\<rbrakk>)"
  using assms by (rel_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma seqr_right_one_point_true:
  assumes "vwb_lens x"
  shows "(P \<Zcomp> (($x\<^sup><)\<^sub>u \<and> Q)) = (P\<lbrakk>true/x\<^sup>>\<rbrakk> \<Zcomp> Q\<lbrakk>true/x\<^sup><\<rbrakk>)"
  using assms by (rel_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma seqr_right_one_point_false:
  assumes "vwb_lens x"
  shows "(P \<Zcomp> (\<not>($x\<^sup><)\<^sub>u \<and> Q)) = (P\<lbrakk>false/x\<^sup>>\<rbrakk> \<Zcomp> Q\<lbrakk>false/x\<^sup><\<rbrakk>)"
  using assms by (rel_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma seqr_insert_ident_left:
  assumes "vwb_lens x" "$x\<^sup>> \<sharp> P" "$x\<^sup>< \<sharp> Q"
  shows "((($x\<^sup>> = $x\<^sup><)\<^sub>u \<and> P) \<Zcomp> Q) = (P \<Zcomp> Q)"
  using assms by (rel_auto, meson vwb_lens_wb wb_lens_weak weak_lens.put_get)

lemma seqr_insert_ident_right:
  assumes "vwb_lens x" "$x\<^sup>> \<sharp> P" "$x\<^sup>< \<sharp> Q"
  shows "(P \<Zcomp> (($x\<^sup>> = $x\<^sup><)\<^sub>u \<and> Q)) = (P \<Zcomp> Q)"
  using assms by (rel_auto, metis (no_types, opaque_lifting) vwb_lens_def wb_lens_def weak_lens.put_get)

lemma seq_var_ident_lift:
  assumes "vwb_lens x" "$x\<^sup>> \<sharp> P" "$x\<^sup>< \<sharp> Q"
  shows "((($x\<^sup>> = $x\<^sup><)\<^sub>u \<and> P) \<Zcomp> (($x\<^sup>> = $x\<^sup><)\<^sub>u \<and> Q)) = (($x\<^sup>> = $x\<^sup><)\<^sub>u \<and> (P \<Zcomp> Q))"
  using assms by (rel_auto, metis (no_types, lifting) vwb_lens_wb wb_lens_weak weak_lens.put_get)

lemma seqr_bool_split:
  assumes "vwb_lens x"
  shows "P \<Zcomp> Q = (P\<lbrakk>true/x\<^sup>>\<rbrakk> \<Zcomp> Q\<lbrakk>true/x\<^sup><\<rbrakk> \<or> P\<lbrakk>(false)\<^sub>u/x\<^sup>>\<rbrakk> \<Zcomp> Q\<lbrakk>false/x\<^sup><\<rbrakk>)"
  using assms apply (subst seqr_middle[of x], simp_all)
  apply rel_auto
  oops

lemma cond_inter_var_split:
  assumes "vwb_lens x"
  shows "(P \<lhd> $x\<^sup>> \<rhd> Q) \<Zcomp> R = (P\<lbrakk>true/x\<^sup>>\<rbrakk> \<Zcomp> R\<lbrakk>true/x\<^sup><\<rbrakk> \<or> Q\<lbrakk>false/x\<^sup>>\<rbrakk> \<Zcomp> R\<lbrakk>false/x\<^sup><\<rbrakk>)"
proof -
  have "(P \<lhd> $x\<^sup>> \<rhd> Q) \<Zcomp> R = (((x\<^sup>>)\<^sub>u \<and> P) \<Zcomp> R \<or> (\<not> (x\<^sup>>)\<^sub>u \<and> Q) \<Zcomp> R)"
    by rel_simp
  also have "... = ((P \<and> (x\<^sup>>)\<^sub>u) \<Zcomp> R \<or> (Q \<and> \<not>(x\<^sup>>)\<^sub>u) \<Zcomp> R)"
    by (rel_auto)
  also have "... = (P\<lbrakk>true/x\<^sup>>\<rbrakk> \<Zcomp> R\<lbrakk>true/x\<^sup><\<rbrakk> \<or> Q\<lbrakk>false/x\<^sup>>\<rbrakk> \<Zcomp> R\<lbrakk>false/x\<^sup><\<rbrakk>)"
    apply (rel_auto add: seqr_left_one_point_true seqr_left_one_point_false assms)
    by (metis (full_types) assms vwb_lens_wb wb_lens.get_put)+
  finally show ?thesis .
qed

theorem seqr_pre_transfer: "in\<alpha> \<sharp> q \<Longrightarrow> ((P \<and> q) \<Zcomp> R) = (P \<Zcomp> (q\<^sup>- \<and> R))"
  by rel_auto

theorem seqr_pre_transfer':
  "((P \<and> (q\<^sup>>)\<^sub>u) \<Zcomp> R) = (P \<Zcomp> ((q\<^sup><)\<^sub>u \<and> R))"
  by (rel_auto)

theorem seqr_post_out: "in\<alpha> \<sharp> r \<Longrightarrow> (P \<Zcomp> (Q \<and> r)) = ((P \<Zcomp> Q) \<and> r)"
  by (rel_auto)

lemma seqr_post_var_out:
  shows "(P \<Zcomp> (Q \<and> (x\<^sup>>)\<^sub>u)) = ((P \<Zcomp> Q) \<and> (x\<^sup>>)\<^sub>u)"
  by (rel_auto)

theorem seqr_post_transfer: "out\<alpha> \<sharp> q \<Longrightarrow> (P \<Zcomp> (q \<and> R)) = ((P \<and> q\<^sup>-) \<Zcomp> R)"
  by (rel_auto)

lemma seqr_pre_out: "out\<alpha> \<sharp> p \<Longrightarrow> ((p \<and> Q) \<Zcomp> R) = (p \<and> (Q \<Zcomp> R))"
  by (rel_auto)

lemma seqr_pre_var_out:
  shows "(((x\<^sup><)\<^sub>u \<and> P) \<Zcomp> Q) = ((x\<^sup><)\<^sub>u \<and> (P \<Zcomp> Q))"
  by (rel_auto)

lemma seqr_true_lemma:
  "(P = (\<not> ((\<not> P) \<Zcomp> true))) = (P = (P \<Zcomp> true))"
  by (rel_auto)

lemma seqr_to_conj: "\<lbrakk> out\<alpha> \<sharp> P; in\<alpha> \<sharp> Q \<rbrakk> \<Longrightarrow> (P \<Zcomp> Q) = (P \<and> Q)"
  by (rel_auto; blast)

lemma liberate_seq_unfold:
  "vwb_lens x \<Longrightarrow> $x \<sharp> Q \<Longrightarrow> (P \\ $x) \<Zcomp> Q = (P \<Zcomp> Q) \\ $x"
  apply (rel_auto add: liberate_pred_def)
  oops

(*
lemma shEx_mem_lift_seq_1 [uquant_lift]:
  assumes "out\<alpha> \<sharp> A"
  shows "((\<^bold>\<exists> x \<in> A \<bullet> P x) \<Zcomp> Q) = (\<^bold>\<exists> x \<in> A \<bullet> (P x \<Zcomp> Q))"
  using assms by rel_blast

lemma shEx_lift_seq_2 [uquant_lift]:
  "(P \<Zcomp> (\<^bold>\<exists> x \<bullet> Q x)) = (\<^bold>\<exists> x \<bullet> (P \<Zcomp> Q x))"
  by rel_auto

lemma shEx_mem_lift_seq_2 [uquant_lift]:
  assumes "in\<alpha> \<sharp> A"
  shows "(P \<Zcomp> (\<^bold>\<exists> x \<in> A \<bullet> Q x)) = (\<^bold>\<exists> x \<in> A \<bullet> (P \<Zcomp> Q x))"
  using assms by rel_blast*)

subsection \<open> Iterated Sequential Composition Laws \<close>
  
lemma iter_seqr_nil [simp]: "(\<Zcomp> i : [] \<bullet> P(i)) = II"
  by (simp add: seqr_iter_def)
    
lemma iter_seqr_cons [simp]: "(\<Zcomp> i : (x # xs) \<bullet> P(i)) = P(x) \<Zcomp> (\<Zcomp> i : xs \<bullet> P(i))"
  by (simp add: seqr_iter_def)

subsection \<open> Quantale Laws \<close>

text \<open> Kept here for backwards compatibility, remove when this library catches up with the old UTP
       as most of these are already proven in Relation.thy\<close>

subsection \<open> Skip Laws \<close>
    
lemma cond_skip: "out\<alpha> \<sharp> b \<Longrightarrow> (b \<and> II) = (II \<and> b\<^sup>-)"
  by (rel_auto)

lemma pre_skip_post: "((b\<^sup><)\<^sub>u \<and> II) = (II \<and> (b\<^sup>>)\<^sub>u)"
  by (rel_auto)

lemma skip_var:
  fixes x :: "(bool \<Longrightarrow> '\<alpha>)"
  shows "(($x\<^sup><)\<^sub>u \<and> II) = (II \<and> ($x\<^sup>>)\<^sub>u)"
  by (rel_auto)

(*
text \<open>Liberate currently doesn't work on relations - it expects a lens of type 'a instead of 'a \<times> 'a\<close>
lemma skip_r_unfold:
  "vwb_lens x \<Longrightarrow> II = (($x\<^sup>> = $x\<^sup><)\<^sub>u \<and> II \\ $x)"
  by (rel_simp, metis mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put)
*)

lemma skip_r_alpha_eq:
  "II = (\<^bold>v\<^sup>< = \<^bold>v\<^sup>>)\<^sub>u"
  by (rel_auto)

(*
lemma skip_ra_unfold:
  "II\<^bsub>x;y\<^esub> = ($x\<acute> =\<^sub>u $x \<and> II\<^bsub>y\<^esub>)"
  by (rel_auto)

lemma skip_res_as_ra:
  "\<lbrakk> vwb_lens y; x +\<^sub>L y \<approx>\<^sub>L 1\<^sub>L; x \<bowtie> y \<rbrakk> \<Longrightarrow> II\<restriction>\<^sub>\<alpha>x = II\<^bsub>y\<^esub>"
  apply (rel_auto)
   apply (metis (no_types, lifting) lens_indep_def)
  apply (metis vwb_lens.put_eq)
  done
*)

section \<open> Frame laws \<close>

named_theorems frame

lemma frame_all [frame]: "\<Sigma>:[P] = P"
  by (rel_auto)

lemma frame_none [frame]: "\<emptyset>:[P] = (P \<and> II)"
  by (rel_auto add: scene_override_commute)


lemma frame_commute:
  assumes "($y\<^sup><) \<sharp> P" "($y\<^sup>>) \<sharp> P""($x\<^sup><) \<sharp> Q" "($x\<^sup>>) \<sharp> Q" "x \<bowtie> y" 
  shows "$x:[P] \<Zcomp> $y:[Q] = $y:[Q] \<Zcomp> $x:[P]"
  oops
  (*apply (insert assms)
  apply (rel_auto)
   apply (rename_tac s s' s\<^sub>0)
   apply (subgoal_tac "(s \<oplus>\<^sub>L s' on y) \<oplus>\<^sub>L s\<^sub>0 on x = s\<^sub>0 \<oplus>\<^sub>L s' on y")
    apply (metis lens_indep_get lens_indep_sym lens_override_def)
   apply (simp add: lens_indep.lens_put_comm lens_override_def)
  apply (rename_tac s s' s\<^sub>0)
  apply (subgoal_tac "put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> s (get\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> s\<^sub>0 (get\<^bsub>x\<^esub> s')))) (get\<^bsub>y\<^esub> (put\<^bsub>y\<^esub> s (get\<^bsub>y\<^esub> s\<^sub>0))) 
                      = put\<^bsub>x\<^esub> s\<^sub>0 (get\<^bsub>x\<^esub> s')")
   apply (metis lens_indep_get lens_indep_sym)
  apply (metis lens_indep.lens_put_comm)
  done*)
 
lemma frame_miracle [simp]:
  "x:[false] = false"
  by (rel_auto)

lemma frame_skip [simp]:
  "idem_scene x \<Longrightarrow> x:[II] = II"
  by (rel_auto)

lemma frame_assign_in [frame]:
  "\<lbrakk> vwb_lens a; x \<subseteq>\<^sub>L a \<rbrakk> \<Longrightarrow> $a:[x := v] = x := v"
  apply rel_auto
  by (simp add: lens_override_def scene_override_commute)

lemma frame_conj_true [frame]:
  "\<lbrakk>-{x\<^sup><, x\<^sup>>} \<sharp> P; vwb_lens x \<rbrakk> \<Longrightarrow> (P \<and> $x:[true]) = $x:[P]"
  by (rel_auto)

(*lemma frame_is_assign [frame]:
  "vwb_lens x \<Longrightarrow> x:[$x\<acute> =\<^sub>u \<lceil>v\<rceil>\<^sub><] = x := v"
  by (rel_auto)
  *)  
lemma frame_seq [frame]:
  assumes "vwb_lens x" "-{x\<^sup>>,x\<^sup><} \<sharp> P" "-{x\<^sup><,x\<^sup>>} \<sharp> Q"
  shows "$x:[P \<Zcomp> Q] = $x:[P] \<Zcomp> $x:[Q]"
  unfolding frame_def apply (rel_auto)
  oops

lemma frame_assign_commute_unrest:
  assumes "vwb_lens x" "x \<bowtie> a" "$a \<sharp> v" "$x\<^sup>< \<sharp> P" "$x\<^sup>> \<sharp> P"
  shows "x := v ;; $a:[P] = $a:[P] ;; x := v"
  using assms apply (rel_auto)
  oops

lemma frame_to_antiframe [frame]:
  "\<lbrakk> x \<bowtie>\<^sub>S y; x \<squnion>\<^sub>S y = \<top>\<^sub>S \<rbrakk> \<Longrightarrow> x:[P] = (-y):[P]"
  apply rel_auto
  by (metis scene_indep_compat scene_indep_override scene_override_commute scene_override_id scene_override_union)+

lemma rel_frext_miracle [frame]: 
  "a:[false]\<^sup>+ = false"
  by (metis false_pred_def frame_miracle trancl_empty)
    
lemma rel_frext_skip [frame]: 
  "idem_scene a \<Longrightarrow> a:[II]\<^sup>+ = II"
  by (metis frame_skip rtrancl_empty rtrancl_trancl_absorb)

lemma rel_frext_seq [frame]:
  "idem_scene a \<Longrightarrow> a:[P \<Zcomp> Q]\<^sup>+ = (a:[P]\<^sup>+ \<Zcomp> a:[Q]\<^sup>+)"
  apply (rel_auto)
  oops (* gets nitpicked *)

(*
lemma rel_frext_assigns [frame]:
  "vwb_lens a \<Longrightarrow> a:[\<langle>\<sigma>\<rangle>\<^sub>a]\<^sup>+ = \<langle>\<sigma> \<oplus>\<^sub>s a\<rangle>\<^sub>a"
  by (rel_auto)

lemma rel_frext_rcond [frame]:
  "a:[P \<triangleleft> b \<triangleright>\<^sub>r Q]\<^sup>+ = (a:[P]\<^sup>+ \<triangleleft> b \<oplus>\<^sub>p a \<triangleright>\<^sub>r a:[Q]\<^sup>+)"
  by (rel_auto)

lemma rel_frext_commute: 
  "x \<bowtie> y \<Longrightarrow> x:[P]\<^sup>+ \<Zcomp> y:[Q]\<^sup>+ = y:[Q]\<^sup>+ \<Zcomp> x:[P]\<^sup>+"
  apply (rel_auto)
   apply (rename_tac a c b)
   apply (subgoal_tac "\<And>b a. get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> b a) = get\<^bsub>y\<^esub> b")
    apply (metis (no_types, hide_lams) lens_indep_comm lens_indep_get)
   apply (simp add: lens_indep.lens_put_irr2)
  apply (subgoal_tac "\<And>b c. get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> b c) = get\<^bsub>x\<^esub> b")
   apply (subgoal_tac "\<And>b a. get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> b a) = get\<^bsub>y\<^esub> b")
    apply (metis (mono_tags, lifting) lens_indep_comm)
   apply (simp_all add: lens_indep.lens_put_irr2)    
  done
    
lemma antiframe_disj [frame]: "(x:\<lbrakk>P\<rbrakk> \<or> x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P \<or> Q\<rbrakk>"
  by (rel_auto)

lemma antiframe_seq [frame]:
  "\<lbrakk> vwb_lens x; $x\<acute> \<sharp> P; $x \<sharp> Q \<rbrakk>  \<Longrightarrow> (x:\<lbrakk>P\<rbrakk> \<Zcomp> x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P \<Zcomp> Q\<rbrakk>"
  apply (rel_auto)
   apply (metis vwb_lens_wb wb_lens_def weak_lens.put_get)
  apply (metis vwb_lens_wb wb_lens.put_twice wb_lens_def weak_lens.put_get)
  done

lemma antiframe_copy_assign:
  "vwb_lens x \<Longrightarrow> (x := \<guillemotleft>v\<guillemotright> \<Zcomp> x:\<lbrakk>P\<rbrakk> \<Zcomp> x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright> \<Zcomp> x:\<lbrakk>P\<rbrakk>)"
  by rel_auto

  
lemma nameset_skip: "vwb_lens x \<Longrightarrow> (\<^bold>n\<^bold>s x \<bullet> II) = II\<^bsub>x\<^esub>"
  by (rel_auto, meson vwb_lens_wb wb_lens.get_put)
    
lemma nameset_skip_ra: "vwb_lens x \<Longrightarrow> (\<^bold>n\<^bold>s x \<bullet> II\<^bsub>x\<^esub>) = II\<^bsub>x\<^esub>"
  by (rel_auto)
    
declare sublens_def [lens_defs]
*)
subsection \<open> Modification laws \<close>
lemma "(rrestr x P) nmods x"
  oops

subsection \<open> Assignment Laws \<close>

text \<open>Extend the alphabet of a substitution\<close>
definition subst_aext :: "'a subst \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'b subst"
  where [rel]: "subst_aext \<sigma> x = (\<lambda> s. put\<^bsub>x\<^esub> s (\<sigma> (get\<^bsub>x\<^esub> s)))"

lemma assigns_subst: "(subst_aext \<sigma> fst\<^sub>L) \<dagger> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  by rel_auto

lemma assigns_r_comp: "(\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> P) = ((\<lambda> s. put\<^bsub>fst\<^sub>L\<^esub> s (\<sigma> (get\<^bsub>fst\<^sub>L\<^esub> s))) \<dagger> P)"
  by (rel_auto)

lemma assigns_r_feasible:
  "(\<langle>\<sigma>\<rangle>\<^sub>a \<Zcomp> true) = true"
  by (rel_auto)

lemma assign_subst [usubst]:
  "\<lbrakk> vwb_lens x; vwb_lens y \<rbrakk> \<Longrightarrow>  [x\<^sup>> \<leadsto> u\<^sup><] \<dagger> (y := v) = (y, x) := ([x \<leadsto> u] \<dagger> v, u)"
  apply rel_auto
  oops

lemma assign_vacuous_skip:
  assumes "vwb_lens x"
  shows "(x := $x) = II"
  using assms by rel_auto

text \<open> The following law shows the case for the above law when $x$ is only mainly-well behaved. We
  require that the state is one of those in which $x$ is well defined using and assumption. \<close>

(*
lemma assign_vacuous_assume:
  assumes "mwb_lens x"
  shows "[&\<^bold>v \<in> \<guillemotleft>\<S>\<^bsub>x\<^esub>\<guillemotright>]\<^sup>\<top> \<Zcomp> (x := &x) = [&\<^bold>v \<in> \<guillemotleft>\<S>\<^bsub>x\<^esub>\<guillemotright>]\<^sup>\<top>"
  using assms by rel_auto *)

lemma assign_simultaneous:
  assumes "vwb_lens y" "x \<bowtie> y"
  shows "(x,y) := (e, $y) = (x := e)"
  using assms by rel_auto

lemma assigns_idem: "mwb_lens x \<Longrightarrow> (x,x) := (v,u) = (x := v)"
  by rel_auto

(*
lemma assigns_cond: "\<langle>f\<rangle>\<^sub>a \<^bold>\<lhd> b \<^bold>\<rhd> \<langle>g\<rangle>\<^sub>a = \<langle>f \<^bold>\<lhd> b \<^bold>\<rhd> g\<rangle>\<^sub>a"
  by (rel_auto)*)

lemma assigns_r_conv:
  "bij f \<Longrightarrow> \<langle>f\<rangle>\<^sub>a\<^sup>- = \<langle>inv f\<rangle>\<^sub>a"
  by (rel_auto, simp_all add: bij_is_inj bij_is_surj surj_f_inv_f)

lemma assign_pred_transfer:
  assumes "$x\<^sup>< \<sharp> b" "out\<alpha> \<sharp> b"
  shows "(b \<and> x := v) = (x := v \<and> b\<^sup>-)"
  using assms apply rel_auto oops
    
lemma assign_r_comp: "x := u ;; P = P\<lbrakk>u\<^sup></x\<^sup><\<rbrakk>"
  by rel_auto

lemma assign_test: "mwb_lens x \<Longrightarrow> (x := \<guillemotleft>u\<guillemotright> ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright>)"
  by rel_auto

lemma assign_twice: "\<lbrakk> mwb_lens x; $x \<sharp> f \<rbrakk> \<Longrightarrow> (x := e ;; x := f) = (x := f)"
  by rel_auto
 
lemma assign_commute:
  assumes "x \<bowtie> y" "$x \<sharp> f" "$y \<sharp> e" "vwb_lens x" "vwb_lens y"
  shows "(x := e ;; y := f) = (y := f ;; x := e)"
  using assms by (rel_auto add: lens_indep_comm)

lemma assign_cond:
  assumes "out\<alpha> \<sharp> b"
  shows "(x := e \<Zcomp> (P \<lhd> b \<rhd> Q)) = ((x := e \<Zcomp> P) \<lhd> b \<rhd> (x := e \<Zcomp> Q))"
  apply rel_auto
     defer
  oops

lemma assign_rcond:
  "(x := e ;; (P \<^bold>\<lhd> b \<^bold>\<rhd> Q)) = ((x := e ;; P) \<^bold>\<lhd> (b\<lbrakk>e/x\<rbrakk>) \<^bold>\<rhd> (x := e ;; Q))"
  by (rel_auto)

lemma assign_r_alt_def:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "x := v = II\<lbrakk>v\<^sup></x\<^sup><\<rbrakk>"
  by (rel_auto)

lemma assigns_r_func: "functional \<langle>f\<rangle>\<^sub>a"
  by (rel_auto)

(*
lemma assigns_r_uinj: "inj\<^sub>s f \<Longrightarrow> uinj \<langle>f\<rangle>\<^sub>a"
  apply (rel_simp, simp add: inj_eq) 
    
lemma assigns_r_swap_uinj:
  "\<lbrakk> vwb_lens x; vwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> uinj ((x,y) := (&y,&x))"
  by (metis assigns_r_uinj pr_var_def swap_usubst_inj)

lemma assign_unfold:
  "vwb_lens x \<Longrightarrow> (x := v) = (x\<^sup>> = v\<^sup><)"
  apply (rel_auto, auto simp add: comp_def)
  using vwb_lens.put_eq by fastforce*)

subsection \<open> Non-deterministic Assignment Laws \<close>

lemma ndet_assign_comp:
  "x \<bowtie> y \<Longrightarrow> x := * ;; y := * = (x,y) := *"
  by (rel_auto add: lens_indep.lens_put_comm)
  
lemma ndet_assign_assign:
  "\<lbrakk> vwb_lens x; $x \<sharp> e \<rbrakk> \<Longrightarrow> x := * ;; x := e = x := e"
  by rel_auto

lemma ndet_assign_refine:
  "x := * \<sqsubseteq> x := e"
  by rel_auto

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

lemma not_convr [simp]: "(\<not> p)\<^sup>- = (\<not> p\<^sup>-)"
  by (pred_auto)

lemma disj_convr [simp]: "(p \<or> q)\<^sup>- = (q\<^sup>- \<or> p\<^sup>-)"
  by (pred_auto)

lemma conj_convr [simp]: "(p \<and> q)\<^sup>- = (q\<^sup>- \<and> p\<^sup>-)"
  by (pred_auto)

lemma seqr_convr [simp]: "(p \<Zcomp> q)\<^sup>- = (q\<^sup>- \<Zcomp> p\<^sup>-)"
  by (rel_auto)

lemma pre_convr [simp]: "\<lceil>p\<rceil>\<^sub><\<^sup>- = \<lceil>p\<rceil>\<^sub>>"
  by (rel_auto)

lemma post_convr [simp]: "\<lceil>p\<rceil>\<^sub>>\<^sup>- = \<lceil>p\<rceil>\<^sub><"
  by (rel_auto)*)

subsection \<open> Assertion and Assumption Laws \<close>


declare sublens_def [lens_defs del]
  
lemma assume_false: "\<questiondown>false? = false"
  by (rel_auto)
  
lemma assume_true: "\<questiondown>true? = II"
  by (rel_auto)
    
lemma assume_seq: "\<questiondown>b? \<Zcomp> \<questiondown>c? = \<questiondown>b \<and> c?"
  by (rel_auto)

(*
lemma assert_false: "{false}\<^sub>\<bottom> = true"
  by (rel_auto)

lemma assert_true: "{true}\<^sub>\<bottom> = II"
  by (rel_auto)
    
lemma assert_seq: "{b}\<^sub>\<bottom> \<Zcomp> {c}\<^sub>\<bottom> = {(b \<and> c)}\<^sub>\<bottom>"
  by (rel_auto)*)

subsection \<open> While Loop Laws \<close>

theorem while_unfold:
  "while b do P od = ((P \<Zcomp> while b do P od) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
proof -
  have m:"mono (\<lambda>X. (P \<Zcomp> X) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    unfolding mono_def by (meson equalityE rcond_mono ref_by_set_def relcomp_mono)
  have "(while b do P od) = (\<nu> X \<bullet> (P \<Zcomp> X) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: while_top_def)
  also have "... = ((P \<Zcomp> (\<nu> X \<bullet> (P \<Zcomp> X) \<^bold>\<lhd> b \<^bold>\<rhd> II)) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (subst lfp_unfold, simp_all add: m)
  also have "... = ((P \<Zcomp> while b do P od) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: while_top_def)
  finally show ?thesis .
qed

theorem while_false: "while (false)\<^sub>e do P od = II"
  by (subst while_unfold, rel_auto)

theorem while_true: "while (true)\<^sub>e do P od = false"
  apply (simp add: while_top_def alpha)
  apply (rule antisym)
  apply (rule lfp_lowerbound)
  apply (rel_auto)+
  done

theorem while_bot_unfold:
  "while\<^sub>\<bottom> b do P od = ((P \<Zcomp> while\<^sub>\<bottom> b do P od) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
proof -
  have m:"mono (\<lambda>X. (P \<Zcomp> X) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    unfolding mono_def by (meson equalityE rcond_mono ref_by_set_def relcomp_mono)
  have "(while\<^sub>\<bottom> b do P od) = (\<mu> X \<bullet> (P \<Zcomp> X) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: while_bot_def)
  also have "... = ((P \<Zcomp> (\<mu> X \<bullet> (P \<Zcomp> X) \<^bold>\<lhd> b \<^bold>\<rhd> II)) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (subst gfp_unfold, simp_all add: m)
  also have "... = ((P \<Zcomp> while\<^sub>\<bottom> b do P od) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: while_bot_def)
  finally show ?thesis .
qed

theorem while_bot_false: "while\<^sub>\<bottom> (false)\<^sub>e do P od = II"
  by (rel_auto add: while_bot_def gfp_const)

theorem while_bot_true: "while\<^sub>\<bottom> (true)\<^sub>e do P od = (\<mu> X \<bullet> P \<Zcomp> X)"
  by (rel_auto add: while_bot_def)

text \<open> An infinite loop with a feasible body corresponds to a program error (non-termination). \<close>

theorem while_infinite: "P \<Zcomp> true = true \<Longrightarrow> while\<^sub>\<bottom> (true)\<^sub>e do P od = true"
  apply (rule antisym)
   apply (simp add: true_pred_def)
    apply (rel_auto add: gfp_upperbound while_bot_true)
  done

subsection \<open> Algebraic Properties \<close>

interpretation upred_semiring: semiring_1 
  where times = "(\<Zcomp>)" and one = Id and zero = false_pred and plus = "Lattices.sup"
  by (unfold_locales; rel_auto+)

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
text \<open> The following two proofs are adapted from the AFP entry 
  \href{https://www.isa-afp.org/entries/Kleene_Algebra.shtml}{Kleene Algebra}. 
  See also~\cite{Armstrong2012,Armstrong2015}. \<close>

lemma upower_inductl: "Q \<sqsubseteq> ((P \<Zcomp> Q) \<sqinter> R) \<Longrightarrow> Q \<sqsubseteq> P ^^ n \<Zcomp> R"
proof (induct n)
  case 0
  then show ?case by (auto)
next
  case (Suc n)
  then show ?case
    by (smt (verit, del_insts) ref_lattice.inf.absorb_iff1 ref_lattice.le_infE relcomp_distrib relpow.simps(2) relpow_commute seqr_assoc)
qed

lemma upower_inductr:
  assumes "Q \<sqsubseteq> R \<sqinter> (Q \<Zcomp> P)"
  shows "Q \<sqsubseteq> R \<Zcomp> (P ^^ n)"
using assms proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    by (rel_auto, blast)
qed

lemma SUP_atLeastAtMost_first:
  fixes P :: "nat \<Rightarrow> 'a::complete_lattice"
  assumes "m \<le> n"
  shows "(\<Sqinter>i\<in>{m..n}. P(i)) = P(m) \<sqinter> (\<Sqinter>i\<in>{Suc m..n}. P(i))"
  by (metis SUP_insert assms atLeastAtMost_insertL)
    
lemma upower_seqr_iter: "P ^^ n = (\<Zcomp> Q : replicate n P \<bullet> Q)"
  apply (induct n)
  by (simp, metis iter_seqr_cons relpow.simps(2) relpow_commute replicate_Suc)

subsection \<open> Omega \<close>

definition uomega :: "'\<alpha> rel \<Rightarrow> '\<alpha> rel" ("_\<^sup>\<omega>" [999] 999) where
"P\<^sup>\<omega> = (\<mu> X \<bullet> P \<Zcomp> X)"

subsection \<open> Relation Algebra Laws \<close>

theorem seqr_disj_cancel: "((P\<^sup>- \<Zcomp> (\<not>(P \<Zcomp> Q))) \<or> (\<not>Q)) = (\<not>Q)"
  by (rel_auto)

subsection \<open> Kleene Algebra Laws \<close>

theorem ustar_sub_unfoldl: "P\<^sup>* \<sqsubseteq> II \<sqinter> (P\<Zcomp>P\<^sup>*)"
  by rel_force
    
theorem rtrancl_inductl:
  assumes "Q \<sqsubseteq> R" "Q \<sqsubseteq> P \<Zcomp> Q"
  shows "Q \<sqsubseteq> P\<^sup>* \<Zcomp> R"
proof -
  have "P\<^sup>* \<Zcomp> R = (\<Sqinter> i. P ^^ i \<Zcomp> R)"
    by (simp add: relcomp_UNION_distrib2 rtrancl_is_UN_relpow)
  also have "Q \<sqsubseteq> ..."
    by (simp add: assms ref_lattice.INF_greatest upower_inductl)
  finally show ?thesis .
qed

theorem rtrancl_inductr:
  assumes "Q \<sqsubseteq> R" "Q \<sqsubseteq> Q \<Zcomp> P"
  shows "Q \<sqsubseteq> R \<Zcomp> P\<^sup>*"
proof -
  have "R \<Zcomp> P\<^sup>* = (\<Sqinter> i. R \<Zcomp> P ^^ i)"
    by (metis rtrancl_is_UN_relpow relcomp_UNION_distrib)
  also have "Q \<sqsubseteq> ..."
    by (simp add: assms ref_lattice.INF_greatest upower_inductr)
  finally show ?thesis .
qed

lemma rtrancl_refines_nu: "(\<nu> X \<bullet> (P \<Zcomp> X) \<sqinter> II) \<sqsubseteq> P\<^sup>*"
proof -
  have mono_X: "mono (\<lambda> X. (P \<Zcomp> X) \<sqinter> II)"
    by (smt (verit, del_insts) Un_mono monoI relcomp_distrib subset_Un_eq sup.idem)
  { 
    fix a b assume "(a, b) \<in> P\<^sup>*"
    then have "(a, b) \<in> (\<nu> X \<bullet> (P \<Zcomp> X) \<sqinter> II)"
      apply (induct rule: converse_rtrancl_induct)
      using mono_X lfp_unfold by blast+
  }
  then show ?thesis
    by rel_auto
qed

lemma rtrancl_as_nu: "P\<^sup>* = (\<nu> X \<bullet> (P \<Zcomp> X) \<sqinter> II)"
proof (rule antisym)
  show "P\<^sup>* \<subseteq> (\<nu> X \<bullet> P \<Zcomp> X \<union> II)"
    using rtrancl_refines_nu by rel_auto
  show "(\<nu> X \<bullet> P \<Zcomp> X \<union> II) \<subseteq> P\<^sup>*"
    by (metis dual_order.refl lfp_lowerbound rtrancl_trancl_reflcl trancl_unfold_left)
qed

lemma rtrancl_unfoldl: "P\<^sup>* = II \<sqinter> (P \<Zcomp> P\<^sup>*)"
  apply (simp add: rtrancl_as_nu)
  apply (subst lfp_unfold)
   apply (rule monoI)
   apply (rel_auto)+
  done

text \<open> While loop can be expressed using Kleene star \<close>
(*
lemma while_star_form:
  "while b do P od = (P \<^bold>\<lhd> b \<^bold>\<rhd> II)\<^sup>* \<Zcomp> \<questiondown>(\<not>b)?"
proof -
  have 1: "Continuous (\<lambda>X. P \<Zcomp> X \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (rel_auto)
  have "while b do P od = (\<Sqinter>i. ((\<lambda>X. P \<Zcomp> X \<^bold>\<lhd> b \<^bold>\<rhd> II) ^^ i) false)"
    by (simp add: "1" false_upred_def sup_continuous_Continuous sup_continuous_lfp while_top_def)
  also have "... = ((\<lambda>X. P \<Zcomp> X \<^bold>\<lhd> b \<^bold>\<rhd> II) ^^ 0) false \<sqinter> (\<Sqinter>i. ((\<lambda>X. P \<Zcomp> X \<^bold>\<lhd> b \<^bold>\<rhd> II) ^^ (i+1)) false)"
    by (subst Sup_power_expand, simp)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P \<Zcomp> X \<^bold>\<lhd> b \<^bold>\<rhd> II) ^^ (i+1)) false)"
    by (simp)
  also have "... = (\<Sqinter>i. (P \<^bold>\<lhd> b \<^bold>\<rhd> II)\<^bold>^i \<Zcomp> (false \<^bold>\<lhd> b \<^bold>\<rhd> II))"
  proof (rule SUP_cong, simp_all)
    fix i
    show "P \<Zcomp> ((\<lambda>X. P \<Zcomp> X \<^bold>\<lhd> b \<^bold>\<rhd> II) ^^ i) false \<^bold>\<lhd> b \<^bold>\<rhd> II = (P \<^bold>\<lhd> b \<^bold>\<rhd> II) \<^bold>^ i \<Zcomp> (false \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    proof (induct i)
      case 0
      then show ?case by simp
    next
      case (Suc i)
      then show ?case
        by (simp add: upred_semiring.power_Suc)
           (metis (no_types, lifting) RA1 comp_cond_left_distr cond_L6 upred_semiring.mult.left_neutral)
    qed
  qed
  also have "... = (\<Sqinter>i\<in>{0..} \<bullet> (P \<^bold>\<lhd> b \<^bold>\<rhd> II)\<^bold>^i \<Zcomp> [(\<not>b)]\<^sup>\<top>)"
    by (rel_auto)
  also have "... = (P \<^bold>\<lhd> b \<^bold>\<rhd> II)\<^sup>\<star> \<Zcomp> [(\<not>b)]\<^sup>\<top>"
    by (metis seq_UINF_distr ustar_def)
  finally show ?thesis .
qed
*)
  
subsection \<open> Omega Algebra Laws \<close>

lemma uomega_induct: "P \<Zcomp> P\<^sup>\<omega> \<sqsubseteq> P\<^sup>\<omega>"
  by (metis gfp_unfold monoI ref_by_set_def relcomp_mono subset_refl uomega_def)

subsection \<open> Refinement Laws \<close>

lemma skip_r_refine: "(p \<Rightarrow> p) \<sqsubseteq> II"
  by rel_auto

lemma conj_refine_left: "(Q \<Rightarrow> P) \<sqsubseteq> R \<Longrightarrow> P \<sqsubseteq> (Q \<and> R)"
  by (rel_auto)

lemma pre_weak_rel:
  assumes "`p \<longrightarrow> I`"
  and     "(I \<longrightarrow> q)\<^sub>u \<sqsubseteq> P"
  shows "(p \<longrightarrow> q)\<^sub>u \<sqsubseteq> P"
  using assms by(rel_auto)

(*
lemma cond_refine_rel: 
  assumes "S \<sqsubseteq> (\<lceil>b\<rceil>\<^sub>< \<and> P)" "S \<sqsubseteq> (\<lceil>\<not>b\<rceil>\<^sub>< \<and> Q)"
  shows "S \<sqsubseteq> P \<^bold>\<lhd> b \<^bold>\<rhd> Q"
  by (metis aext_not assms(1) assms(2) cond_def lift_rcond_def utp_pred_laws.le_sup_iff)

lemma seq_refine_pred:
  assumes "(\<lceil>b\<rceil>\<^sub>< \<Rightarrow> \<lceil>s\<rceil>\<^sub>>) \<sqsubseteq> P" and "(\<lceil>s\<rceil>\<^sub>< \<Rightarrow> \<lceil>c\<rceil>\<^sub>>) \<sqsubseteq> Q"
  shows "(\<lceil>b\<rceil>\<^sub>< \<Rightarrow> \<lceil>c\<rceil>\<^sub>>) \<sqsubseteq> (P \<Zcomp> Q)"
  using assms by rel_auto
    
lemma seq_refine_unrest:
  assumes "out\<alpha> \<sharp> b" "in\<alpha> \<sharp> c"
  assumes "(b \<Rightarrow> \<lceil>s\<rceil>\<^sub>>) \<sqsubseteq> P" and "(\<lceil>s\<rceil>\<^sub>< \<Rightarrow> c) \<sqsubseteq> Q"
  shows "(b \<Rightarrow> c) \<sqsubseteq> (P \<Zcomp> Q)"
  using assms by rel_blast 
    
subsection \<open> Preain and Postge Laws \<close>

named_theorems prepost

lemma Pre_conv_Post [prepost]:
  "Pre(P\<^sup>-) = Post(P)"
  by (rel_auto)

lemma Post_conv_Pre [prepost]:
  "Post(P\<^sup>-) = Pre(P)"
  by (rel_auto)  

lemma Pre_skip [prepost]:
  "Pre(II) = true"
  by (rel_auto)

lemma Pre_assigns [prepost]:
  "Pre(\<langle>\<sigma>\<rangle>\<^sub>a) = true"
  by (rel_auto)
   
lemma Pre_miracle [prepost]:
  "Pre(false) = false"
  by (rel_auto)

lemma Pre_assume [prepost]:
  "Pre([b]\<^sup>\<top>) = b"
  by (rel_auto)
    
lemma Pre_seq:
  "Pre(P \<Zcomp> Q) = Pre(P \<Zcomp> [Pre(Q)]\<^sup>\<top>)"
  by (rel_auto)
    
lemma Pre_disj [prepost]:
  "Pre(P \<or> Q) = (Pre(P) \<or> Pre(Q))"
  by (rel_auto)

lemma Pre_inf [prepost]:
  "Pre(P \<sqinter> Q) = (Pre(P) \<or> Pre(Q))"
  by (rel_auto)

text \<open> If P uses on the variables in @{term a} and @{term Q} does not refer to the variables of
  @{term "$a\<acute>"} then we can distribute. \<close>

lemma Pre_conj_indep [prepost]: "\<lbrakk> {$a,$a\<acute>} \<natural> P; $a\<acute> \<sharp> Q; vwb_lens a \<rbrakk> \<Longrightarrow> Pre(P \<and> Q) = (Pre(P) \<and> Pre(Q))"
  by (rel_auto, metis lens_override_def lens_override_idem)

lemma assume_Pre [prepost]:
  "[Pre(P)]\<^sup>\<top> \<Zcomp> P = P"
  by (rel_auto)
*)

end
