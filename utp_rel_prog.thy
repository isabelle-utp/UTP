theory utp_rel_prog
  imports utp_rel_laws
begin

text \<open> Assignment is defined using substitutions, where latter defines what each variable should
  map to. This approach, which is originally due to Back~\cite{Back1998}, permits more general 
  assignment expressions. The definition of the operator identifies the after state binding, $b'$, 
  with the substitution function applied to the before state binding $b$. \<close>

definition assigns_r :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) urel" where
[pred]: "assigns_r \<sigma> = (\<lambda> (s, s'). s' = \<sigma> s)"

adhoc_overloading uassigns == assigns_r

text \<open> Non-deterministic assignment, also known as ``choose'', assigns an arbitrarily chosen value 
  to the given variable \<close>

definition ndet_assign :: "('a \<Longrightarrow> 's) \<Rightarrow> 's hrel" where
[pred]: "ndet_assign x = (\<Sqinter> v. x := \<guillemotleft>v\<guillemotright>)"

syntax "_ndet_assign" :: "svid \<Rightarrow> logic" ("_ := *" [75] 76)
translations "_ndet_assign x" == "CONST ndet_assign x"

definition while_top :: "(bool, 's) expr \<Rightarrow> 's hrel \<Rightarrow> 's hrel" where 
"while_top b P = (\<nu> X \<bullet> ((P ;; X) \<lhd> b \<rhd> II))"

definition while_bot :: "(bool, 's) expr \<Rightarrow> 's hrel \<Rightarrow> 's hrel" where 
"while_bot b P = (\<mu> X \<bullet> ((P ;; X) \<lhd> b \<rhd> II))"

adhoc_overloading uwhile == while_top

syntax 
  "_while_top" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("while\<^sup>\<top> _ do _ od")
  "_while_bot" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("while\<^sub>\<bottom> _ do _ od")

translations
  "_while_top b P" == "CONST while_top (b)\<^sub>e P"
  "_while_bot b P" == "CONST while_bot (b)\<^sub>e P"

definition let_rel :: "('i, 's) expr \<Rightarrow> ('i \<Rightarrow> 's hrel) \<Rightarrow> 's hrel" where
"let_rel e S = (\<lambda> (s, s'). S (e s) (s, s'))"

syntax 
  "_let_rel" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(let _ \<leftarrow> (_) in (_))" [0, 0, 10] 10)

translations
  "_let_rel x e S" == "CONST let_rel (e)\<^sub>e (\<lambda> x. S)"

subsection \<open> Assignment Laws \<close>

lemma assigns_skip: "\<langle>id\<rangle>\<^sub>a = II"
  by pred_auto

lemma assigns_comp: "\<langle>\<sigma>\<rangle>\<^sub>a ;; \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  by pred_auto

lemma assigns_cond: "\<langle>\<sigma>\<rangle>\<^sub>a \<lhd> b \<rhd> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<sigma> \<triangleleft> b \<triangleright> \<rho>\<rangle>\<^sub>a"
  by pred_auto  

text \<open> Extend the alphabet of a substitution \<close>

lemma assigns_subst: "(subst_aext \<sigma> fst\<^sub>L) \<dagger> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  by pred_auto

lemma assigns_r_comp: "(\<langle>\<sigma>\<rangle>\<^sub>a ;; P) = (\<sigma> \<up>\<^sub>s \<^bold>v\<^sup>< \<dagger> P)"
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

lemma pre_assigns [prepost]:
  "pre(\<langle>\<sigma>\<rangle>\<^sub>a) = true"
  by (pred_auto)

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
                  (\<exists>xs. xs \<noteq> [] \<and> (\<forall> i<length xs. b ((s # xs) ! i) \<and> P ((s # xs) ! i, xs ! i)) \<and> s' = List.last xs)) \<and>
                 \<not> b s'))"
  by (simp add: while_star_test_form, pred_simp add: ustar_chain_pred')

end