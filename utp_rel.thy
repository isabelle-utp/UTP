subsection \<open> UTP Relations \<close>

theory utp_rel
  imports utp_pred utp_pred_laws utp_rel_syntax
begin

unbundle UTP_Logic_Syntax

text \<open> Convert a predicate into a set-based (i.e. relational) representation. \<close>

type_synonym ('a, 'b) urel = "('a \<times> 'b) \<Rightarrow> bool"

translations
  (type) "('a, 'b) urel" <= (type) "('a \<times> 'b) \<Rightarrow> bool"

type_synonym 'a hrel = "('a, 'a) urel"

definition seq :: "('a, 'b) urel \<Rightarrow> ('b, 'c) urel \<Rightarrow> ('a, 'c) urel" (infixl ";;" 55) where
[pred]: "P ;; Q = (\<lambda> (s, s'). \<exists> s\<^sub>0. P (s, s\<^sub>0) \<and> Q (s\<^sub>0, s'))"

expr_ctr seq (0 1)

abbreviation "in\<alpha> \<equiv> var_alpha fst\<^sub>L"
abbreviation "out\<alpha> \<equiv> var_alpha snd\<^sub>L"

definition skip :: "'a hrel" where
[pred]: "skip = (\<lambda> (s, s'). s' = s)"

adhoc_overloading uskip skip

abbreviation "true\<^sub>h \<equiv> (true :: 's hrel)"
abbreviation "false\<^sub>h \<equiv> (false :: 's hrel)"

definition cond :: "('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> (bool, 's\<^sub>1 \<times> 's\<^sub>2) expr \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) urel"
  where [pred]: "cond P B Q = (B \<and> P \<or> \<not> B \<and> Q)\<^sub>e"

syntax 
  "_cond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<lhd> _ \<rhd>/ _)" [52,0,53] 52)
  "_rcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<^bold>\<lhd> _ \<^bold>\<rhd>/ _)" [52,0,53] 52)

translations
  "_cond P B Q" == "CONST cond P (B)\<^sub>e Q"
  "_rcond P b Q" == "_cond P (b\<^sup><) Q"

definition conv_r :: "('a, 'b) urel \<Rightarrow> ('b, 'a) urel" ("_\<^sup>-" [999] 999) where
[pred]: "conv_r P = (\<lambda> (b,a). P (a,b))"

definition assigns_rel :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) urel" where
[pred]: "assigns_rel \<sigma> = (\<lambda> (s, s'). s' = \<sigma> s)"

adhoc_overloading uassigns assigns_rel

definition test :: "('s \<Rightarrow> bool) \<Rightarrow> 's hrel" where
[pred]: "test b = (\<lambda> (s, s'). b s \<and> s' = s)"

adhoc_overloading utest test

definition ndet_assign :: "('a \<Longrightarrow> 's) \<Rightarrow> 's hrel" where
[pred]: "ndet_assign x = (\<Sqinter> v. x := \<guillemotleft>v\<guillemotright>)"

syntax "_ndet_assign" :: "svid \<Rightarrow> logic" ("_ := *" [75] 76)
translations "_ndet_assign x" == "CONST ndet_assign x"

definition seqr_iter :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b hrel) \<Rightarrow> 'b hrel" where
[pred]: "seqr_iter xs P = foldr (\<lambda> i Q. P(i) ;; Q) xs II"

syntax "_seqr_iter" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3;; _ : _ \<bullet>/ _)" [0, 0, 10] 10)
translations ";; x : l \<bullet> P" \<rightleftharpoons> "(CONST seqr_iter) l (\<lambda>x. P)"

definition while_top :: "(bool, 's) expr \<Rightarrow> 's hrel \<Rightarrow> 's hrel" ("while\<^sup>\<top> _ do _ od") where 
"while_top b P = (\<nu> X \<bullet> ((P ;; X) \<^bold>\<lhd> b \<^bold>\<rhd> II))"

notation while_top ("while _ do _ od")

definition while_bot :: "(bool, 's) expr \<Rightarrow> 's hrel \<Rightarrow> 's hrel" ("while\<^sub>\<bottom> _ do _ od") where 
"while_bot b P = (\<mu> X \<bullet> ((P ;; X) \<^bold>\<lhd> b \<^bold>\<rhd> II))"

text \<open> While loops with invariant decoration -- partial correctness\<close>

definition while_inv :: "(bool, 's) expr \<Rightarrow> (bool, 's) expr \<Rightarrow> 's hrel \<Rightarrow> 's hrel" ("while\<^sup>\<top> _ invr _ do _ od") where
"while_inv b p P = while_top b P"

notation while_inv ("while _ invr _ do _ od")

text \<open> While loops with invariant decoration -- total correctness\<close>

definition while_inv_bot :: "(bool, 's) expr \<Rightarrow> (bool, 's) expr \<Rightarrow> 's hrel \<Rightarrow> 's hrel" ("while\<^sub>\<bottom> _ invr _ do _ od") where
"while_inv_bot b p P = while_bot b P"

text \<open> While loops with invariant and variant decoration -- total correctness \<close>

definition while_vrt :: "(bool, 's) expr \<Rightarrow> (bool, 's) expr \<Rightarrow> (nat, 's) expr \<Rightarrow> 's hrel \<Rightarrow> 's hrel"
                        ("while _ invr _ vrt _ do _ od")
where "while_vrt b p v P = while_bot b P"

definition pre :: "('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>1 \<Rightarrow> bool)" 
  where [pred]: "pre P = (\<lambda> s. \<exists> s'. P (s, s'))"

definition post :: "('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>2 \<Rightarrow> bool)" 
  where [pred]: "post P = (\<lambda> s'. \<exists> s. P (s, s'))"

expr_ctr pre

expr_ctr post

subsection \<open> Predicate Semantics \<close>

lemma pred_skip [pred]: "II = ($\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e"
  by pred_simp

lemma pred_seq_hom [pred]:
  "P ;; Q = (\<exists> v\<^sub>0. [ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P \<and> [ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q)\<^sub>e"
  by pred_auto

lemma pred_seq [pred]: 
  "P ;; Q = (\<exists> v\<^sub>0. \<lparr> \<^bold>v\<^sup>< \<leadsto> $\<^bold>v\<^sup><, \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> \<rparr> \<dagger> P \<and> \<lparr> \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright>, \<^bold>v\<^sup>> \<leadsto> $\<^bold>v\<^sup>> \<rparr> \<dagger> Q)\<^sub>e"
  by (pred_auto)

lemma pred_pre [pred]: "pre P = (\<exists> s. P \<lbrakk>\<guillemotleft>s\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk>)\<^sub><"
  by (expr_simp add: pre_def Domain_iff)

lemma pred_pre_liberate: "pre P = (P \\ out\<alpha>)\<^sub><"
  by (expr_auto add: pre_def)

subsection \<open> Substitution Laws \<close>

declare seq_def [expr_defs]

thm usubst_eval

text \<open> subst_unrest needs a lens - I would like to write in\<alpha> and out\<alpha> here but that does not typecheck\<close>

lemma subst_seq_left [usubst]: "out\<alpha> \<sharp>\<^sub>s \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = (\<sigma> \<dagger> P) ;; Q"
  by pred_auto (metis snd_conv)+

lemma subst_seq_right [usubst]:
  "in\<alpha> \<sharp>\<^sub>s \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = P ;; (\<sigma> \<dagger> Q)"
  by pred_auto (metis fst_conv)+

subsection \<open> Unrestriction Laws \<close>

lemma unrest_seq_ivar [unrest]: "\<lbrakk> mwb_lens x; $x\<^sup>< \<sharp> P \<rbrakk> \<Longrightarrow> $x\<^sup>< \<sharp> P ;; Q"
  by (pred_auto)

lemma unrest_seq_ovar [unrest]: "\<lbrakk> mwb_lens x; $x\<^sup>> \<sharp> Q \<rbrakk> \<Longrightarrow> $x\<^sup>> \<sharp> P ;; Q"
  by pred_auto

subsection \<open> Relational Transfer Method \<close>

definition pred_rel :: "'s pred \<Rightarrow> 's set" ("\<lbrakk>_\<rbrakk>\<^sub>U") where
"pred_rel = Collect"

syntax "_pred_rel" :: "logic \<Rightarrow> logic" ("'(_')\<^sub>U")
translations "(p)\<^sub>U" == "CONST pred_rel (p)\<^sub>e"

named_theorems rel and rel_transfer

lemma rel_pred_interp [rel]: 
  "\<lbrakk>true\<rbrakk>\<^sub>U = UNIV" "\<lbrakk>false\<rbrakk>\<^sub>U = {}" 
  "\<lbrakk>P \<and> Q\<rbrakk>\<^sub>U = (\<lbrakk>P\<rbrakk>\<^sub>U \<inter> \<lbrakk>Q\<rbrakk>\<^sub>U)" "\<lbrakk>P \<or> Q\<rbrakk>\<^sub>U = (\<lbrakk>P\<rbrakk>\<^sub>U \<union> \<lbrakk>Q\<rbrakk>\<^sub>U)" "\<lbrakk>\<not> P\<rbrakk>\<^sub>U = - \<lbrakk>P\<rbrakk>\<^sub>U"
  by (auto simp add: pred_rel_def pred)

lemma rel_interp [rel]:
  "\<lbrakk>P ;; Q\<rbrakk>\<^sub>U = \<lbrakk>P\<rbrakk>\<^sub>U \<Zcomp> \<lbrakk>Q\<rbrakk>\<^sub>U" "\<lbrakk>II\<rbrakk>\<^sub>U = Id"
  by (auto simp add: pred_rel_def pred)

lemma rel_pre [rel_transfer]: "\<lbrakk>pre P\<rbrakk>\<^sub>U = Domain \<lbrakk>P\<rbrakk>\<^sub>U"
  by (auto simp add: pre_def Domain_def pred_rel_def)

lemma rel_post [rel_transfer]: "\<lbrakk>post P\<rbrakk>\<^sub>U = Range \<lbrakk>P\<rbrakk>\<^sub>U"
  by (auto simp add: post_def Range_def pred_rel_def)

lemma rel_eq_transfer [rel_transfer]: "P = Q \<longleftrightarrow> \<lbrakk>P\<rbrakk>\<^sub>U = \<lbrakk>Q\<rbrakk>\<^sub>U"
  by (auto simp add: pred_rel_def)

lemma rel_refine_transfer [rel_transfer]: "P \<sqsubseteq> Q \<longleftrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>U \<subseteq> \<lbrakk>P\<rbrakk>\<^sub>U"
  by (auto simp add: pred_rel_def pred_refine_iff)

lemma rel_pointwise_transfer [rel_transfer]: "P (s, s') \<longleftrightarrow> (s, s') \<in> \<lbrakk>P\<rbrakk>\<^sub>U"
  by (auto simp: pred_rel_def)

method rel_transfer = (simp add: rel_transfer rel)

method rel_simp uses add = (rel_transfer, expr_simp add: relcomp_unfold add)
method rel_auto uses add = (rel_transfer, expr_auto add: relcomp_unfold add)

subsection \<open> Relational Properties \<close>

definition [rel_transfer]: "Functional P = functional \<lbrakk>P\<rbrakk>\<^sub>U"

definition [rel_transfer]: "Injective P = injective \<lbrakk>P\<rbrakk>\<^sub>U"

subsection \<open> Algebraic Laws \<close>

interpretation upred_semiring: semiring_1
  where times = seq and one = skip and zero = false\<^sub>h and plus = Lattices.sup
  by (unfold_locales; pred_auto add: sup_fun_def)+

declare upred_semiring.power_Suc [simp del]

text \<open> We introduce the power syntax derived from semirings \<close>

abbreviation upower :: "'\<alpha> hrel \<Rightarrow> nat \<Rightarrow> '\<alpha> hrel" (infixr "\<^bold>^" 80) where
"upower P n \<equiv> upred_semiring.power P n"

translations
  "P \<^bold>^ i" <= "CONST power.power II op ;; P i"
  "P \<^bold>^ i" <= "(CONST power.power II op ;; P) i"

lemma upower_interp [rel]: "\<lbrakk>P \<^bold>^ i\<rbrakk>\<^sub>U = \<lbrakk>P\<rbrakk>\<^sub>U ^^ i"
  by (induct i arbitrary: P)
     ((auto; pred_auto add: pred_rel_def), simp add: rel_interp(1) upred_semiring.power_Suc2)

lemma upower_inductl: "Q \<sqsubseteq> ((P ;; Q) \<sqinter> R) \<Longrightarrow> Q \<sqsubseteq> P \<^bold>^ n ;; R"
proof (induct n)
  case 0
  then show ?case apply rel_auto
    by (metis (no_types, lifting) rel_pointwise_transfer subsetD)
next
  case (Suc n)
  then show ?case
    apply rel_auto
    by (smt (verit, ccfv_SIG) rel_interp(1) rel_pointwise_transfer rel_refine_transfer relcomp.intros relpow_Suc_D2' subset_iff upower_interp)
qed

lemma upower_inductr:
  assumes "Q \<sqsubseteq> R \<sqinter> (Q ;; P)"
  shows "Q \<sqsubseteq> R ;; (P \<^bold>^ n)"
  apply (induct n)
    apply (rel_auto, metis assms pred_refine_iff rel_pointwise_transfer sup1I1)
    apply (rel_auto, smt (verit, ccfv_SIG) Collect_mono_iff assms old.prod.case pred_refine_iff pred_rel_def rel_interp(1) rel_pointwise_transfer relcomp.relcompI sup1CI) 
  done

definition kleene_star :: "'\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("_\<^sup>\<star>" [999] 999) where
"P\<^sup>\<star> = (\<Sqinter>i. P\<^bold>^i)"

lemma kleene_rep_eq[rel]: "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U = \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*"
proof 
  have "((a, b) \<in> \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*) \<Longrightarrow> (a,b) \<in> \<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U" for a b
    apply (induct rule: rtrancl.induct)
     apply (simp_all add: pred_rel_def kleene_star_def)
     apply (metis (full_types) power.power.power_0 prod.simps(2) skip_def)
    by (metis (mono_tags, lifting) case_prodI upred_semiring.power_Suc2 utp_rel.seq_def)
  then show "\<lbrakk>P\<rbrakk>\<^sub>U\<^sup>* \<subseteq> \<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U"
    by auto
next
  have "((a, b) \<in> \<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U) \<Longrightarrow> (a,b) \<in> \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*" for a b
    apply (simp add: kleene_star_def pred_rel_def)
    by (metis mem_Collect_eq pred_rel_def rtrancl_power upower_interp)
  then show "\<lbrakk>P\<^sup>\<star>\<rbrakk>\<^sub>U \<subseteq> \<lbrakk>P\<rbrakk>\<^sub>U\<^sup>*"
    by force
qed

theorem ustar_inductl:
  assumes "Q \<sqsubseteq> R" "Q \<sqsubseteq> P ;; Q"
  shows "Q \<sqsubseteq> P\<^sup>\<star> ;; R"
  apply (insert assms)
  apply (rel_auto)
  oops
  

lemma seqr_middle: "vwb_lens x \<Longrightarrow> P ;; Q = (\<Sqinter> v. P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup><\<rbrakk>)"
  by (pred_auto, metis vwb_lens.put_eq)

lemma precond_equiv: "true ;; P = P \<longleftrightarrow> (in\<alpha> \<sharp> P)"
  by pred_auto

lemma precond_simp [simp]: "in\<alpha> \<sharp> P \<Longrightarrow> true ;; P = P"
  by (simp add: precond_equiv)

lemma postcond_equiv: "P ;; true = P \<longleftrightarrow> (out\<alpha> \<sharp> P)"
  by (pred_auto)

lemma postcond_simp: "out\<alpha> \<sharp> P \<Longrightarrow> P ;; true = P"
  by (simp add: postcond_equiv)

lemma "($x\<^sup>< = $x\<^sup>>)\<^sub>e ;; ($x\<^sup>< = $x\<^sup>>)\<^sub>e = ($x\<^sup>< = $x\<^sup>>)\<^sub>e"
  by pred_auto

lemma assigns_skip: "\<langle>id\<rangle>\<^sub>a = II"
  by pred_auto

lemma assigns_comp: "\<langle>\<sigma>\<rangle>\<^sub>a ;; \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  by pred_auto

lemma assigns_cond: "\<langle>\<sigma>\<rangle>\<^sub>a \<^bold>\<lhd> b \<^bold>\<rhd> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<sigma> \<triangleleft> b \<triangleright> \<rho>\<rangle>\<^sub>a"
  by pred_auto  

end

