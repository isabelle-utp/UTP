subsection \<open> UTP Relations \<close>

theory utp_rel
  imports utp_alpha
begin

consts
  useq     :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 61)
  uassigns :: "('a, 'b) psubst \<Rightarrow> 'c" ("\<langle>_\<rangle>\<^sub>a")
  uskip    :: "'a" ("II")

abbreviation (input) hseq (infixr ";;\<^sub>h" 61) where
"hseq \<equiv> (useq :: 'a \<Rightarrow> 'a \<Rightarrow> 'a)"

named_theorems rel_transfer

type_synonym ('s\<^sub>1, 's\<^sub>2) rpred = "('s\<^sub>1 \<times> 's\<^sub>2) pred"

lemma rel_eq_iff [rel_transfer]: "P = Q \<longleftrightarrow> (\<forall> s s'. \<lbrakk>P\<rbrakk>\<^sub>P (s, s') = \<lbrakk>Q\<rbrakk>\<^sub>P (s, s'))"
  by (simp add: set_eq_iff set_pred_def)

method rel_simp uses add = (simp add: add rel_transfer pred usubst_eval unrest)
method rel_auto uses add = (rel_simp add: add; (expr_simp add: add)?; (auto simp add: alpha_splits add)?)

subsection \<open> Operators \<close>

abbreviation "in\<alpha> \<equiv> var_alpha fst\<^sub>L"
abbreviation "out\<alpha> \<equiv> var_alpha snd\<^sub>L"

adhoc_overloading uskip Id
adhoc_overloading useq relcomp

abbreviation "true\<^sub>h \<equiv> (true :: 's rel)"

definition cond :: "('s\<^sub>1 \<leftrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>1 \<times> 's\<^sub>2 \<Rightarrow> bool) \<Rightarrow> ('s\<^sub>1 \<leftrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>1 \<leftrightarrow> 's\<^sub>2)" where
"cond P B Q = (((B)\<^sub>u \<and> P) \<or> ((\<not>B)\<^sub>u \<and> P))" 

syntax 
  "_cond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<lhd> _ \<rhd>/ _)" [52,0,53] 52)
  "_rcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<^bold>\<lhd> _ \<^bold>\<rhd>/ _)" [52,0,53] 52)

translations
  "_cond P B Q" == "CONST cond P (B)\<^sub>e Q"
  "_rcond P b Q" == "_cond P (b\<^sup><) Q"

definition assigns_rel :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> 's\<^sub>1 \<leftrightarrow> 's\<^sub>2" where
  "assigns_rel \<sigma> = pfun_graph (fun_pfun \<sigma>)"

adhoc_overloading uassigns assigns_rel

syntax "_assign" :: "svid \<Rightarrow> logic \<Rightarrow> logic" (infix ":=" 76)
translations "_assign x e" == "CONST uassigns [x \<leadsto> e]"

definition test :: "'s pred \<Rightarrow> 's rel" where
[expr_defs]: "test P = Id_on (Collect P)"

syntax "_test" :: "logic \<Rightarrow> logic" ("\<questiondown>_?")
translations "\<questiondown>P?" == "CONST test (P)\<^sub>e"

definition ndet_assign :: "('a \<Longrightarrow> 's) \<Rightarrow> 's rel" where
[pred]: "ndet_assign x = (\<Union> v. x := \<guillemotleft>v\<guillemotright>)"

syntax "_ndet_assign" :: "svid \<Rightarrow> logic" ("_ := *" [75] 76)
translations "_ndet_assign x" == "CONST ndet_assign x"

definition [pred]: "pre P = \<lbrakk>Domain P\<rbrakk>\<^sub>P"
definition [pred]: "post P = \<lbrakk>Range P\<rbrakk>\<^sub>P"

subsection \<open> Predicate Semantics \<close>

lemma pred_skip: "\<lbrakk>II\<rbrakk>\<^sub>P = (\<^bold>v\<^sup>> = \<^bold>v\<^sup><)\<^sub>e"
  by (pred_auto)

lemma pred_seq [pred]: "\<lbrakk>P \<^bold>; Q\<rbrakk>\<^sub>P (s, s') = (\<exists> s\<^sub>0. \<lbrakk>P\<rbrakk>\<^sub>P (s, s\<^sub>0) \<and> \<lbrakk>Q\<rbrakk>\<^sub>P (s\<^sub>0, s'))"
  by (expr_auto)

lemma pred_seq': 
  "\<lbrakk>P \<^bold>; Q\<rbrakk>\<^sub>P = (\<exists> v\<^sub>0. \<lparr> \<^bold>v\<^sup>< \<leadsto> $\<^bold>v\<^sup><, \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> \<rparr> \<dagger> \<lbrakk>P\<rbrakk>\<^sub>P \<and> \<lparr> \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright>, \<^bold>v\<^sup>> \<leadsto> $\<^bold>v\<^sup>> \<rparr> \<dagger> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
  by (expr_auto)

lemma pred_assigns [pred]: "\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P (s, s') = (s' = \<sigma> s)"
  by (simp add: expr_defs assigns_rel_def pfun_entries_pabs pfun_graph_pabs)

lemma pred_assigns': "\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P = ($\<^bold>v\<^sup>> = \<sigma>\<^sup><)\<^sub>e"
  by (auto simp add: expr_defs assigns_rel_def lens_defs pfun_entries_pabs pfun_graph_pabs prod.case_eq_if)

subsection \<open> Algebraic Laws \<close>

lemma seqr_middle: "vwb_lens x \<Longrightarrow> P \<^bold>; Q = (\<Union> v. P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk> \<^bold>; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup><\<rbrakk>)"
  by (rel_auto, metis vwb_lens.put_eq)

lemma precond_equiv: "true ;; P = P \<longleftrightarrow> (in\<alpha> \<sharp> P)"
  by (rel_auto)

lemma precond_simp [simp]: "in\<alpha> \<sharp> P \<Longrightarrow> true ;; P = P"
  by (simp add: precond_equiv)

lemma postcond_equiv: "P ;; true = P \<longleftrightarrow> (out\<alpha> \<sharp> P)"
  by (rel_auto)

lemma postcond_simp: "out\<alpha> \<sharp> P \<Longrightarrow> P ;; true = P"
  by (simp add: postcond_equiv)

lemma "($x\<^sup>< = $x\<^sup>>)\<^sub>u ;; ($x\<^sup>< = $x\<^sup>>)\<^sub>u = ($x\<^sup>< = $x\<^sup>>)\<^sub>u"
  by rel_auto

lemma "\<langle>id\<rangle>\<^sub>a = II"
  by rel_auto

lemma "\<langle>\<sigma>\<rangle>\<^sub>a ;; \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  by rel_auto

end