subsection \<open> Alphabetised Relations \<close>

theory utp_rel
  imports utp_pred utp_pred_laws utp_rel_syntax utp_recursion
begin

subsection \<open> Relational Types \<close>

unbundle UTP_Logic_Syntax

text \<open> An alphabetised relation is simply a predicate whose state-space is a product type. In this
  theory we construct the core operators of the relational calculus, and prove a libary of 
  associated theorems, based on Chapters 2 and 5 of the UTP book~\cite{Hoare&98}. 

  We create type synonyms for alphabetised relations where the input and output alphabet can
  be different, and also homogeneous relations. \<close>

type_synonym ('a, 'b) urel = "('a \<times> 'b) \<Rightarrow> bool"

translations
  (type) "('a, 'b) urel" <= (type) "('a \<times> 'b) \<Rightarrow> bool"

type_synonym 'a hrel = "('a, 'a) urel"

text \<open> The following code sets up pretty-printing for homogeneous relational expressions. We cannot 
  do this via the ``translations'' command as we only want the rule to apply when the input and output
  alphabet types are the same. The code has to deconstruct an expression (function) type, determine 
  that it is relational (product alphabet), and then checks if the types \emph{alpha} and \emph{beta} 
  are the same. If they are, the type is printed as a @{type hrel}. Otherwise, we have no match. 
  We then set up a regular translation for the @{type hrel} type that uses this. \<close>
  
print_translation \<open>
let
fun tr' ctx [ Const (@{type_syntax "prod"},_) $ alpha $ beta
            , Const (@{type_syntax "bool"},t) ] = 
  if (alpha = beta) 
    then Syntax.const @{type_syntax "hrel"} $ alpha
    else raise Match;
in [(@{type_syntax "fun"},tr')]
end
\<close>

subsection \<open> Relational Alphabets \<close>
  
text \<open> We set up convenient syntax to refer to the input and output parts of the alphabet, as is
  common in UTP. Since we are in a product space, these are simply the lenses @{term "fst\<^sub>L"} and
  @{term "snd\<^sub>L"} lifted into alphabets. \<close>

definition in\<alpha> :: "('\<alpha> \<times> '\<beta>) scene" where
[lens_defs, expr_simps]: "in\<alpha> = var_alpha fst\<^sub>L"

definition out\<alpha> :: "('\<alpha> \<times> '\<beta>) scene" where
[lens_defs, expr_simps]: "out\<alpha> \<equiv> var_alpha snd\<^sub>L"

lemma in\<alpha>_idem_scene [simp]: "idem_scene in\<alpha>"
  by (simp add: in\<alpha>_def)

lemma out\<alpha>_idem_scene [simp]: "idem_scene out\<alpha>"
  by (simp add: out\<alpha>_def)

lemma in\<alpha>_out\<alpha>_indeps [simp]: "in\<alpha> \<bowtie>\<^sub>S out\<alpha>" "out\<alpha> \<bowtie>\<^sub>S in\<alpha>"
  by (simp_all add: in\<alpha>_def out\<alpha>_def)

lemma alpha_in_out: "in\<alpha> \<squnion>\<^sub>S out\<alpha> = \<top>\<^sub>S"
proof -
  have "fst\<^sub>L +\<^sub>L snd\<^sub>L \<approx>\<^sub>L 1\<^sub>L"
    by (simp add: fst_snd_id_lens)
  hence "\<lbrakk>fst\<^sub>L\<rbrakk>\<^sub>\<sim> \<squnion>\<^sub>S \<lbrakk>snd\<^sub>L\<rbrakk>\<^sub>\<sim> = \<top>\<^sub>S"
    by (simp add: fst_snd_id_lens one_lens_scene scene_space_lemmas(1))
  thus ?thesis
    by (simp add: in\<alpha>_def out\<alpha>_def var_alpha_def)
qed

subsection \<open> Relational Operators \<close>

text \<open> We define a specialised version of the conditional where the condition can refer only to
  undashed variables, as is usually the case in programs, but not universally in UTP models. 
  We implement this by lifting the condition predicate into the relational state-space with
  construction @{term "\<lceil>b\<rceil>\<^sub><"}. \<close>

definition lift_rcond :: "'a pred \<Rightarrow> ('a, 'b) urel" ("\<lceil>_\<rceil>\<^sub>\<leftarrow>") where
[pred]: "\<lceil>b\<rceil>\<^sub>\<leftarrow> = b\<^sup><"

abbreviation cond_rel :: "('a, 'b) urel \<Rightarrow> ('a \<times> 'b) pred \<Rightarrow> ('a, 'b) urel \<Rightarrow> ('a, 'b) urel" where
"cond_rel P B Q \<equiv> cond P B Q"

syntax
  "_rcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<^bold>\<lhd> _ \<^bold>\<rhd>/ _)" [52,0,53] 52)

translations
  "_rcond P b Q" == "CONST cond_rel P \<lceil>(b)\<^sub>e\<rceil>\<^sub>\<leftarrow> Q"

text \<open> Sequential composition is heterogeneous, and simply requires that the output alphabet
  of the first matches then input alphabet of the second. \<close>

definition seq :: "('a, 'b) urel \<Rightarrow> ('b, 'c) urel \<Rightarrow> ('a, 'c) urel" (infixl ";;" 55) where
[pred]: "P ;; Q = (\<lambda> (s, s'). \<exists> s\<^sub>0. P (s, s\<^sub>0) \<and> Q (s\<^sub>0, s'))"

expr_ctr seq (0 1)

text \<open> We also set up a homogeneous sequential composition operator, and versions of @{term true}
  and @{term false} that are explicitly typed by a homogeneous alphabet. \<close>

abbreviation seqh :: "'s hrel \<Rightarrow> 's hrel \<Rightarrow> 's hrel" (infixr ";;\<^sub>h" 61) where
"seqh P Q \<equiv> (P ;; Q)"

abbreviation truer :: "'s hrel" ("true\<^sub>h") where
"truer \<equiv> true"

abbreviation falser :: "'s hrel" ("false\<^sub>h") where
"falser \<equiv> false"

text \<open> We define the relational converse operator as an alphabet extrusion on the bijective
  lens @{term swap\<^sub>L} that swaps the elements of the product state-space. \<close>

abbreviation conv_r :: "('a, 'b) urel \<Rightarrow> ('b, 'a) urel" ("_\<^sup>-" [999] 999) where
"conv_r P \<equiv> aext P swap\<^sub>L"

text \<open> Assignment is defined using substitutions, where latter defines what each variable should
  map to. This approach, which is originally due to Back~\cite{Back1998}, permits more general 
  assignment expressions. The definition of the operator identifies the after state binding, $b'$, 
  with the substitution function applied to the before state binding $b$. \<close>

definition assigns_r :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) urel" where
[pred]: "assigns_r \<sigma> = (\<lambda> (s, s'). s' = \<sigma> s)"

adhoc_overloading uassigns assigns_r

text \<open> Relational identity, or skip, leaves all variables unchanged. \<close>

definition skip :: "'a hrel" where
[pred]: "skip = (\<lambda> (s, s'). s' = s)"

adhoc_overloading uskip skip

text \<open> Non-deterministic assignment, also known as ``choose'', assigns an arbitrarily chosen value 
  to the given variable \<close>

definition ndet_assign :: "('a \<Longrightarrow> 's) \<Rightarrow> 's hrel" where
[pred]: "ndet_assign x = (\<Sqinter> v. x := \<guillemotleft>v\<guillemotright>)"

syntax "_ndet_assign" :: "svid \<Rightarrow> logic" ("_ := *" [75] 76)
translations "_ndet_assign x" == "CONST ndet_assign x"

text \<open> We set up iterated sequential composition which iterates an indexed predicate over the
  elements of a list. \<close>

definition seqr_iter :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b hrel) \<Rightarrow> 'b hrel" where
[pred]: "seqr_iter xs P = foldr (\<lambda> i Q. P(i) ;; Q) xs II"

syntax "_seqr_iter" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3;; _ : _ \<bullet>/ _)" [0, 0, 10] 10)
translations ";; x : l \<bullet> P" \<rightleftharpoons> "(CONST seqr_iter) l (\<lambda>x. P)"

text \<open> We also define the alphabetised skip operator that identifies all input and output variables
  in the given alphabet scene. All other variables are unrestricted. We also set up syntax for it. \<close>
  
definition skip_ra :: "'s scene \<Rightarrow> 's hrel" where
[pred]: "skip_ra a = (\<lambda> (s, s'). s' \<approx>\<^sub>S s on a)"

definition test :: "('s \<Rightarrow> bool) \<Rightarrow> 's hrel" where
[pred]: "test b = (\<lambda> (s, s'). b s \<and> s' = s)"

adhoc_overloading utest test

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

subsection \<open> Predicate Semantics \<close>

lemma pred_skip: "II = ($\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e"
  by pred_simp

lemma pred_seq_hom:
  "P ;; Q = (\<exists> v\<^sub>0. [ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P \<and> [ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q)\<^sub>e"
  by pred_auto

lemma pred_seq: 
  "P ;; Q = (\<exists> v\<^sub>0. \<lparr> \<^bold>v\<^sup>< \<leadsto> $\<^bold>v\<^sup><, \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> \<rparr> \<dagger> P \<and> \<lparr> \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright>, \<^bold>v\<^sup>> \<leadsto> $\<^bold>v\<^sup>> \<rparr> \<dagger> Q)\<^sub>e"
  by (pred_auto)

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

lemma rel_lattice_interp [rel]:
  "\<lbrakk>P \<sqinter> Q\<rbrakk>\<^sub>U = \<lbrakk>P\<rbrakk>\<^sub>U \<union> \<lbrakk>Q\<rbrakk>\<^sub>U" "\<lbrakk>P \<squnion> Q\<rbrakk>\<^sub>U = \<lbrakk>P\<rbrakk>\<^sub>U \<inter> \<lbrakk>Q\<rbrakk>\<^sub>U" "\<lbrakk>\<top>\<rbrakk>\<^sub>U = {}" "\<lbrakk>\<bottom>\<rbrakk>\<^sub>U = UNIV"
  by (auto simp add: pred_rel_def)

lemma rel_complete_lattice_interp [rel]:
  "\<lbrakk>\<Sqinter> i\<in>I. P(i)\<rbrakk>\<^sub>U = (\<Union> i\<in>I. \<lbrakk>P(i)\<rbrakk>\<^sub>U)" "\<lbrakk>\<Squnion> i\<in>I. P(i)\<rbrakk>\<^sub>U = (\<Inter> i\<in>I. \<lbrakk>P(i)\<rbrakk>\<^sub>U)"
  by (auto simp add: pred_rel_def)

lemma rel_interp [rel]:
  "\<lbrakk>P ;; Q\<rbrakk>\<^sub>U = \<lbrakk>P\<rbrakk>\<^sub>U \<Zcomp> \<lbrakk>Q\<rbrakk>\<^sub>U" "\<lbrakk>II\<rbrakk>\<^sub>U = Id"
  by (auto simp add: pred_rel_def pred)

lemma rel_eq_transfer [rel_transfer]: "P = Q \<longleftrightarrow> \<lbrakk>P\<rbrakk>\<^sub>U = \<lbrakk>Q\<rbrakk>\<^sub>U"
  by (auto simp add: pred_rel_def)

lemma rel_refine_transfer [rel_transfer]: "P \<sqsubseteq> Q \<longleftrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>U \<subseteq> \<lbrakk>P\<rbrakk>\<^sub>U"
  by (auto simp add: pred_rel_def pred_refine_iff)

(* I think this law is too general to be a transfer law *)

lemma rel_pointwise_transfer (*[rel_transfer]*): "P (s, s') \<longleftrightarrow> (s, s') \<in> \<lbrakk>P\<rbrakk>\<^sub>U"
  by (auto simp: pred_rel_def)

method rel_transfer = (simp only: rel_transfer rel)

method rel_simp uses add = (rel_transfer, expr_simp add: relcomp_unfold add)
method rel_auto uses add = (rel_transfer, expr_auto add: relcomp_unfold add)

subsection \<open> Relational Properties \<close>

text \<open> We describe some properties of relations, including functional and injective relations. We
  also provide operators for extracting the domain and range of a UTP relation. \<close>

definition [rel_transfer]: "Functional P = functional \<lbrakk>P\<rbrakk>\<^sub>U"

lemma Functional_alt_def [pred]: "Functional R \<longleftrightarrow> II \<sqsubseteq> R\<^sup>- ;; R"
  by (rel_auto add: pred_rel_def Id_def single_valued_def)

definition [rel_transfer]: "Injective P = injective \<lbrakk>P\<rbrakk>\<^sub>U"

lemma Injective_alt_def [pred]: "Injective R \<longleftrightarrow> (Functional R \<and> II \<sqsubseteq> R ;; R\<^sup>-)"
  by (rel_auto add: pred_rel_def injective_def Id_def)

definition pre :: "('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>1 \<Rightarrow> bool)" 
  where [pred]: "pre P = (\<lambda> s. \<exists> s'. P (s, s'))"

definition post :: "('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>2 \<Rightarrow> bool)" 
  where [pred]: "post P = (\<lambda> s'. \<exists> s. P (s, s'))"

expr_ctr pre

expr_ctr post

lemma pred_pre: "pre P = (\<exists> s. P \<lbrakk>\<guillemotleft>s\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk>)\<^sub><"
  by (expr_simp add: pre_def Domain_iff)

lemma pred_pre_liberate: "pre P = (P \\ out\<alpha>)\<^sub><"
  by (expr_auto add: pre_def)

lemma rel_pre [rel_transfer]: "\<lbrakk>pre P\<rbrakk>\<^sub>U = Domain \<lbrakk>P\<rbrakk>\<^sub>U"
  by (auto simp add: pre_def Domain_def pred_rel_def)

lemma rel_post [rel_transfer]: "\<lbrakk>post P\<rbrakk>\<^sub>U = Range \<lbrakk>P\<rbrakk>\<^sub>U"
  by (auto simp add: post_def Range_def pred_rel_def)

subsection \<open> Algebraic Laws \<close>

interpretation upred_semiring: semiring_1
  where times = seq and one = skip and zero = false\<^sub>h and plus = Lattices.sup
  by (unfold_locales; pred_auto add: sup_fun_def)+

declare upred_semiring.power_Suc [simp del]

text \<open> We introduce the power syntax derived from semirings. We can't use the standard @{class power},
  because this would need to apply to any relation, whereas power only applies to homogeneous relations. \<close>
 
abbreviation upower :: "'\<alpha> hrel \<Rightarrow> nat \<Rightarrow> '\<alpha> hrel" (infixr "\<^bold>^" 80) where
"upower P n \<equiv> upred_semiring.power P n"

translations
  "P \<^bold>^ i" <= "CONST power.power II op ;; P i"
  "P \<^bold>^ i" <= "(CONST power.power II op ;; P) i"

definition ustar :: "'\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("_\<^sup>\<star>" [999] 999) where
"P\<^sup>\<star> = (\<Sqinter>i. P\<^bold>^i)"

lemma precond_equiv: "true ;; P = P \<longleftrightarrow> (in\<alpha> \<sharp> P)"
  by pred_auto

lemma precond_simp [simp]: "in\<alpha> \<sharp> P \<Longrightarrow> true ;; P = P"
  by (simp add: precond_equiv)

lemma postcond_equiv: "P ;; true = P \<longleftrightarrow> (out\<alpha> \<sharp> P)"
  by (pred_auto)

lemma postcond_simp: "out\<alpha> \<sharp> P \<Longrightarrow> P ;; true = P"
  by (simp add: postcond_equiv)

end

