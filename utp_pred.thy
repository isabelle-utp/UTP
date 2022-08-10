section \<open> UTP Predicates \<close>

theory utp_pred
  imports 
    "HOL-Library.Order_Continuity"
    "Z_Toolkit.Z_Toolkit" 
    "Shallow-Expressions.Shallow_Expressions"
begin
                    
unbundle Expression_Syntax Z_Syntax

subsection \<open> Core Definitions \<close>

text \<open> We collect all definitional equations in a theorem attribute, to aid proof automation. \<close>

named_theorems pred

type_synonym 's pred = "'s \<Rightarrow> bool"

definition true_pred :: "'s pred" ("true") where [pred]: "true_pred = (True)\<^sub>e"
definition false_pred :: "'s pred" ("false") where [pred]: "false_pred = (False)\<^sub>e"

definition conj_pred :: "'s pred \<Rightarrow> 's pred \<Rightarrow> 's pred" where
[pred]: "conj_pred = inf"

definition disj_pred :: "'s pred \<Rightarrow> 's pred \<Rightarrow> 's pred" where
[pred]: "disj_pred = sup"

definition not_pred :: "'s pred \<Rightarrow> 's pred" where
[pred]: "not_pred = uminus"

definition diff_pred :: "'s pred \<Rightarrow> 's pred \<Rightarrow> 's pred" where
[pred]: "diff_pred = minus"

definition impl_pred :: "'s pred \<Rightarrow> 's pred \<Rightarrow> 's pred" where
[pred]: "impl_pred P Q = (\<lambda>s. P s \<longrightarrow> Q s)"

subsection \<open> Syntax \<close>

text \<open> We want to remain as close as possible to the mathematical UTP syntax, but also
       want to be conservative with HOL. For this reason we chose not to steal syntax
       from HOL, but where possible use polymorphism to allow selection of the appropriate
       operator (UTP vs. HOL). Thus we will first remove the standard syntax for conjunction,
       disjunction, and negation, and replace these with overloaded definitions. We
       similarly use polymorphic constants for the other predicate calculus operators. \<close>

consts 
  uconj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  udisj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" 
  unot  :: "'a \<Rightarrow> 'a" 
  uimplies :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

adhoc_overloading 
  uconj conj and uconj conj_pred and
  udisj disj and udisj disj_pred and
  unot Not and unot not_pred and
  uimplies implies and uimplies impl_pred

text \<open> The following bundle sets up the syntax for our overloaded operators, following the same
  syntax provide in HOL. \<close>

bundle UTP_Logic_Syntax
begin

no_notation 
  conj (infixr "\<and>" 35) and 
  disj (infixr "\<or>" 30) and 
  Not ("\<not> _" [40] 40) and 
  implies (infixr "\<longrightarrow>" 25)

notation 
  uconj (infixr "\<and>" 35) and 
  udisj (infixr "\<or>" 30) and 
  unot ("\<not> _" [40] 40) and 
  uimplies (infixr "\<longrightarrow>" 25)

end

unbundle UTP_Logic_Syntax

subsection \<open> Proof Strategy \<close>

lemma pred_refine_iff: "P \<sqsubseteq> Q \<longleftrightarrow> (\<forall> s. Q s \<longrightarrow> P s)"
  by (simp add: ref_by_bool_def ref_by_fun_def)

lemma pred_ref_iff_le: "(f :: 's pred) \<sqsubseteq> g \<longleftrightarrow> g \<le> f"
  by (simp add: le_fun_def pred_refine_iff)

method pred_simp uses assms add = (insert assms, (simp add: pred expr_simps add)?; expr_simp add: pred_refine_iff add)
method pred_auto uses assms add = (insert assms, (simp add: pred expr_simps add)?; expr_auto add: pred_refine_iff add)

declare expr_if_def [pred]

subsection \<open> Algebraic Structures \<close>

interpretation pred_ba: boolean_algebra diff_pred not_pred conj_pred "(\<sqsupseteq>)" "(\<sqsupset>)"
  disj_pred false_pred true_pred
  by (unfold_locales; pred_auto add: sref_by_fun_def)

lemmas ref_antisym = pred_ba.order.antisym

interpretation ref_lattice: complete_lattice Sup Inf sup "(\<sqsubseteq>)" "(\<sqsubset>)" inf true_pred false_pred
  by (unfold_locales, pred_auto)+

lemma ref_by_pred_is_leq: "((\<sqsubseteq>) :: 'a pred \<Rightarrow> 'a pred \<Rightarrow> bool) = (\<ge>)"
  by (simp add: fun_eq_iff pred_ref_iff_le)

subsection \<open> Lattice syntax \<close>

text \<open> In accordance with \cite{hoare1998}, we turn the lattice operators upside down \<close>

bundle utp_lattice_syntax
begin

notation
  bot ("\<top>") and
  top ("\<bottom>") and
  inf  (infixl "\<squnion>" 70) and
  sup  (infixl "\<sqinter>" 65) and
  Inf  ("\<Squnion> _" [900] 900) and
  Sup  ("\<Sqinter> _" [900] 900)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)

end

unbundle utp_lattice_syntax

subsection \<open> Substitution Laws \<close>

lemma subst_pred [usubst]:
  "\<sigma> \<dagger> true = true"
  "\<sigma> \<dagger> false = false"
  "\<sigma> \<dagger> (P \<and> Q) = ((\<sigma> \<dagger> P) \<and> (\<sigma> \<dagger> Q))"
  "\<sigma> \<dagger> (P \<or> Q) = ((\<sigma> \<dagger> P) \<or> (\<sigma> \<dagger> Q))"
  "\<sigma> \<dagger> (P \<longrightarrow> Q) = ((\<sigma> \<dagger> P) \<longrightarrow> (\<sigma> \<dagger> Q))"
  "\<sigma> \<dagger> (\<not> P) = (\<not> (\<sigma> \<dagger> P))"
  by pred_auto+

lemma subst_INF_SUP [usubst]:
  "\<sigma> \<dagger> (\<Sqinter> i. P(i)) = (\<Sqinter> i. \<sigma> \<dagger> P(i))"
  "\<sigma> \<dagger> (\<Sqinter> i\<in>I. P(i)) = (\<Sqinter> i\<in>I. \<sigma> \<dagger> P(i))"
  "\<sigma> \<dagger> (\<Squnion> i. P(i)) = (\<Squnion> i. \<sigma> \<dagger> P(i))"
  "\<sigma> \<dagger> (\<Squnion> i\<in>I. P(i)) = (\<Squnion> i\<in>I. \<sigma> \<dagger> P(i))"
  by (pred_auto add: image_image)+

subsection \<open> Unrestriction Laws \<close>

lemma unrest_pred [unrest]:
  "a \<sharp> true" "a \<sharp> false"
  "\<lbrakk> a \<sharp> P; a \<sharp> Q \<rbrakk> \<Longrightarrow> a \<sharp> P \<and> Q"
  "\<lbrakk> a \<sharp> P; a \<sharp> Q \<rbrakk> \<Longrightarrow> a \<sharp> P \<or> Q"
  "\<lbrakk> a \<sharp> P; a \<sharp> Q \<rbrakk> \<Longrightarrow> a \<sharp> P \<longrightarrow> Q"
  "a \<sharp> P \<Longrightarrow> a \<sharp> \<not> P"
  by (pred_auto+)

lemma unrest_INF_SUP [unrest]:
  "\<lbrakk> \<And> i. a \<sharp> P(i) \<rbrakk> \<Longrightarrow> a \<sharp> (\<Sqinter> i. P(i))"
  "\<lbrakk> \<And> i. i \<in> I \<Longrightarrow> a \<sharp> P(i) \<rbrakk> \<Longrightarrow> a \<sharp> (\<Sqinter> i\<in>I. P(i))"
  "\<lbrakk> \<And> i. a \<sharp> P(i) \<rbrakk> \<Longrightarrow> a \<sharp> (\<Squnion> i. P(i))"
  "\<lbrakk> \<And> i. i \<in> I \<Longrightarrow> a \<sharp> P(i) \<rbrakk> \<Longrightarrow> a \<sharp> (\<Squnion> i\<in>I. P(i))"
  by (pred_auto add: image_image)+

end
