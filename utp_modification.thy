subsection \<open> Modification of Variable \<close>

theory utp_modification
  imports utp_rel_prog
begin

text \<open> Characterising whether a program affects the valuation of an expression. \<close>

definition not_modifies :: "'s hrel \<Rightarrow> ('a, 's) expr \<Rightarrow> bool" where
[pred]: "not_modifies P e = (\<forall> s s'. P (s, s') \<longrightarrow> e s = e s')"

syntax
  "_not_modifies" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "nmods" 30)

translations
  "_not_modifies P e" == "CONST not_modifies P (e)\<^sub>e"

named_theorems nmods

text \<open> We can determine modification for assignments using symbolic execution. \<close>

lemma assigns_nmods_iff : "\<langle>\<sigma>\<rangle>\<^sub>a nmods e \<longleftrightarrow> \<sigma> \<dagger> (e)\<^sub>e = (e)\<^sub>e"
  by (auto simp add: pred fun_eq_iff subst_app_def)

lemma assigns_nmods [nmods]: "\<sigma> \<dagger> (e)\<^sub>e = (e)\<^sub>e \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>a nmods e"
  by (simp add: assigns_nmods_iff)

lemma Skip_nmods [nmods]: "II nmods e"
  by (simp add: not_modifies_def skip_def)

lemma seq_nmods [nmods]: "\<lbrakk> P nmods e; Q nmods e \<rbrakk> \<Longrightarrow> P ;; Q nmods e"
  by (auto simp add: pred)

text \<open> The following law ignores the condition when checking for modification, which is possibly
  overly restrictive. \<close>

lemma cond_nmods [nmods]: "\<lbrakk> P nmods e; Q nmods e \<rbrakk> \<Longrightarrow> if b then P else Q fi nmods e"
  by (simp add: expr_if_def not_modifies_def rcond_def)

end