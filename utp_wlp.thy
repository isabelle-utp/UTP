subsection \<open> Weakest Liberal Preconditions \<close>

theory utp_wlp
  imports utp_rel
begin

named_theorems wp

definition wlp_pred :: "('s\<^sub>1 \<leftrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>2 \<Rightarrow> bool) \<Rightarrow> ('s\<^sub>1 \<Rightarrow> bool)" where
[rel]: "wlp_pred Q r = pre (\<not> (Q \<Zcomp> ((\<not> r\<^sup><)\<^sub>u)) :: ('s\<^sub>1 \<leftrightarrow> 's\<^sub>2))"

expr_ctr wlp_pred

syntax
  "_wlp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "wlp" 60)

translations
  "_wlp Q r" == "CONST wlp_pred Q (r)\<^sub>e"

lemma wlp_seq [wp]: "(P \<Zcomp> Q) wlp b = P wlp (Q wlp b)"
  by (rel_auto)

lemma wlp_assigns [wp]: "\<langle>\<sigma>\<rangle>\<^sub>a wlp b = (\<sigma> \<dagger> b)\<^sub>e"
  by (rel_auto)

end