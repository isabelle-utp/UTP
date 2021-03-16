subsection \<open> Weakest Liberal Preconditions \<close>

theory utp_wlp
  imports utp_rel
begin

definition wlp_pred :: "('s\<^sub>1 \<leftrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>2 \<Rightarrow> bool) \<Rightarrow> _" where
[pred]: "wlp_pred Q r = pre (\<not> (Q ;; ((\<not> r\<^sup><)\<^sub>u)) :: ('s\<^sub>1 \<leftrightarrow> 's\<^sub>2))"

expr_ctr wlp_pred

syntax
  "_wlp" :: "logic \<Rightarrow> sexpr \<Rightarrow> logic" (infix "wlp" 60)

translations
  "_wlp Q r" == "CONST wlp_pred Q r"

end