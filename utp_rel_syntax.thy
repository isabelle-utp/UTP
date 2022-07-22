section \<open> Relation Syntax \<close>

theory utp_rel_syntax
    imports "Z_Toolkit.Z_Toolkit" "Shallow-Expressions.Shallow_Expressions"
begin
                    
unbundle Expression_Syntax Z_Syntax

consts
  uassigns :: "('a, 'b) psubst \<Rightarrow> 'p" ("\<langle>_\<rangle>\<^sub>a")
  uskip    :: "'p" ("II")
  utest    :: "('s \<Rightarrow> bool) \<Rightarrow> 'p"

expr_ctr uassigns
expr_ctr uskip
expr_ctr utest

syntax "_assign" :: "svid \<Rightarrow> logic \<Rightarrow> logic" (infix ":=" 61)
translations "_assign x e" == "CONST uassigns [x \<leadsto> e]"

syntax "_test" :: "logic \<Rightarrow> logic" ("\<questiondown>_?")
translations "\<questiondown>P?" == "CONST utest (P)\<^sub>e"

end