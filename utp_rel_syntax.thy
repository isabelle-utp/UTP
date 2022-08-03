section \<open> Relation Syntax \<close>

theory utp_rel_syntax
    imports "Z_Toolkit.Z_Toolkit" "Shallow-Expressions.Shallow_Expressions"
begin
                    
unbundle Expression_Syntax Z_Syntax

consts
  useq     :: "'p \<Rightarrow> 'q \<Rightarrow> 'r" (infixl ";;" 55)
  uassigns :: "('a, 'b) psubst \<Rightarrow> 'p" ("\<langle>_\<rangle>\<^sub>a")
  uskip    :: "'p" ("II")
  utest    :: "('s \<Rightarrow> bool) \<Rightarrow> 'p"

abbreviation (input) useqh :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" (infixr ";;\<^sub>h" 61) where
"useqh P Q \<equiv> (P ;; Q)"

expr_ctr useq (0 1)
expr_ctr useqh (0 1)
expr_ctr uassigns
expr_ctr uskip
expr_ctr utest

syntax 
  "_uassign" :: "svid \<Rightarrow> logic \<Rightarrow> logic" (infix ":=" 61)
  "_utest" :: "logic \<Rightarrow> logic" ("\<questiondown>_?")

translations
  "_uassign x e" == "CONST uassigns (CONST subst_upd (CONST subst_id) x (e)\<^sub>e)"
  "_uassign (_svid_tuple (_of_svid_list (x +\<^sub>L y))) e" <= "_uassign (x +\<^sub>L y) e" 
  "_utest P" == "CONST utest (P)\<^sub>e"

end