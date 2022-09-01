section \<open> Relation Syntax \<close>

theory utp_rel_syntax
    imports "Z_Toolkit.Z_Toolkit" "Shallow-Expressions.Shallow_Expressions"
begin
                    
unbundle Expression_Syntax Z_Syntax

consts
  ucond    :: "'p \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> 'p"
  useq     :: "'p \<Rightarrow> 'q \<Rightarrow> 'r" (infixl ";;" 55)
  uassigns :: "('a, 'b) psubst \<Rightarrow> 'p" ("\<langle>_\<rangle>\<^sub>a")
  uskip    :: "'p" ("II")
  utest    :: "('s \<Rightarrow> bool) \<Rightarrow> 'p"

abbreviation (input) useqh :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" (infixr ";;\<^sub>h" 61) where
"useqh P Q \<equiv> (P ;; Q)"

expr_constructor ucond (0 2)
expr_constructor useq (0 1)
expr_constructor useqh (0 1)
expr_constructor uassigns
expr_constructor uskip
expr_constructor utest

syntax 
  "_ucond"   :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<lhd> _ \<rhd>/ _)" [52,0,53] 52)
  "_uassign" :: "svid \<Rightarrow> logic \<Rightarrow> logic" (infix ":=" 61)
  "_utest"   :: "logic \<Rightarrow> logic" ("\<questiondown>_?")

translations
  "_ucond P b Q" == "CONST ucond P (b)\<^sub>e Q"
  "_uassign x e" == "CONST uassigns (CONST subst_upd (CONST subst_id) x (e)\<^sub>e)"
  "_uassign (_svid_tuple (_of_svid_list (x +\<^sub>L y))) e" <= "_uassign (x +\<^sub>L y) e" 
  "_utest P" == "CONST utest (P)\<^sub>e"

end