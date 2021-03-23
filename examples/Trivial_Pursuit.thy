theory Trivial_Pursuit
  imports ZIOS
begin

lit_vars

typedecl Player
typedecl Colour

alphabet LocalScore =
  s :: "Colour set"
 
alphabet GlobalScore =
  score :: "Player \<Zpfun> LocalScore"

definition AnswerLocal :: "Colour \<Rightarrow> LocalScore rel" where
"AnswerLocal c = (s\<^sup>> = s\<^sup>< \<union> {c})\<^sub>u"

definition AnswerGlobal :: "Player \<Rightarrow> Colour \<Rightarrow> GlobalScore rel" where
"AnswerGlobal p c = 
  (p \<in> dom ($score\<^sup><) 
  \<and> {p} \<Zndres> $score\<^sup>> = {p} \<Zndres> $score\<^sup><
  \<and> (($score\<^sup>>) p):s = (($score\<^sup><) p):s \<union> {c})\<^sub>u"

text \<open> We can prove that promoting @{term AnswerLocal} yields @{term AnswerGlobal}. \<close>

lemma promote_AnswerLocal:
  "AnswerLocal c \<Up> score[p] = AnswerGlobal p c"
  apply (rel_simp add: AnswerLocal_def AnswerGlobal_def)
  apply (auto simp add: scene_equiv_outside_pfun unrest)
     apply (simp_all add: scene_equiv_def scene_override_commute unrest)    
     apply (expr_auto)+
  done

end