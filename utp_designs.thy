theory utp_designs
  imports utp_wlp
begin 

alphabet des_vars = 
  ok :: bool

type_synonym ('s\<^sub>1, 's\<^sub>2) des_rel = "'s\<^sub>1 des_vars_scheme \<leftrightarrow> 's\<^sub>2 des_vars_scheme"

definition design where
[pred]: "design P Q = ((ok\<^sup><)\<^sub>u \<and> P \<Rightarrow> (ok\<^sup>>)\<^sub>u \<and> Q)"

definition rdesign :: "('s\<^sub>1 \<leftrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>1 \<leftrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) des_rel" where
[pred]: "rdesign P Q = design (P \<up> more\<^sub>L\<^sup>2) (Q \<up> more\<^sub>L\<^sup>2)"

syntax 
  "_design"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<turnstile>" 85)
  "_rdesign" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<turnstile>\<^sub>r" 85)
  "_ndesign" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<turnstile>\<^sub>n" 85)

translations 
  "P \<turnstile> Q" == "CONST design P Q"
  "P \<turnstile>\<^sub>r Q" == "CONST rdesign P Q"
  "p \<turnstile>\<^sub>n Q" == "(p\<^sup><)\<^sub>u \<turnstile>\<^sub>r Q"

lemma "false \<turnstile> true = true"
  by (pred_auto)

theorem design_composition_subst:
  assumes
    "$ok\<^sup>> \<sharp> P1" "$ok\<^sup>< \<sharp> P2"
  shows "((P1 \<turnstile> Q1) \<^bold>; (P2 \<turnstile> Q2)) =
         (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1\<lbrakk>true/ok\<^sup>>\<rbrakk> \<^bold>; (\<not> P2))) \<turnstile> (Q1\<lbrakk>true/ok\<^sup>>\<rbrakk> ;; Q2\<lbrakk>true/ok\<^sup><\<rbrakk>))"
proof -
  have "((P1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) = (\<Union> ok\<^sub>0. ((P1 \<turnstile> Q1)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/ok\<^sup>>\<rbrakk> ;; (P2 \<turnstile> Q2)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/ok\<^sup><\<rbrakk>))"
    by (rule seqr_middle, simp)
  also have " ...
        = (((P1 \<turnstile> Q1)\<lbrakk>false/ok\<^sup>>\<rbrakk> ;; (P2 \<turnstile> Q2)\<lbrakk>false/ok\<^sup><\<rbrakk>)
            \<or> ((P1 \<turnstile> Q1)\<lbrakk>true/ok\<^sup>>\<rbrakk> ;; (P2 \<turnstile> Q2)\<lbrakk>true/ok\<^sup><\<rbrakk>))"
    by (rel_auto, (metis (full_types))+)
  also from assms
  have "... = ((((ok\<^sup><)\<^sub>u \<and> P1 \<Rightarrow> Q1\<lbrakk>true/ok\<^sup>>\<rbrakk>) ;; (P2 \<Rightarrow> (ok\<^sup>>)\<^sub>u \<and> Q2\<lbrakk>true/ok\<^sup><\<rbrakk>)) \<or> ((\<not> ((ok\<^sup><)\<^sub>u \<and> P1)) ;; true))"
    by (rel_auto, blast+)
  also have "... = (((\<not>ok\<^sup><)\<^sub>u ;; true\<^sub>h) \<or> ((\<not>P1) ;; true) \<or> (Q1\<lbrakk>true/ok\<^sup>>\<rbrakk> ;; (\<not>P2)) \<or> ((ok\<^sup>>)\<^sub>u \<and> (Q1\<lbrakk>true/ok\<^sup>>\<rbrakk> ;; Q2\<lbrakk>true/ok\<^sup><\<rbrakk>)))"
    by (rel_auto)
  also have "... = (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1\<lbrakk>true/ok\<^sup>>\<rbrakk> ;; (\<not> P2))) \<turnstile> (Q1\<lbrakk>true/ok\<^sup>>\<rbrakk> ;; Q2\<lbrakk>true/ok\<^sup><\<rbrakk>))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma design_composition:
  assumes "$ok\<^sup>> \<sharp> P1" "$ok\<^sup>< \<sharp> P2" "$ok\<^sup>> \<sharp> Q1" "$ok\<^sup>< \<sharp> Q2"
  shows "((P1 \<turnstile> Q1) \<^bold>; (P2 \<turnstile> Q2)) = (((\<not> ((\<not> P1) \<^bold>; true)) \<and> \<not> (Q1 \<^bold>; (\<not> P2))) \<turnstile> (Q1 \<^bold>; Q2))"
  using assms
  by (simp add: design_composition_subst usubst)

theorem rdesign_composition:
  "((P1 \<turnstile>\<^sub>r Q1) \<^bold>; (P2 \<turnstile>\<^sub>r Q2)) = (((\<not> ((\<not> P1) \<^bold>; true)) \<and> \<not> (Q1 \<^bold>; (\<not> P2))) \<turnstile>\<^sub>r (Q1 \<^bold>; Q2))"
  by (simp add: rdesign_def design_composition unrest usubst, rel_auto)

theorem ndesign_composition_wlp:
  "(p\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>1) ;; (p\<^sub>2 \<turnstile>\<^sub>n Q\<^sub>2) = ((p\<^sub>1 \<and> (Q\<^sub>1 wlp p\<^sub>2)) \<turnstile>\<^sub>n (Q\<^sub>1 ;; Q\<^sub>2))"
  by (simp add: rdesign_composition unrest, rel_auto, fastforce+)

end