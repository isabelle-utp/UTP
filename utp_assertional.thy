section \<open> Assertional Reasoning \<close>

theory utp_assertional
  imports utp_rel_laws
begin

subsection \<open> Hoare triples \<close>

text \<open> The main definition is heterogeneous, and allows the postcondition to refer to the pre-state. \<close>

definition hoare_rel_r :: "('s\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>1 \<Rightarrow> 's\<^sub>2 \<Rightarrow> bool) \<Rightarrow> bool" where
[pred]: "hoare_rel_r P C Q = (\<forall> s s'. P s \<and> C (s, s') \<longrightarrow> Q s s')"

adhoc_overloading hoare_rel \<rightleftharpoons> hoare_rel_r

lemma hoare_r_def: "\<^bold>{P\<^bold>} C \<^bold>{Q\<^bold>} \<longleftrightarrow> (P\<^sup>< \<longrightarrow> Q\<^sup>>)\<^sub>e \<sqsubseteq> C"
  by pred_auto

named_theorems hoare and hoare_safe

lemma hoare_meaning: "H{P} C {Q} = (\<forall> s s'. P s \<and> C (s, s') \<longrightarrow> Q s')"
  by (pred_auto)

lemma hoare_alt_def [rel]: "\<^bold>{b\<^bold>}P\<^bold>{c\<^bold>} = (P ;; \<questiondown>c? \<sqsubseteq> \<questiondown>b? ;; P)"
  by (pred_auto)

lemma hoare_assume: "\<^bold>{P\<^bold>}S\<^bold>{Q\<^bold>} \<Longrightarrow> \<questiondown>P? ;; S = \<questiondown>P? ;; S ;; \<questiondown>Q?"
  by (pred_auto)

lemma hoare_pre_assume_1: "\<^bold>{b \<and> c\<^bold>}P\<^bold>{d\<^bold>} = \<^bold>{c\<^bold>}\<questiondown>b? ;; P\<^bold>{d\<^bold>}"
  by (pred_auto)

lemma hoare_pre_assume_2: "\<^bold>{b \<and> c\<^bold>}P\<^bold>{d\<^bold>} = \<^bold>{b\<^bold>}\<questiondown>c? ;; P\<^bold>{d\<^bold>}"
  by pred_auto
                               
lemma hoare_test [hoare_safe]: "`p \<and> b \<longrightarrow> q` \<Longrightarrow> \<^bold>{p\<^bold>}\<questiondown>b?\<^bold>{q\<^bold>}"
  by pred_auto

lemma hoare_gcmd [hoare_safe]: "\<^bold>{p \<and> b\<^bold>}P\<^bold>{q\<^bold>} \<Longrightarrow> \<^bold>{p\<^bold>}\<questiondown>b? ;; P\<^bold>{q\<^bold>}"
  by pred_auto

lemma hoare_r_conj [hoare_safe]: "\<lbrakk> \<^bold>{p\<^bold>}Q\<^bold>{r\<^bold>}; \<^bold>{p\<^bold>}Q\<^bold>{s\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p\<^bold>}Q\<^bold>{r \<and> s\<^bold>}"
  by pred_auto

lemma hoare_r_weaken_pre [hoare]:
  "\<^bold>{p\<^bold>}Q\<^bold>{r\<^bold>} \<Longrightarrow> \<^bold>{p \<and> q\<^bold>}Q\<^bold>{r\<^bold>}"
  "\<^bold>{q\<^bold>}Q\<^bold>{r\<^bold>} \<Longrightarrow> \<^bold>{p \<and> q\<^bold>}Q\<^bold>{r\<^bold>}"
  by pred_auto+

lemma pre_str_hoare_r:
  assumes "`p\<^sub>1 \<longrightarrow> p\<^sub>2`" and "\<^bold>{p\<^sub>2\<^bold>}C\<^bold>{q\<^bold>}"
  shows "\<^bold>{p\<^sub>1\<^bold>}C\<^bold>{q\<^bold>}"
  using assms by pred_auto
    
lemma post_weak_hoare_r:
  assumes "\<^bold>{p\<^bold>}C\<^bold>{q\<^sub>2\<^bold>}" and "`q\<^sub>2 \<longrightarrow> q\<^sub>1`"
  shows "\<^bold>{p\<^bold>}C\<^bold>{q\<^sub>1\<^bold>}" 
  using assms by pred_auto

lemma hoare_r_conseq: "\<lbrakk> \<^bold>{p\<^sub>2\<^bold>}S\<^bold>{q\<^sub>2\<^bold>}; `p\<^sub>1 \<longrightarrow> p\<^sub>2`; `q\<^sub>2 \<longrightarrow> q\<^sub>1` \<rbrakk> \<Longrightarrow> \<^bold>{p\<^sub>1\<^bold>}S\<^bold>{q\<^sub>1\<^bold>}"
  by pred_auto

lemma hoare_r_cut:
  assumes "\<^bold>{b\<^bold>}P\<^bold>{b\<^bold>}" "\<^bold>{b \<and> c\<^bold>}P\<^bold>{c\<^bold>}"
  shows "\<^bold>{b \<and> c\<^bold>}P\<^bold>{b \<and> c\<^bold>}"
  by (simp add: assms(1,2) hoare_r_conj hoare_r_weaken_pre(1))
  
lemma hoare_r_cut_simple: 
  assumes "\<^bold>{b\<^bold>}P\<^bold>{b\<^bold>}" "\<^bold>{c\<^bold>}P\<^bold>{c\<^bold>}"
  shows "\<^bold>{b \<and> c\<^bold>}P\<^bold>{b \<and> c\<^bold>}"
  using assms by pred_auto

lemma hoare_oracle: "\<^bold>{p\<^bold>}false\<^bold>{q\<^bold>}"
  by (simp add: hoare_r_def)

subsection \<open> Weakest precondition \<close>

named_theorems wp

definition wp_pred :: "('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>2 \<Rightarrow> bool) \<Rightarrow> ('s\<^sub>1 \<Rightarrow> bool)" where
[pred]: "wp_pred Q r = pre ((Q ;; r\<^sup><) :: ('s\<^sub>1, 's\<^sub>2) urel)"

expr_constructor wp_pred

syntax
  "_wp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "wp" 60)

translations
  "_wp Q r" == "CONST wp_pred Q (r)\<^sub>e"

lemma wp_seq [wp]: "(P ;; Q) wp b = P wp (Q wp b)"
  by (pred_auto)

lemma wp_false [wp]: "p wp False = false"
  by pred_auto

theorem wp_skip_r [wp]: "II wp r = r"
  by pred_auto

subsection \<open> Total Correctness Hoare Logic \<close>

definition thoare_rel_r :: "('s\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>1 \<Rightarrow> 's\<^sub>2 \<Rightarrow> bool) \<Rightarrow> bool" where
[pred]: "thoare_rel_r P C Q = (\<forall> s. P s \<longrightarrow> (\<forall> s'. C (s, s') \<longrightarrow> Q s s') \<and> (\<exists> s'. C (s, s')))"

adhoc_overloading thoare_rel \<rightleftharpoons> thoare_rel_r

lemma thoare_rel_r_alt_def: "H[P] C [Q] = (H{P} C {Q} \<and> `P \<longrightarrow> C wp True`)"
  by pred_auto

subsection \<open> Weakest liberal precondition \<close>

definition wlp_pred :: "('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>2 \<Rightarrow> bool) \<Rightarrow> ('s\<^sub>1 \<Rightarrow> bool)" where
[pred]: "wlp_pred Q r = pre (\<not> (Q ;; (\<not> r\<^sup><)\<^sub>e) :: ('s\<^sub>1, 's\<^sub>2) urel)"

expr_constructor wlp_pred

syntax
  "_wlp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "wlp" 60)

translations
  "_wlp Q r" == "CONST wlp_pred Q (r)\<^sub>e"

lemma wlp_seq [wp]: "(P ;; Q) wlp b = P wlp (Q wlp b)"
  by (pred_auto)

lemma wlp_true [wp]: "p wlp True = (True)\<^sub>e"
  by pred_auto

lemma wlp_conj [wp]: "P wlp (b \<and> c) = ((P wlp b)\<^sub>e \<and> (P wlp c)\<^sub>e)"
  by (pred_auto)

theorem wlp_cond [wp]: "((P \<lhd> b \<rhd> Q) wlp r) = ((b \<longrightarrow> P wlp r) \<and> (\<not> b \<longrightarrow> Q wlp r))\<^sub>e"
  by pred_auto

theorem wlp_skip_r [wp]: "II wlp r = r"
  by pred_auto

theorem wlp_abort [wp]:
  assumes"r \<noteq> (True)\<^sub>e"
  shows      
  "true wlp r =( False)\<^sub>e"
  using assms by pred_auto

theorem wlp_hoare_link:
  "\<^bold>{P\<^bold>} C \<^bold>{Q\<^bold>} \<longleftrightarrow> `P \<longrightarrow> C wlp Q`"
  by pred_auto

end