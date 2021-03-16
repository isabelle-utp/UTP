theory utp_subst
  imports utp_unrest
begin

definition subst_app_pred :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> 's\<^sub>2 set \<Rightarrow> 's\<^sub>1 set" 
  where [pred]: "subst_app_pred \<sigma> P = \<lbrakk>\<sigma> \<dagger> \<lbrakk>P\<rbrakk>\<^sub>P\<rbrakk>\<^sub>u"

adhoc_overloading subst_app subst_app_pred

lemma subst_pred_id [usubst]: "[\<leadsto>] \<dagger> (P :: 's set) = P"
  by pred_auto

lemma subst_pred_unrest [usubst]: 
  fixes P :: "'s set"
  shows "\<lbrakk> vwb_lens x; $x \<sharp> P \<rbrakk> \<Longrightarrow> \<sigma>(x \<leadsto> e) \<dagger> P = \<sigma> \<dagger> P"
  by pred_auto

lemma subst_pred [usubst]: 
  fixes P Q :: "'s set"
  shows 
    "\<sigma> \<dagger> true_pred = true" "\<sigma> \<dagger> false_pred = false"
    "\<sigma> \<dagger> (P \<and> Q) = (\<sigma> \<dagger> P \<and> \<sigma> \<dagger> Q)"
    "\<sigma> \<dagger> (P \<or> Q) = (\<sigma> \<dagger> P \<or> \<sigma> \<dagger> Q)"
    "\<sigma> \<dagger> (P \<Rightarrow> Q) = (\<sigma> \<dagger> P \<Rightarrow> \<sigma> \<dagger> Q)"
    "\<sigma> \<dagger> (\<not> P) = (\<not> \<sigma> \<dagger> P)"
    "\<sigma> \<dagger> (e)\<^sub>u = (\<sigma> \<dagger> e)\<^sub>u"
  by (pred_auto)+

end