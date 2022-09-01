section \<open> Strongest Postcondition Calculus\<close>

theory utp_sp
  imports utp_wlp
begin         

named_theorems sp

definition sp_pred :: "('s\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>2 \<Rightarrow> bool)" where
[pred]: "sp_pred p Q = post((p\<^sup>>)\<^sub>e ;; Q :: ('s\<^sub>1, 's\<^sub>2) urel)"

syntax "_sp" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "sp" 60)

translations
  "_sp p Q" == "CONST sp_pred (p)\<^sub>e Q"

expr_constructor sp_pred

lemma sp_false [sp]: "p sp false = false"
  by pred_simp 

lemma sp_true [sp]: "q \<noteq> false \<Longrightarrow> q sp true = true"
  by pred_simp 
    
lemma sp_assign_r: 
  "vwb_lens x \<Longrightarrow> p sp x := e = (\<exists> v. $x = e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> \<and> p\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)\<^sub>e"
  by (pred_auto, metis vwb_lens_wb wb_lens.get_put, metis vwb_lens.put_eq) 

lemma sp_assigns_r: 
  "p sp \<langle>\<sigma>\<rangle>\<^sub>a = (\<exists> s. $\<^bold>v = \<sigma>\<lbrakk>\<guillemotleft>s\<guillemotright>/\<^bold>v\<rbrakk> \<and> p\<lbrakk>\<guillemotleft>s\<guillemotright>/\<^bold>v\<rbrakk>)\<^sub>e"
  by pred_auto

(*
lemma sp_convr [sp]: "b sp P\<^sup>- = P wp b"
  by (rel_auto)

lemma wp_convr [wp]: "P\<^sup>- wp b = b sp P"
  by (rel_auto)
*)

lemma sp_seqr [sp]: "b sp (P ;; Q) = (b sp P) sp Q"
  by pred_auto

lemma sp_is_postcondition:
  "\<^bold>{p\<^bold>} C \<^bold>{p sp C\<^bold>}"
  by pred_auto
    
lemma sp_strongest_post:
  "`p sp C \<longrightarrow> Q` \<Longrightarrow> \<^bold>{p\<^bold>} C \<^bold>{Q\<^bold>}"
  by pred_auto
        
theorem sp_hoare_link:
  "\<^bold>{p\<^bold>} Q \<^bold>{r\<^bold>} \<longleftrightarrow> `p sp Q \<longrightarrow> r`"
  by pred_auto   

end