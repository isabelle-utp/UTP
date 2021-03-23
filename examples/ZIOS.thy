theory ZIOS
  imports "Z_Toolkit.Z_Toolkit_Pretty" "../utp"
begin                                                    

unbundle UTP_Syntax

definition [lens_defs]: "pfun_collection_lens = pfun_lens"

adhoc_overloading collection_lens pfun_collection_lens

lemma pfun_collection_lens_mwb [simp]: "mwb_lens (pfun_collection_lens e)"
  by (simp add: pfun_collection_lens_def)

lemma source_pfun_collection_lens: "\<S>\<^bsub>pfun_collection_lens i\<^esub> = {f. i \<in> pdom(f)}"
  by (auto simp add: lens_defs lens_source_def, metis pfun_upd_ext)

lemma defined_pfun_collection_lens [simp]: 
  "\<lbrakk> vwb_lens x; $x \<sharp> (@e)\<^sub>e \<rbrakk> \<Longrightarrow> \<^bold>D(x[e]) = (e \<in> pdom($x))\<^sub>e"
  by (simp add: lens_defined_def src_dyn_lens unrest source_ns_alpha source_pfun_collection_lens)
     (simp add: lens_defs wb_lens.source_UNIV)

text \<open> The meaning of scene equivalence outside of a partial function selection. \<close>

lemma scene_equiv_outside_pfun:
  assumes "vwb_lens x" "$x \<sharp> (@e)\<^sub>e" "e s\<^sub>1 \<in> pdom (get\<^bsub>x\<^esub> s\<^sub>1)"
  shows "s\<^sub>1 \<approx>\<^sub>S s\<^sub>2 on - \<lbrakk>(x[@e])\<^sub>v\<rbrakk>\<^sub>\<sim> 
        \<longleftrightarrow> 
        (s\<^sub>1 \<approx>\<^sub>S s\<^sub>2 on - \<lbrakk>x\<rbrakk>\<^sub>\<sim> \<and> - {e s\<^sub>1} \<lhd> get\<^bsub>x\<^esub> s\<^sub>1 = - {e s\<^sub>1} \<lhd> get\<^bsub>x\<^esub> s\<^sub>2)"  
  using assms
  apply (auto simp add: scene_equiv_def scene_override_commute unrest)
    apply (simp_all add: unrest_lens)
    apply (simp_all add: lens_defs)
    apply (metis vwb_lens.put_eq)
   apply (metis Compl_iff Partial_Fun.pdom_res_upd_out all_not_in_conv insert_not_empty mwb_lens_weak singletonD vwb_lens_mwb weak_lens.put_get)
  apply (metis Diff_insert_absorb compl_bot_eq empty_iff pdom_res_UNIV pfun_pdom_antires_upd pfun_upd_ext singletonI)
  done

alphabet ('i, 'o, 's) ios = 
  inp :: "'i"
  out :: "'o"
  st :: "'s"


definition ZDelta :: "('s \<Rightarrow> \<bool>) \<Rightarrow> _" ("\<Delta>[_]") where
[expr_defs]: "ZDelta P = (P\<^sup>< \<and> P\<^sup>>)\<^sub>e \<up> (st \<times> st)"

definition ZXi ("\<Xi>[_]") where
[expr_defs]: "ZXi P = (P\<^sup>< \<and> (\<^bold>v\<^sup>< = \<^bold>v\<^sup>>))\<^sub>e \<up> (st \<times> st)"

definition ZBefore ("[_]\<^sup><") where
[expr_defs]: "ZBefore P = P\<^sup>< \<up> (st \<times> st)"

definition ZAfter ("[_]\<^sup>>") where
[expr_defs]: "ZAfter P = P\<^sup>> \<up> (st \<times> st)"

definition ZedSchema :: "('s \<Rightarrow> \<bool>) \<Rightarrow> ('s \<Rightarrow> \<bool>) \<Rightarrow> _" ("[_ | _]") where
[expr_defs]: "ZedSchema P Q \<equiv> (P \<and> Q)\<^sub>e"

expr_ctr ZDelta (0)
expr_ctr ZXi (0)
expr_ctr ZBefore (0)
expr_ctr ZAfter (0)

expr_ctr ZedSchema (0 1)

no_notation Set.member ("(_/ : _)" [51, 51] 50)

syntax
  "_zed_input"  :: "id \<Rightarrow> logic" ("(_)?" [1000] 1000)
  "_zed_output" :: "id \<Rightarrow> logic" ("(_)!" [1000] 1000)

translations
  "_zed_input x"  == "(_sexp_var (_svid_fst (_svid_dot (_svid (CONST inp)) (_svid x))))"
  "_zed_output x" == "(_sexp_var (_svid_snd (_svid_dot (_svid (CONST out)) (_svid x))))"

end