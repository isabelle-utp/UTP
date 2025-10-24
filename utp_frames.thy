section \<open> Frames \<close>

theory utp_frames
  imports utp_modification
begin

subsection \<open> Operators \<close>

text \<open> The frame operator restricts the relation P to only operate on variables in the frame a \<close>

definition frame :: "'s scene \<Rightarrow> 's hrel \<Rightarrow> 's hrel" where
 [pred]: "frame a P = (\<lambda> (s, s'). s \<approx>\<^sub>S s' on - a \<and> P (s, s'))"

text \<open> The frame extension operator take a lens @{term a}, and a relation @{term P}. It constructs
  a relation such that all variables outside of @{term a} are unchanged, and the valuations for
  @{term a} are drawn from @{term P}. Intuitively, this can be seen as extending the alphabet
  of @{term P}. \<close>

definition frame_ext :: "('s\<^sub>1 \<Longrightarrow> ('s\<^sub>2 :: scene_space)) \<Rightarrow> 's\<^sub>1 hrel \<Rightarrow> 's\<^sub>2 hrel" where
  "frame_ext a P = frame (lens_scene a) (P \<up>\<^sub>2 a)"

text \<open> Variable restriction - assign arbitrary values to a scene, effectively forbidding the 
  relation from using its value\<close>

definition rrestr :: "'s scene \<Rightarrow> 's hrel \<Rightarrow> 's hrel" where
[pred]: "rrestr A P = (\<lambda> (s, s'). (\<exists> s\<^sub>0 s\<^sub>0'. P (s \<oplus>\<^sub>S s\<^sub>0 on A, s' \<oplus>\<^sub>S s\<^sub>0' on A)) \<and> s' \<approx>\<^sub>S s on A)" 

abbreviation not_uses :: "'s hrel \<Rightarrow> 's scene \<Rightarrow> bool" where
"not_uses P a \<equiv> P is rrestr a"

syntax 
  "_frame" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]")
  "_frame_ext" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sub>\<up>")
  \<comment> \<open> Not Uses Predicate \<close>
  "_not_uses"     :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infix "nuses" 30)

translations
  "_frame a P" == "CONST frame a P"
  "_frame_ext a P" == "CONST frame_ext a P"
  "_not_uses P a" == "CONST not_uses P a"

lemma nuses_iff [pred]: 
  assumes "idem_scene A"
  shows "P nuses A \<longleftrightarrow> (\<forall> s s' s\<^sub>0. P (s, s') \<longrightarrow> (s \<approx>\<^sub>S s' on A \<and> P (s \<oplus>\<^sub>S s\<^sub>0 on A, s' \<oplus>\<^sub>S s\<^sub>0 on A)))"
  apply (pred_auto assms: assms add: Healthy_def)
  apply (metis scene_override_idem scene_override_overshadow_right)
  apply (metis scene_override_overshadow_left scene_override_overshadow_right)
  apply (metis scene_override_idem scene_override_overshadow_left)
  apply blast
  apply (metis scene_override_idem scene_override_overshadow_right)
  done

lemma nuses_converse_commute: "\<lbrakk> idem_scene A; P nuses A; Q nuses (- A) \<rbrakk> \<Longrightarrow> P ;; Q = Q ;; P"
  apply (simp add: nuses_iff)
  apply (pred_auto)
  apply (metis scene_override.rep_eq scene_override_commute scene_override_idem subscene_eliminate subscene_refl)
  apply (metis scene_equiv_def scene_equiv_sym scene_override_commute)
  done

lemma subst_indep_commute: "\<lbrakk> idem_scene A; A \<sharp>\<^sub>s \<sigma>; -A \<sharp>\<^sub>s \<rho> \<rbrakk> \<Longrightarrow> \<sigma> \<circ>\<^sub>s \<rho> = \<rho> \<circ>\<^sub>s \<sigma>"
  by (expr_auto, metis scene_override_commute scene_override_idem)

lemma nuses_assigns: "\<lbrakk> idem_scene A; A \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>a nuses A"
  by (simp add: nuses_iff expr_defs, auto, simp_all add: assigns_r_def)
     (metis scene_equiv_def scene_equiv_sym scene_override_idem)
  
subsection \<open> Frame laws \<close>

named_theorems frame

lemma frame_all [frame]: "\<Sigma>:[P] = P"
  by (pred_auto)

lemma frame_none [frame]: "\<emptyset>:[P] = (P \<and> II)"
  by (pred_auto add: scene_override_commute)

(*
translations
  "\<lbrace>A\<rbrace> \<sharp> P" <= "_unrest \<lbrakk>\<lbrace>A\<rbrace>\<^sub>F\<rbrakk>\<^sub>F P"
*)

lemma skip_uses_nothing: "idem_scene A \<Longrightarrow> II nuses A"
  by (pred_simp)
     (metis scene_override_idem scene_override_overshadow_left)

(*
lemma frame_commute:
  assumes "\<lbrace>y\<^sup><, y\<^sup>>\<rbrace> \<sharp> P" 
  shows "$x:[P] ;; $y:[Q] = $y:[Q] ;; $x:[P]"
  oops

lemma frame_commute:
  assumes "($y\<^sup><) \<sharp> P" "($y\<^sup>>) \<sharp> P""($x\<^sup><) \<sharp> Q" "($x\<^sup>>) \<sharp> Q" "x \<bowtie> y" 
  shows "$x:[P] ;; $y:[Q] = $y:[Q] ;; $x:[P]"
  oops
*)

lemma frame_miracle [simp]:
  "x:[false] = false"
  by (pred_auto)

lemma frame_skip [simp]:
  "idem_scene x \<Longrightarrow> x:[II] = II"
  by (pred_auto)

lemma frame_assign_in [frame]:
  "\<lbrakk> vwb_lens a; x \<subseteq>\<^sub>L a \<rbrakk> \<Longrightarrow> $a:[x := v] = x := v"
  apply pred_auto
  by (simp add: lens_override_def scene_override_commute)

lemma frame_conj_true [frame]:
  "\<lbrakk>-{x\<^sup><, x\<^sup>>} \<sharp> P; vwb_lens x \<rbrakk> \<Longrightarrow> (P \<and> $x:[true]) = $x:[P]"
  by (pred_auto)

(*lemma frame_is_assign [frame]:
  "vwb_lens x \<Longrightarrow> x:[$x\<acute> =\<^sub>u \<lceil>v\<rceil>\<^sub><] = x := v"
  by (pred_auto)
  *)  

(*
lemma frame_seq [frame]:
  assumes "vwb_lens x" "-{x\<^sup>>,x\<^sup><} \<sharp> P" "-{x\<^sup><,x\<^sup>>} \<sharp> Q"
  shows "$x:[P ;; Q] = $x:[P] ;; $x:[Q]"
  unfolding frame_def apply (pred_auto)
  oops

lemma frame_assign_commute_unrest:
  assumes "vwb_lens x" "x \<bowtie> a" "$a \<sharp> v" "$x\<^sup>< \<sharp> P" "$x\<^sup>> \<sharp> P"
  shows "x := v ;; $a:[P] = $a:[P] ;; x := v"
  using assms apply (pred_auto)
  oops
*)

lemma frame_to_antiframe [frame]:
  "\<lbrakk> x \<bowtie>\<^sub>S y; x \<squnion>\<^sub>S y = \<top>\<^sub>S \<rbrakk> \<Longrightarrow> x:[P] = (-y):[P]"
  apply pred_auto
  by (metis scene_indep_compat scene_indep_override scene_override_commute scene_override_id scene_override_union)+

(*
lemma rel_frext_miracle [frame]: 
  "a:[false]\<^sup>+ = false"
  by (metis false_pred_def frame_miracle trancl_empty)
    
lemma rel_frext_skip [frame]: 
  "idem_scene a \<Longrightarrow> a:[II]\<^sup>+ = II"
  by (metis frame_skip rtrancl_empty rtrancl_trancl_absorb)

lemma rel_frext_seq [frame]:
  "idem_scene a \<Longrightarrow> a:[P ;; Q]\<^sup>+ = (a:[P]\<^sup>+ ;; a:[Q]\<^sup>+)"
  apply (pred_auto)
  oops (* gets nitpicked *)
*)

(*
lemma rel_frext_assigns [frame]:
  "vwb_lens a \<Longrightarrow> a:[\<langle>\<sigma>\<rangle>\<^sub>a]\<^sup>+ = \<langle>\<sigma> \<oplus>\<^sub>s a\<rangle>\<^sub>a"
  by (pred_auto)

lemma rel_frext_rcond [frame]:
  "a:[P \<triangleleft> b \<triangleright>\<^sub>r Q]\<^sup>+ = (a:[P]\<^sup>+ \<triangleleft> b \<oplus>\<^sub>p a \<triangleright>\<^sub>r a:[Q]\<^sup>+)"
  by (pred_auto)

lemma rel_frext_commute: 
  "x \<bowtie> y \<Longrightarrow> x:[P]\<^sup>+ ;; y:[Q]\<^sup>+ = y:[Q]\<^sup>+ ;; x:[P]\<^sup>+"
  apply (pred_auto)
   apply (rename_tac a c b)
   apply (subgoal_tac "\<And>b a. get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> b a) = get\<^bsub>y\<^esub> b")
    apply (metis (no_types, hide_lams) lens_indep_comm lens_indep_get)
   apply (simp add: lens_indep.lens_put_irr2)
  apply (subgoal_tac "\<And>b c. get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> b c) = get\<^bsub>x\<^esub> b")
   apply (subgoal_tac "\<And>b a. get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> b a) = get\<^bsub>y\<^esub> b")
    apply (metis (mono_tags, lifting) lens_indep_comm)
   apply (simp_all add: lens_indep.lens_put_irr2)    
  done
    
lemma antiframe_disj [frame]: "(x:\<lbrakk>P\<rbrakk> \<or> x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P \<or> Q\<rbrakk>"
  by (pred_auto)

lemma antiframe_seq [frame]:
  "\<lbrakk> vwb_lens x; $x\<acute> \<sharp> P; $x \<sharp> Q \<rbrakk>  \<Longrightarrow> (x:\<lbrakk>P\<rbrakk> ;; x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P ;; Q\<rbrakk>"
  apply (pred_auto)
   apply (metis vwb_lens_wb wb_lens_def weak_lens.put_get)
  apply (metis vwb_lens_wb wb_lens.put_twice wb_lens_def weak_lens.put_get)
  done

lemma antiframe_copy_assign:
  "vwb_lens x \<Longrightarrow> (x := \<guillemotleft>v\<guillemotright> ;; x:\<lbrakk>P\<rbrakk> ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright> ;; x:\<lbrakk>P\<rbrakk>)"
  by pred_auto

  
lemma nameset_skip: "vwb_lens x \<Longrightarrow> (\<^bold>n\<^bold>s x \<bullet> II) = II\<^bsub>x\<^esub>"
  by (pred_auto, meson vwb_lens_wb wb_lens.get_put)
    
lemma nameset_skip_ra: "vwb_lens x \<Longrightarrow> (\<^bold>n\<^bold>s x \<bullet> II\<^bsub>x\<^esub>) = II\<^bsub>x\<^esub>"
  by (pred_auto)
    
declare sublens_def [lens_defs]
*)

subsection \<open> Modification laws \<close>

(*
lemma "vwb_lens x \<Longrightarrow> (rrestr x P) nmods $x"
  by (pred_auto)
     (metis scene_override_idem scene_override_overshadow_right)
*)

subsection \<open> Frames as lenses \<close>

text \<open> For now, frames are most useful when the scene is a wrapped up lens. Therefore, for the proof
  automation we assume this form in the following lemmas. \<close>

lemma frame_var_alpha [pred]: "vwb_lens x \<Longrightarrow> frame (var_alpha x) P = (\<lambda>(s, s'). s' = s \<oplus>\<^sub>L s' on x \<and> P (s, s'))"
  by (pred_simp, metis lens_override_def lens_scene_override scene_override_commute vwb_lens.put_eq vwb_lens_mwb)

lemma frame_neg_var_alpha [pred]: "mwb_lens x \<Longrightarrow> frame (- (var_alpha x)) P = (\<lambda>(s, s'). s = s \<oplus>\<^sub>L s' on x \<and> P (s, s'))"
  by (pred_simp, metis)

declare frame_def [pred del]

end