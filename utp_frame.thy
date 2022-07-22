theory utp_frame
  imports utp_rel
begin

text \<open> The frame operator restricts the relation P to only operate on variables in the frame a \<close>

definition frame :: "'s frame \<Rightarrow> ('s ::scene_space) rel \<Rightarrow> 's rel" where
"frame a P = {(s, s'). s \<approx>\<^sub>F s' on - a \<and> (s, s') \<in> P}"
(*
text \<open> The frame extension operator take a lens @{term a}, and a relation @{term P}. It constructs
  a relation such that all variables outside of @{term a} are unchanged, and the valuations for
  @{term a} are drawn from @{term P}. Intuitively, this can be seen as extending the alphabet
  of @{term P}. \<close>

definition frame_ext :: "('s\<^sub>1 \<Longrightarrow> ('s\<^sub>2 :: scene_space)) \<Rightarrow> 's\<^sub>1 rel \<Rightarrow> 's\<^sub>2 rel" where
  "frame_ext a P = frame \<lbrace>a\<rbrace>\<^sub>F (P \<up> (a \<times> a))"

syntax 
  "_frame" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]")
  "_frame_ext" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sub>\<up>")

translations
  "_frame a P" == "CONST frame a P"
  "_frame_ext a P" == "CONST frame_ext a P"

abbreviation modifies ("_ mods _") where
"modifies P a \<equiv> P is frame a"

abbreviation not_modifies ("_ nmods _") where
"not_modifies P a \<equiv> P is frame (-a)"

text \<open> Variable restriction - assign arbitrary values to a scene, effectively forbidding the 
  relation from using its value\<close>

definition rrestr :: "('s :: scene_space) frame \<Rightarrow> 's rel \<Rightarrow> 's rel" where
[rel]: "rrestr x P = (\<Union>t t'. frame (-x) ((\<lambda>(s,s'). (t \<oplus>\<^sub>S s on \<lbrakk>x\<rbrakk>\<^sub>F, t' \<oplus>\<^sub>S s' on \<lbrakk>x\<rbrakk>\<^sub>F))`P))"

abbreviation not_uses ("_ nuses _") where
"not_uses P a \<equiv> P is rrestr a"

lemma nuses_nmods: "P nuses x \<Longrightarrow> P nmods x"
  unfolding Healthy_def rrestr_def frame_def by (transfer, auto)
    
lemma nuses_assign_commute:
  assumes "vwb_lens x" "P nuses $x"
  shows "(x := v) \<Zcomp> P = P \<Zcomp> (x := v)"
  oops

text \<open> Promotion takes a partial lens @{term a} and a relation @{term P}. It constructs a relation
  that firstly restricts the state to valuations where @{term a} is valid (i.e. defined), and 
  secondly uses the lens to promote @{term P} so that it acts only on the @{term a} region of
  the state space. \<close>

definition promote :: "'c rel \<Rightarrow> ('c \<Longrightarrow> ('s::scene_space)) \<Rightarrow> 's rel" where
[rel]: "promote P a = \<questiondown>\<^bold>D(a)? \<Zcomp> a:[P]\<^sub>\<up>"

syntax "_promote" :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infix "\<Up>" 60)
translations "_promote P a" == "CONST promote P a"

lemma rel_frame [rel]: "\<lbrakk>a:[P]\<rbrakk>\<^sub>P (s, s') = (s \<approx>\<^sub>F s' on -a \<and> \<lbrakk>P\<rbrakk>\<^sub>P (s, s'))"
  by (expr_auto add: frame_def)

lemma rel_frame_ext [rel]: "\<lbrakk>a:[P]\<^sub>\<up>\<rbrakk>\<^sub>P (s, s') = (s \<approx>\<^sub>S s' on (-\<lbrakk>a\<rbrakk>\<^sub>\<sim>) \<and> \<lbrakk>P\<rbrakk>\<^sub>P (get\<^bsub>a\<^esub> s, get\<^bsub>a\<^esub> s'))"
  apply (expr_auto add: frame_ext_def frame_def subst_app_pred_def)
  oops


section \<open> Frame laws \<close>

named_theorems frame

lemma frame_all [frame]: "top:[P] = P"
  by rel_auto

lemma frame_none [frame]: "bot:[P] = (P \<and> II)"
  by rel_auto

lemma frame_commute:
  assumes "($y\<^sup><) \<sharp> P" "($y\<^sup>>) \<sharp> P""($x\<^sup><) \<sharp> Q" "($x\<^sup>>) \<sharp> Q" "x \<bowtie> y" 
  shows "$x:[P] \<Zcomp> $y:[Q] = $y:[Q] \<Zcomp> $x:[P]"
  oops
  (*apply (insert assms)
  apply (rel_auto)
   apply (rename_tac s s' s\<^sub>0)
   apply (subgoal_tac "(s \<oplus>\<^sub>L s' on y) \<oplus>\<^sub>L s\<^sub>0 on x = s\<^sub>0 \<oplus>\<^sub>L s' on y")
    apply (metis lens_indep_get lens_indep_sym lens_override_def)
   apply (simp add: lens_indep.lens_put_comm lens_override_def)
  apply (rename_tac s s' s\<^sub>0)
  apply (subgoal_tac "put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> s (get\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> s\<^sub>0 (get\<^bsub>x\<^esub> s')))) (get\<^bsub>y\<^esub> (put\<^bsub>y\<^esub> s (get\<^bsub>y\<^esub> s\<^sub>0))) 
                      = put\<^bsub>x\<^esub> s\<^sub>0 (get\<^bsub>x\<^esub> s')")
   apply (metis lens_indep_get lens_indep_sym)
  apply (metis lens_indep.lens_put_comm)
  done*)
 
lemma frame_miracle [simp]:
  "x:[false] = false"
  by (rel_auto)

lemma frame_skip [simp]:
  "x:[II] = II"
  by (rel_auto)

lemma frame_assign_in [frame]:
  "\<lbrakk> var_lens a; x \<subseteq>\<^sub>L a \<rbrakk> \<Longrightarrow> (\<lbrace>a\<rbrace>\<^sub>F):[x := v] = x := v"
  apply (rel_auto add: lens_insert_def, transfer, auto)
  by (metis lens_override_def lens_scene_override scene_equiv_def scene_override_commute
       var_lens.axioms(1) vwb_lens.put_eq vwb_lens_def)

lemma frame_conj_true [frame]:
  "\<lbrakk>-{x\<^sup><, x\<^sup>>} \<sharp> P; var_lens x \<rbrakk> \<Longrightarrow> (P \<and> $x:[true]) = $x:[P]"
  by (rel_auto)

(*lemma frame_is_assign [frame]:
  "vwb_lens x \<Longrightarrow> x:[$x\<acute> =\<^sub>u \<lceil>v\<rceil>\<^sub><] = x := v"
  by (rel_auto)
  *)  
lemma frame_seq [frame]:
  assumes "vwb_lens x" "-{x\<^sup>>,x\<^sup><} \<sharp> P" "-{x\<^sup><,x\<^sup>>} \<sharp> Q"
  shows "$x:[P \<Zcomp> Q] = $x:[P] \<Zcomp> $x:[Q]"
  unfolding frame_def apply (rel_auto)
  oops

lemma frame_assign_commute_unrest:
  assumes "vwb_lens x" "x \<bowtie> a" "$a \<sharp> v" "$x\<^sup>< \<sharp> P" "$x\<^sup>> \<sharp> P"
  shows "(x := v) \<Zcomp> $a:[P] = $a:[P] \<Zcomp> (x := v)"
  using assms apply (rel_auto)
  oops

lemma frame_to_antiframe [frame]:
  "\<lbrakk> x \<bowtie>\<^sub>S y; x \<squnion>\<^sub>S y = \<top>\<^sub>S \<rbrakk> \<Longrightarrow> x:[P] = (-y):[P]"
  apply rel_auto
  by (metis scene_indep_compat scene_indep_override scene_override_commute scene_override_id scene_override_union)+

lemma rel_frext_miracle [frame]: 
  "a:[false]\<^sup>+ = false"
  by (metis false_pred_def frame_miracle trancl_empty)
    
lemma rel_frext_skip [frame]: 
  "idem_scene a \<Longrightarrow> a:[II]\<^sup>+ = II"
  by (metis frame_skip rtrancl_empty rtrancl_trancl_absorb)

lemma rel_frext_seq [frame]:
  "idem_scene a \<Longrightarrow> a:[P \<Zcomp> Q]\<^sup>+ = (a:[P]\<^sup>+ \<Zcomp> a:[Q]\<^sup>+)"
  apply (rel_auto)
  oops (* gets nitpicked *)


lemma rel_frext_assigns [frame]:
  "vwb_lens a \<Longrightarrow> a:[\<langle>\<sigma>\<rangle>\<^sub>a]\<^sup>+ = \<langle>\<sigma> \<oplus>\<^sub>s a\<rangle>\<^sub>a"
  by (rel_auto)

lemma rel_frext_rcond [frame]:
  "a:[P \<triangleleft> b \<triangleright>\<^sub>r Q]\<^sup>+ = (a:[P]\<^sup>+ \<triangleleft> b \<oplus>\<^sub>p a \<triangleright>\<^sub>r a:[Q]\<^sup>+)"
  by (rel_auto)

lemma rel_frext_commute: 
  "x \<bowtie> y \<Longrightarrow> x:[P]\<^sup>+ \<Zcomp> y:[Q]\<^sup>+ = y:[Q]\<^sup>+ \<Zcomp> x:[P]\<^sup>+"
  apply (rel_auto)
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
  by (rel_auto)

lemma antiframe_seq [frame]:
  "\<lbrakk> vwb_lens x; $x\<acute> \<sharp> P; $x \<sharp> Q \<rbrakk>  \<Longrightarrow> (x:\<lbrakk>P\<rbrakk> \<Zcomp> x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P \<Zcomp> Q\<rbrakk>"
  apply (rel_auto)
   apply (metis vwb_lens_wb wb_lens_def weak_lens.put_get)
  apply (metis vwb_lens_wb wb_lens.put_twice wb_lens_def weak_lens.put_get)
  done

lemma antiframe_copy_assign:
  "vwb_lens x \<Longrightarrow> (x := \<guillemotleft>v\<guillemotright> \<Zcomp> x:\<lbrakk>P\<rbrakk> \<Zcomp> x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright> \<Zcomp> x:\<lbrakk>P\<rbrakk>)"
  by rel_auto

  
lemma nameset_skip: "vwb_lens x \<Longrightarrow> (\<^bold>n\<^bold>s x \<bullet> II) = II\<^bsub>x\<^esub>"
  by (rel_auto, meson vwb_lens_wb wb_lens.get_put)
    
lemma nameset_skip_ra: "vwb_lens x \<Longrightarrow> (\<^bold>n\<^bold>s x \<bullet> II\<^bsub>x\<^esub>) = II\<^bsub>x\<^esub>"
  by (rel_auto)
    
declare sublens_def [lens_defs]



subsection \<open> Modification laws \<close>
lemma "(rrestr x P) nmods x"
  oops
*)
end
