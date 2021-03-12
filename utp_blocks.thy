section \<open> Variable Blocks \<close>

theory utp_blocks
  imports utp_rel
begin

subsection \<open> Extending and Contracting the Statespace \<close>

definition ext_state :: "(<'s\<^sub>1, 'c> \<Longleftrightarrow> 's\<^sub>2) \<Rightarrow> _" ("ext\<^bsub>_\<^esub>") where
[lens_defs]: "ext\<^bsub>\<X>\<^esub> = (\<lambda> s. put\<^bsub>\<V>\<^bsub>\<X>\<^esub>\<^esub> (create\<^bsub>\<C>\<^bsub>\<X>\<^esub>\<^esub> undefined) s)"

definition con_state :: "(<'s\<^sub>1, 'c> \<Longleftrightarrow> 's\<^sub>2) \<Rightarrow> _" ("con\<^bsub>_\<^esub>") where
[lens_defs]: "con\<^bsub>\<X>\<^esub> = (\<lambda> s. get\<^bsub>\<V>\<^bsub>\<X>\<^esub>\<^esub> s)"

lemma ext_con: "psym_lens \<X> \<Longrightarrow> con\<^bsub>\<X>\<^esub> (ext\<^bsub>\<X>\<^esub> s) = s"
  by (simp add: lens_defs comp_def id_def)

lemma con_surj: "psym_lens \<X> \<Longrightarrow> surj con\<^bsub>\<X>\<^esub>"
  by (meson ext_con surjI)

lemma put_con_in: "\<lbrakk> psym_lens \<X>; x \<subseteq>\<^sub>L \<C>\<^bsub>\<X>\<^esub> \<rbrakk> \<Longrightarrow> con\<^bsub>\<X>\<^esub> (put\<^bsub>x\<^esub> s v) = con\<^bsub>\<X>\<^esub> s"
  by (simp add: con_state_def sublens_pres_indep')

subsection \<open> Lifting Symmetric Lenses \<close>

definition slens_pcomp :: "(<'a, 'b> \<Longleftrightarrow> 's\<^sub>1) \<Rightarrow> ('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> (<'a, 'b> \<Longleftrightarrow> 's\<^sub>2)" where
[lens_defs]: "slens_pcomp S L = \<lparr> view = view S ;\<^sub>L L, coview = coview S ;\<^sub>L L \<rparr>"

text \<open> This rather complex looking operator converts a endogeneous lens on one state space, to one
  on a larger state space. An example of a endogeneous lens is @{term "tl\<^sub>L"}, which views the tail
  of a list. Let's say then we have a state space with a variable denoting a list. Then the 
  following function constructs a lens which allows us to view the state space, where the only
  change is that we are viewing the tail of the lens. \<close>
  
definition lens_lift :: "('s\<^sub>1 \<Longrightarrow> 's\<^sub>1) \<Rightarrow> ('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>2 \<Longrightarrow> 's\<^sub>2)" where
[lens_defs]: "lens_lift X Y = \<lparr> lens_get = (\<lambda> s. put\<^bsub>Y\<^esub> s (get\<^bsub>X\<^esub> (get\<^bsub>Y\<^esub> s)))
                              , lens_put = (\<lambda> s v. put\<^bsub>Y\<^esub> v (put\<^bsub>X\<^esub> (get\<^bsub>Y\<^esub> s) (get\<^bsub>Y\<^esub> v)))  \<rparr>"

lemma lens_lift_mwb [simp]: "\<lbrakk> mwb_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> mwb_lens (lens_lift X Y)"
  by (unfold_locales, simp_all add: lens_defs)

lemma lens_lift_vwb [simp]: "\<lbrakk> vwb_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> vwb_lens (lens_lift X Y)"
  by (unfold_locales, simp_all add: lens_defs)

definition slens_lift :: "(<'s\<^sub>1, 'a> \<Longleftrightarrow> 's\<^sub>1) \<Rightarrow> ('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> (<'s\<^sub>2, 'a> \<Longleftrightarrow> 's\<^sub>2)" (infixl "\<up>\<^sub>S" 80) where
[lens_defs]: "slens_lift S L = \<lparr> view = lens_lift (view S) L, coview = coview S ;\<^sub>L L \<rparr>"

lemma "\<lbrakk> psym_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> psym_lens (X \<up>\<^sub>S Y)"
  apply (simp add: slens_lift_def)
  apply (rule psym_lens.intro)
  apply (simp_all)
  using comp_mwb_lens psym_lens.mwb_coregion vwb_lens_mwb apply blast
  oops

text \<open> The following result is needed to demonstrate the combination of the view and co-view
  covers all of the statespace. \<close>

context psym_lens
begin

lemma put_region_coregion_cover: "put\<^bsub>\<V>\<^esub> (put\<^bsub>\<C>\<^esub> s\<^sub>1 v\<^sub>1) v\<^sub>2 = put\<^bsub>\<V>\<^esub> (put\<^bsub>\<C>\<^esub> s\<^sub>2 v\<^sub>1) v\<^sub>2"
proof -
  have "\<And> \<sigma> \<rho> v\<^sub>1 v\<^sub>2. put\<^bsub>\<V> +\<^sub>L \<C>\<^esub> \<sigma> (v\<^sub>1, v\<^sub>2) = put\<^bsub>\<V> +\<^sub>L \<C>\<^esub> \<rho> (v\<^sub>1, v\<^sub>2)"
    by (simp add: pbij_lens.put_det)
  thus ?thesis
    by (simp add: lens_defs)
qed

end

subsection \<open> Adding and Deleting Variables \<close>

text \<open> The functions implement addition and deletion of variables in the style proposed by
   Back and Preoteasa. A variable is a lens point to a stack-like local variable store. We 
  By lifting a symmetric lens for splitting the statespace we can save and retrieve values
  in the stack. \<close>

abbreviation add_var ("add[_]\<^bsub>_\<^esub>") where "add_var \<X> x \<equiv> ext\<^bsub>\<X> \<up>\<^sub>S x\<^esub>"
abbreviation del_var ("del[_]\<^bsub>_\<^esub>") where "del_var \<X> x \<equiv> con\<^bsub>\<X> \<up>\<^sub>S x\<^esub>"

lemma del_var_def: "del[\<X>]\<^bsub>x\<^esub> = (\<lambda>s. put\<^bsub>x\<^esub> s (get\<^bsub>\<V>\<^bsub>\<X>\<^esub>\<^esub> (get\<^bsub>x\<^esub> s)))"
  by (simp add: con_state_def slens_lift_def lens_lift_def)

lemma add_var_prop:
  "\<lbrakk> psym_lens \<X>; weak_lens x \<rbrakk> \<Longrightarrow> 
    put\<^bsub>\<V>\<^bsub>\<X>\<^esub>\<^esub> (get\<^bsub>x\<^esub> (create\<^bsub>\<C>\<^bsub>\<X>\<^esub> ;\<^sub>L x\<^esub> undefined)) v
    = put\<^bsub>\<C>\<^bsub>\<X>\<^esub>\<^esub> (put\<^bsub>\<V>\<^bsub>\<X>\<^esub>\<^esub> s v) undefined"
  using psym_lens.put_region_coregion_cover psym_lens_compl 
  by (fastforce simp add: lens_defs lens_indep_comm)

lemma add_var_def: 
  "\<lbrakk> psym_lens \<X>; weak_lens x \<rbrakk> \<Longrightarrow> 
    add[\<X>]\<^bsub>x\<^esub> = (\<lambda>s. put\<^bsub>x\<^esub> s (put\<^bsub>\<C>\<^bsub>\<X>\<^esub>\<^esub> (put\<^bsub>\<V>\<^bsub>\<X>\<^esub>\<^esub> undefined (get\<^bsub>x\<^esub> s)) undefined))"
  using add_var_prop by (fastforce simp add: ext_state_def slens_lift_def lens_lift_def)

text \<open> Back and von Wright's axioms \<close>

lemma add_del:
  "\<lbrakk> psym_lens \<X>; vwb_lens x \<rbrakk> \<Longrightarrow> del[\<X>]\<^bsub>x\<^esub> (add[\<X>]\<^bsub>x\<^esub> s) = s"
  by (simp add: add_var_def del_var_def)

lemma del_surj: "\<lbrakk> psym_lens \<X>; vwb_lens x \<rbrakk> \<Longrightarrow> surj del[\<X>]\<^bsub>x\<^esub>"
  by (meson add_del surjI)

lemma del_get: "x \<bowtie> y \<Longrightarrow> get\<^bsub>x\<^esub> (del[\<X>]\<^bsub>y\<^esub> s) = get\<^bsub>x\<^esub> s"
  by (simp add: del_var_def)

lemma put_del_diff: "x \<bowtie> y \<Longrightarrow> del[\<X>]\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> s v) = put\<^bsub>x\<^esub> (del[\<X>]\<^bsub>y\<^esub> s) v"
  by (simp add: del_var_def lens_indep_comm, simp add: lens_indep_sym)

subsection \<open> Variable Stacks \<close>

text \<open> A variable stack is a non-empty list. This means there is always a value at the top, and
  there is always a @{const vwb_lens} for pointing the current value of a local variable. \<close>

typedef 'a vstack = "{xs :: 'a list. xs \<noteq> []}"
  by auto

setup_lifting type_definition_vstack

lift_definition vtop :: "'a vstack \<Rightarrow> 'a" is hd .
lift_definition vpush :: "'a \<Rightarrow> 'a vstack \<Rightarrow> 'a vstack" is "(#)" by simp
lift_definition vmake :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a vstack" is "(#)" by simp
lift_definition vtop_put :: "'a \<Rightarrow> 'a vstack \<Rightarrow> 'a vstack" is "\<lambda> x stk. x # tl stk" by simp
lift_definition vshrink :: "'a vstack \<Rightarrow> 'a vstack" is "\<lambda> xs. if (length xs > 1) then tl xs else [undefined]"
  apply (auto)
  apply (simp add: Nitpick.size_list_simp(2))
  done
lift_definition vappend :: "'a vstack \<Rightarrow> 'a vstack \<Rightarrow> 'a vstack" is "(@)"
  by simp

lemma vtop_put_vtop [simp]: "vtop (vtop_put x s) = x"
  by (transfer, simp_all)

lemma vpush_vtop_put [simp]: "vtop_put y (vpush x s) = vpush y s"
  by (transfer, simp)

lemma vtop_put_vshrink [simp]: "vshrink (vtop_put v s) = vshrink s"
  by (transfer, simp)

lemma vtop_put_vshrink [simp]: "vshrink (vtop_put x s) = s"
  apply (transfer, auto)
  oops

lemma vtop_vpush [simp]: "vtop (vpush x s) = x"
  by (transfer, simp)

lemma vshrink_vpush [simp]: "vshrink (vpush x s) = s"
  by (transfer, simp)

lemma vtop_put_put [simp]: "vtop_put x (vtop_put y s) = vtop_put x s"
  by (transfer, simp)

lemma vtop_vtop_put [simp]: "vtop_put (vtop s) s = s"
  by (transfer, simp)

definition vtop\<^sub>L :: "'a \<Longrightarrow> 'a vstack" where
[lens_defs]: "vtop\<^sub>L = \<lparr> lens_get = vtop, lens_put = (\<lambda> s v. vtop_put v s) \<rparr>"

definition vshrink\<^sub>L :: "'a vstack \<Longrightarrow> 'a vstack" where
[lens_defs]: "vshrink\<^sub>L = \<lparr> lens_get = vshrink, lens_put = (\<lambda> s v. vpush (vtop s) v) \<rparr>"

lemma vtop_vwb [simp]: "vwb_lens vtop\<^sub>L"
  by (unfold_locales, simp_all add: lens_defs)

lemma vshrink_vwb [simp]: "mwb_lens vshrink\<^sub>L"
  by (unfold_locales, simp_all add: lens_defs)

lemma vshrink_vtop_indep [simp]: "vshrink\<^sub>L \<bowtie> vtop\<^sub>L"
  by (unfold_locales, simp_all add: lens_defs)

abbreviation "vstack\<^sub>L \<equiv> \<lparr> view = vshrink\<^sub>L, coview = vtop\<^sub>L \<rparr>"

lemma vstack_psym_lens [simp]: "psym_lens vstack\<^sub>L"
  apply (rule psym_lens.intro)
     apply (simp_all)
  apply (rule pbij_lens.intro)
  using mwb_lens_weak plus_mwb_lens vshrink_vtop_indep vshrink_vwb vtop_vwb vwb_lens_mwb apply blast
  apply (simp add: pbij_lens_axioms_def)
  apply (simp add: lens_defs)
  done

text \<open> This theorem can only be proved when we know how to select the variable last created. \<close>

lemma put_del: "vwb_lens x \<Longrightarrow> del[vstack\<^sub>L]\<^bsub>x\<^esub> (put\<^bsub>vtop\<^sub>L ;\<^sub>L x\<^esub> s v) = del[vstack\<^sub>L]\<^bsub>x\<^esub> s"
  by (simp add: del_var_def lens_defs)

lemma add_vstack: "weak_lens x \<Longrightarrow> add[vstack\<^sub>L]\<^bsub>x\<^esub> = (\<lambda> s. put\<^bsub>x\<^esub> s (vpush undefined (get\<^bsub>x\<^esub> s)))"
  by (simp add: lens_defs)

end