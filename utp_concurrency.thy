section \<open> Concurrent Programming \<close>

theory utp_concurrency
  imports utp_rel_laws utp_rel_prog
begin

text \<open> In this theory we describe the UTP scheme for concurrency, \emph{parallel-by-merge},
  which provides a general parallel operator parametrised by a ``merge predicate'' that explains
  how to merge the after states of the composed predicates. It can thus be applied to many languages
  and concurrency schemes, with this theory providing a number of generic laws. The operator is
  explained in more detail in Chapter 7 of the UTP book~\cite{Hoare&98}. \<close>
  
subsection \<open> Variable Renamings \<close>

text \<open> In parallel-by-merge constructions, a merge predicate defines the behaviour following execution of
  of parallel processes, $P \parallel Q$, as a relation that merges the output of $P$ and $Q$. In order 
  to achieve this we need to separate the variable values output from $P$ and $Q$, and in addition the 
  variable values before execution. The following three constructs do these separations. The initial
  state-space before execution is @{typ "'\<alpha>"}, the final state-space after the first parallel process
  is @{typ "'\<beta>\<^sub>0"}, and the final state-space for the second is @{typ "'\<beta>\<^sub>1"}. These three functions
  lift variables on these three state-spaces, respectively.
\<close>

alphabet ('\<alpha>, '\<beta>\<^sub>0, '\<beta>\<^sub>1) mrg =
  mrg_prior :: "'\<alpha>"
  mrg_left  :: "'\<beta>\<^sub>0"
  mrg_right  :: "'\<beta>\<^sub>1"


text \<open> We set up syntax for the three variable classes. \<close> 

syntax
  "_svarprior" :: "svid" ("<")
  "_svarl"     :: "svid" ("0")
  "_svarr"     :: "svid" ("1")

translations
  "_svarprior"   == "CONST mrg_prior"
  "_svarl"       == "CONST mrg_left"
  "_svarr"       == "CONST mrg_right"

subsection \<open> Merge Predicates \<close>

text \<open> A merge predicate is a relation whose input has three parts: the prior variables, the output
  variables of the left predicate, and the output of the right predicate. \<close>
  
type_synonym '\<alpha> merge = "(('\<alpha>, '\<alpha>, '\<alpha>) mrg, '\<alpha>) urel"
  
text \<open> skip is the merge predicate which ignores the output of both parallel predicates \<close>

definition skip\<^sub>m :: "'\<alpha> merge" where
[pred, rel]: "skip\<^sub>m = ($\<^bold>v\<^sup>> = $<:\<^bold>v\<^sup><)\<^sub>e"

text \<open> swap is a predicate that the swaps the left and right indices; it is used to specify
        commutativity of the parallel operator \<close>

definition swap\<^sub>m :: "(('\<alpha>, '\<beta>, '\<beta>) mrg) hrel" where
[pred, rel]: "swap\<^sub>m = (0:\<^bold>v,1:\<^bold>v) := ($1:\<^bold>v,$0:\<^bold>v)"

text \<open> A symmetric merge is one for which swapping the order of the merged concurrent predicates
  has no effect. We represent this by the following healthiness condition that states that
  @{term "swap\<^sub>m"} is a left-unit. \<close>

abbreviation SymMerge :: "'\<alpha> merge \<Rightarrow> '\<alpha> merge" where
"SymMerge(M) \<equiv> (swap\<^sub>m ;; M)"

subsection \<open> Separating Simulations \<close>

text \<open> U0 and U1 are relations modify the variables of the input state-space such that they become 
  indexed with $0$ and $1$, respectively. \<close>

definition U0 :: "('\<beta>\<^sub>0, ('\<alpha>, '\<beta>\<^sub>0, '\<beta>\<^sub>1) mrg) urel" where
[pred, rel]: "U0 = ($0:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e"

definition U1 :: "('\<beta>\<^sub>1, ('\<alpha>, '\<beta>\<^sub>0, '\<beta>\<^sub>1) mrg) urel" where
[pred, rel]: "U1 = ($1:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e"

lemma U0_swap: "(U0 ;; swap\<^sub>m) = U1"
  by (pred_auto)

lemma U1_swap: "(U1 ;; swap\<^sub>m) = U0"
  by (pred_auto)

text \<open> As shown below, separating simulations can also be expressed using the following two 
  alphabet extrusions \<close>

definition U0\<alpha> :: "'a \<times> 'b \<Longrightarrow> 'a \<times> ('c, 'b, 'd) mrg" where [pred, rel]: "U0\<alpha> = (1\<^sub>L \<times>\<^sub>L mrg_left)"

definition U1\<alpha> where [pred, rel]: "U1\<alpha> = (1\<^sub>L \<times>\<^sub>L mrg_right)"

text \<open> We then create the following intuitive syntax for separating simulations. \<close>

abbreviation U0_alpha_lift :: "('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>1, (_, 's\<^sub>2, _) mrg) urel" ("\<lceil>_\<rceil>\<^sub>0") 
  where "\<lceil>P\<rceil>\<^sub>0 \<equiv> (U0\<alpha>\<^sup>\<up>) \<dagger> P"

abbreviation U1_alpha_lift :: "('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>1, (_, _, 's\<^sub>2) mrg) urel" ("\<lceil>_\<rceil>\<^sub>1") 
  where "\<lceil>P\<rceil>\<^sub>1 \<equiv> (U1\<alpha>\<^sup>\<up>) \<dagger> P"
  
text \<open> @{term "\<lceil>P\<rceil>\<^sub>0"} is predicate $P$ where all variables are indexed by $0$, and 
  @{term "\<lceil>P\<rceil>\<^sub>1"} is where all variables are indexed by $1$. We can thus equivalently express separating 
  simulations using alphabet extrusion. \<close>
  
lemma U0_as_alpha: "(P ;; U0) = \<lceil>P\<rceil>\<^sub>0"
  by (pred_auto)

lemma U1_as_alpha: "(P ;; U1) = \<lceil>P\<rceil>\<^sub>1"
  by (pred_auto)

lemma U0\<alpha>_vwb_lens [simp]: "vwb_lens U0\<alpha>"
  by (simp add: U0\<alpha>_def prod_vwb_lens)

lemma U1\<alpha>_vwb_lens [simp]: "vwb_lens U1\<alpha>"
  by (simp add: U1\<alpha>_def prod_vwb_lens)

lemma U0\<alpha>_indep_right_uvar [simp]: "vwb_lens x \<Longrightarrow> U0\<alpha> \<bowtie> (1:x\<^sup>>)\<^sub>v"
  by (simp add: U0\<alpha>_def prod_as_plus lens_indep_right_ext ns_alpha_def)

lemma U1\<alpha>_indep_left_uvar [simp]: "vwb_lens x \<Longrightarrow> U1\<alpha> \<bowtie> (0:x\<^sup>>)\<^sub>v"
  by (simp add: U1\<alpha>_def prod_as_plus lens_indep_right_ext ns_alpha_def)

lemma U0_alpha_lift_subst [usubst]:
  "\<sigma>(0:x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright>) \<dagger> \<lceil>P\<rceil>\<^sub>0 = \<sigma> \<dagger> \<lceil>P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk>\<rceil>\<^sub>0"
  by pred_auto

lemma U1_alpha_lift_subst [usubst]:
  "\<sigma>(1:x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright>) \<dagger> \<lceil>P\<rceil>\<^sub>1 = \<sigma> \<dagger> \<lceil>P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk>\<rceil>\<^sub>1"
  by pred_auto

lemma U0_alpha_out_var [usubst]: "\<lceil>($x\<^sup>>)\<^sub>e\<rceil>\<^sub>0 = ($0:x\<^sup>>)\<^sub>e"
  by (pred_auto)

lemma U1_alpha_out_var [usubst]: "\<lceil>($x\<^sup>>)\<^sub>e\<rceil>\<^sub>1 = ($1:x\<^sup>>)\<^sub>e"
  by (pred_auto)

lemma U0_skip [usubst]: "\<lceil>II\<rceil>\<^sub>0 = ($0:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e"
  by (pred_auto)

lemma U1_skip [usubst]: "\<lceil>II\<rceil>\<^sub>1 = ($1:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e"
  by (pred_auto)

lemma U0_seqr [usubst]: "\<lceil>P ;; Q\<rceil>\<^sub>0 = P ;; \<lceil>Q\<rceil>\<^sub>0"
  by (pred_auto)

lemma U1_seqr [usubst]: "\<lceil>P ;; Q\<rceil>\<^sub>1 = P ;; \<lceil>Q\<rceil>\<^sub>1"
  by (pred_auto)

lemma U0\<alpha>_comp_in_var [usubst]: "(x\<^sup><)\<^sub>v ;\<^sub>L U0\<alpha> = (x\<^sup><)\<^sub>v"
  by (simp add: U0\<alpha>_def prod_as_plus lens_indep_right_ext ns_alpha_def lens_comp_assoc[THEN sym] fst_lens_plus comp_vwb_lens)

lemma U0\<alpha>_comp_out_var [usubst]: "(x\<^sup>>)\<^sub>v ;\<^sub>L U0\<alpha> = (0:x\<^sup>>)\<^sub>v"
  by (simp add: U0\<alpha>_def prod_as_plus lens_indep_right_ext ns_alpha_def lens_comp_assoc[THEN sym] snd_lens_plus)

lemma U1\<alpha>_comp_in_var [usubst]: "(x\<^sup><)\<^sub>v ;\<^sub>L U1\<alpha> = (x\<^sup><)\<^sub>v"
  by (simp add: U1\<alpha>_def prod_as_plus lens_indep_right_ext ns_alpha_def lens_comp_assoc[THEN sym] fst_lens_plus comp_vwb_lens)

lemma U1\<alpha>_comp_out_var [usubst]: "(x\<^sup>>)\<^sub>v ;\<^sub>L U1\<alpha> = (1:x\<^sup>>)\<^sub>v"
  by (simp add: U1\<alpha>_def prod_as_plus lens_indep_right_ext ns_alpha_def lens_comp_assoc[THEN sym] snd_lens_plus)

lemma U0_comp [simp]: "(U0\<alpha>:(x\<^sup>>))\<^sub>v = (0:x\<^sup>>)\<^sub>v"
  by (auto simp add: U0\<alpha>_def lens_defs)

lemma U1_comp [simp]: "(U1\<alpha>:(x\<^sup>>))\<^sub>v = (1:x\<^sup>>)\<^sub>v"
  by (auto simp add: U1\<alpha>_def lens_defs)

lemma varl_sub_merge_left [simp]: "vwb_lens x \<Longrightarrow> (0:x\<^sup>>)\<^sub>v \<subseteq>\<^sub>L U0\<alpha>"
  by (metis U0\<alpha>_comp_out_var comp_vwb_lens lens_comp_lb ns_alpha_def snd_vwb_lens)

lemma varr_sub_merge_right [simp]: "vwb_lens x \<Longrightarrow> (1:x\<^sup>>)\<^sub>v \<subseteq>\<^sub>L U1\<alpha>"
  by (metis U1\<alpha>_comp_out_var comp_vwb_lens ns_alpha_def snd_vwb_lens sublens_def)

subsection \<open> Associative Merges \<close>
  
text \<open> Associativity of a merge means that if we construct a three way merge from a two way merge
  and then rotate the three inputs of the merge to the left, then we get exactly the same three
  way merge back. 

  We first construct the operator that constructs the three way merge by effectively wiring up
  the two way merge in an appropriate way.
\<close>
  
definition ThreeWayMerge :: "'\<alpha> merge \<Rightarrow> (('\<alpha>, '\<alpha>, ('\<alpha>, '\<alpha>, '\<alpha>) mrg) mrg, '\<alpha>) urel" ("\<^bold>M3'(_')") where
[pred, rel]: "ThreeWayMerge M = (($0:\<^bold>v\<^sup>> = $0:\<^bold>v\<^sup>< \<and> $1:\<^bold>v\<^sup>> = $1:0:\<^bold>v\<^sup>< \<and> $<:\<^bold>v\<^sup>> = $<:\<^bold>v\<^sup><)\<^sub>e ;; M ;; U0 \<and> ($1:\<^bold>v\<^sup>> = $1:1:\<^bold>v\<^sup>< \<and> $<:\<^bold>v\<^sup>> = $<:\<^bold>v\<^sup><)\<^sub>e) ;; M"
  
text \<open> The next definition rotates the inputs to a three way merge to the left one place. \<close>

abbreviation rotate\<^sub>m where "rotate\<^sub>m \<equiv> (0:\<^bold>v,1:0:\<^bold>v,1:1:\<^bold>v) := ($1:0:\<^bold>v,$1:1:\<^bold>v,$0:\<^bold>v)"

text \<open> Finally, a merge is associative if rotating the inputs does not effect the output. \<close>
  
definition AssocMerge :: "'\<alpha> merge \<Rightarrow> bool" where
[pred, rel]: "AssocMerge M = (rotate\<^sub>m ;; \<^bold>M3(M) = \<^bold>M3(M))"
    
subsection \<open> Parallel Operators \<close>

text \<open> We implement the following useful operator for separating of two parallel processes and
  copying of the before variables, all to act as input to the merge predicate. \<close>

definition par_sep :: "('a, 'b) urel \<Rightarrow> ('a, 'c) urel \<Rightarrow> ('a, ('a, 'b, 'c) mrg) urel" (infixr "\<parallel>\<^sub>s" 85) where
[pred, rel]: "P \<parallel>\<^sub>s Q \<equiv> (P ;; U0) \<and> (Q ;; U1) \<and> ($<\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e"

text \<open> The following implementation of parallel by merge is less general than the book version, in
  that it does not properly partition the alphabet into two disjoint segments. We could actually
  achieve this specifying lenses into the larger alphabet, but this would complicate the definition
  of programs. \<close>

definition 
  par_by_merge :: "('\<alpha>, '\<beta>) urel \<Rightarrow> (('\<alpha>, '\<beta>, '\<gamma>) mrg, '\<delta>) urel \<Rightarrow> ('\<alpha>, '\<gamma>) urel \<Rightarrow> ('\<alpha>, '\<delta>) urel" 
  ("_ \<parallel>\<^bsub>_\<^esub> _" [85,0,86] 85)
where [pred, rel]: "P \<parallel>\<^bsub>M\<^esub> Q = (P \<parallel>\<^sub>s Q ;; M)"

lemma par_by_merge_alt_def: "P \<parallel>\<^bsub>M\<^esub> Q = (\<lceil>P\<rceil>\<^sub>0 \<and> \<lceil>Q\<rceil>\<^sub>1 \<and> ($<\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; M"
  by (simp add: par_by_merge_def par_sep_def U0_as_alpha U1_as_alpha)

(*
lemma shEx_pbm_left: "((\<exists> x. P x)\<^sub>e \<parallel>\<^bsub>M\<^esub> Q) = (\<^bold>\<exists> x \<bullet> (P x \<parallel>\<^bsub>M\<^esub> Q))"
  by (pred_auto)

lemma shEx_pbm_right: "(P \<parallel>\<^bsub>M\<^esub> (\<^bold>\<exists> x \<bullet> Q x)) = (\<^bold>\<exists> x \<bullet> (P \<parallel>\<^bsub>M\<^esub> Q x))"
  by (pred_auto)
*)

subsection \<open> Unrestriction Laws \<close>

lemma unrest_in_par_by_merge [unrest]:
  "\<lbrakk> vwb_lens x; $x\<^sup>< \<sharp> P; $<:x\<^sup>< \<sharp> M; $x\<^sup>< \<sharp> Q \<rbrakk> \<Longrightarrow> $x\<^sup>< \<sharp> P \<parallel>\<^bsub>M\<^esub> Q"
  by (pred_auto, blast, metis)

lemma unrest_out_par_by_merge [unrest]:
  "\<lbrakk> mwb_lens x; $x\<^sup>> \<sharp> M \<rbrakk> \<Longrightarrow> $x\<^sup>> \<sharp> P \<parallel>\<^bsub>M\<^esub> Q"
  by (simp add: par_by_merge_alt_def unrest)

lemma unrest_merge_vars [unrest]: "$1:x\<^sup>> \<sharp> \<lceil>P\<rceil>\<^sub>0" "$<:x\<^sup>> \<sharp> \<lceil>P\<rceil>\<^sub>0" "$0:x\<^sup>> \<sharp> \<lceil>P\<rceil>\<^sub>1" "$<:x\<^sup>> \<sharp> \<lceil>P\<rceil>\<^sub>1"
  by (pred_simp, simp add: lens_override_def lens_scene.rep_eq scene_override.rep_eq)+ 
  
subsection \<open> Substitution laws \<close>

text \<open> Substitution is a little tricky because when we push the expression through the composition
  operator the alphabet of the expression must also change. Consequently for now we only support
  literal substitution, thoughthis could be generalised with suitable alphabet coercsions. \<close>

lemma U0_seq_subst: "(P ;; U0)\<lbrakk>\<guillemotleft>v\<guillemotright>/0:x\<^sup>>\<rbrakk> = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk> ;; U0)"
  by (pred_auto)

lemma U1_seq_subst: "(P ;; U1)\<lbrakk>\<guillemotleft>v\<guillemotright>/1:x\<^sup>>\<rbrakk> = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk> ;; U1)"
  by (pred_auto)

lemma lit_pbm_subst [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q M \<sigma>. \<sigma>(x\<^sup>< \<leadsto> \<guillemotleft>v\<guillemotright>) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup><\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>\<guillemotleft>v\<guillemotright>/<:x\<^sup><\<rbrakk>\<^esub> (Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup><\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>(x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright>) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<^sup>>\<rbrakk>\<^esub> Q)"
  by (pred_auto)+

subsection \<open> Parallel-by-merge laws \<close>

lemma par_by_merge_false [simp]:
  "P \<parallel>\<^bsub>false\<^esub> Q = false"
  by (pred_auto)

lemma par_by_merge_left_false [simp]:
  "false \<parallel>\<^bsub>M\<^esub> Q = false"
  by (pred_auto)

lemma par_by_merge_right_false [simp]:
  "P \<parallel>\<^bsub>M\<^esub> false = false"
  by (pred_auto)

lemma par_by_merge_seq_add: "(P \<parallel>\<^bsub>M\<^esub> Q) ;; R = (P \<parallel>\<^bsub>M ;; R\<^esub> Q)"
  by (simp add: par_by_merge_def seqr_assoc)

text \<open> A skip parallel-by-merge yields a skip whenever the parallel predicates are both feasible. \<close>

lemma par_by_merge_skip:
  assumes "P ;; true = true" "Q ;; true = true"
  shows "P \<parallel>\<^bsub>skip\<^sub>m\<^esub> Q = II"
  using assms by (pred_auto)

lemma skip_merge_swap: "swap\<^sub>m ;; skip\<^sub>m = skip\<^sub>m"
  by (pred_auto)

lemma par_sep_swap: "P \<parallel>\<^sub>s Q ;; swap\<^sub>m = Q \<parallel>\<^sub>s P"
  by (pred_auto)

end