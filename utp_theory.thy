section \<open> UTP Theories \<close>

theory utp_theory
  imports 
    utp_rel_laws
begin

text \<open> Here, we mechanise a representation of UTP theories using locales~\cite{Ballarin06}. We also
  link them to the HOL-Algebra library~\cite{Ballarin17}, which allows us to import properties from 
  complete lattices and Galois connections. \<close>

subsection \<open> Complete lattice of predicates \<close>

definition upred_lattice :: "('\<alpha> pred) gorder" ("\<P>") where
"upred_lattice = \<lparr> carrier = UNIV, eq = (=), le = (\<sqsubseteq>) \<rparr>"

text \<open> @{term "\<P>"} is the complete lattice of alphabetised predicates. All other theories will
  be defined relative to it. \<close>

interpretation upred_lattice: complete_lattice \<P>
proof (unfold_locales, simp_all add: upred_lattice_def)
  fix A :: "'\<alpha> pred set"
  show "\<exists>s. is_lub \<lparr>carrier = UNIV, eq = (=), le = (\<sqsubseteq>)\<rparr> s A"
    apply (rule_tac x="\<Squnion> A" in exI)
    apply (rule least_UpperI)
       apply (auto intro: Inf_greatest ref_lattice.Sup_least simp add: Inf_lower Upper_def ref_lattice.Sup_upper)
    done
  show "\<exists>i. is_glb \<lparr>carrier = UNIV, eq = (=), le = (\<sqsubseteq>)\<rparr> i A"
    apply (rule_tac x="\<Sqinter> A" in exI)
    apply (rule greatest_LowerI)
       apply (auto intro: Sup_least ref_lattice.Inf_greatest simp add: Sup_upper Lower_def ref_lattice.Inf_lower)
    done
qed

lemma upred_weak_complete_lattice [simp]: "weak_complete_lattice \<P>"
  by (simp add: upred_lattice.weak.weak_complete_lattice_axioms)

lemma upred_lattice_eq [simp]:
  "(.=\<^bsub>\<P>\<^esub>) = (=)"
  by (simp add: upred_lattice_def)

lemma upred_lattice_le [simp]:
  "le \<P> P Q = (P \<sqsubseteq> Q)"
  by (simp add: upred_lattice_def)

lemma upred_lattice_carrier [simp]:
  "carrier \<P> = UNIV"
  by (simp add: upred_lattice_def)

lemma Healthy_fixed_points [simp]: "fps \<P> H = \<lbrakk>H\<rbrakk>\<^sub>H"
  by (simp add: fps_def upred_lattice_def Healthy_def)
    
lemma upred_lattice_Idempotent [simp]: "Idem\<^bsub>\<P>\<^esub> H = Idempotent H"
  using upred_lattice.weak_partial_order_axioms by (auto simp add: idempotent_def Idempotent_def)

lemma upred_lattice_Monotonic [simp]: "Mono\<^bsub>\<P>\<^esub> H = Monotonic H"
  using upred_lattice.weak_partial_order_axioms 
  by (auto simp add: isotone_def mono_def ref_by_pred_is_leq)
    
subsection \<open> UTP theories hierarchy \<close>

definition utp_order :: "('\<alpha> \<times> '\<alpha>) health \<Rightarrow> '\<alpha> hrel gorder" where
"utp_order H = \<lparr> carrier = {P. P is H}, eq = (=), le = (\<sqsubseteq>) \<rparr>"

text \<open> Constant @{term utp_order} obtains the order structure associated with a UTP theory.
  Its carrier is the set of healthy predicates, equality is HOL equality, and the order is
  refinement. \<close>

lemma utp_order_carrier [simp]:
  "carrier (utp_order H) = \<lbrakk>H\<rbrakk>\<^sub>H"
  by (simp add: utp_order_def)

lemma utp_order_eq [simp]:
  "eq (utp_order T) = (=)"
  by (simp add: utp_order_def)

lemma utp_order_le [simp]:
  "le (utp_order T) = (\<sqsubseteq>)"
  by (simp add: utp_order_def)

lemma utp_partial_order: "partial_order (utp_order T)"
  by (unfold_locales, simp_all add: utp_order_def)

lemma utp_weak_partial_order: "weak_partial_order (utp_order T)"
  by (unfold_locales, simp_all add: utp_order_def)

lemma mono_Monotone_utp_order:
  "mono f \<Longrightarrow> Monotone (utp_order T) f"
  apply (auto simp add: isotone_def ref_by_pred_is_leq)
   apply (metis partial_order_def utp_partial_order)
  apply (metis monotoneD rev_predicate1D)
  done

lemma isotone_utp_orderI: "Monotonic H \<Longrightarrow> isotone (utp_order X) (utp_order Y) H"
  by (auto simp add: mono_def isotone_def ref_by_pred_is_leq utp_weak_partial_order)

lemma Mono_utp_orderI:
  "\<lbrakk> \<And> P Q. \<lbrakk> P \<sqsubseteq> Q; P is H; Q is H \<rbrakk> \<Longrightarrow> F(P) \<sqsubseteq> F(Q) \<rbrakk> \<Longrightarrow> Mono\<^bsub>utp_order H\<^esub> F"
  by (auto simp add: isotone_def utp_weak_partial_order)

text \<open> The UTP order can equivalently be characterised as the fixed point lattice, @{const fpl}. \<close>

lemma utp_order_fpl: "utp_order H = fpl \<P> H"
  by (auto simp add: utp_order_def upred_lattice_def fps_def Healthy_def)

subsection \<open> UTP theory hierarchy \<close>

text \<open> We next define a hierarchy of locales that characterise different classes of UTP theory.
  Minimally we require that a UTP theory's healthiness condition is idempotent. \<close>

locale utp_theory =
  fixes hcond :: "'\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("\<H>")
  assumes HCond_Idempotent [closure,intro]: "Idempotent \<H>"
begin

  abbreviation thy_order :: "'\<alpha> hrel gorder" where
  "thy_order \<equiv> utp_order \<H>"

  lemma HCond_Idem: "\<H>(\<H>(P)) = \<H>(P)"
    using HCond_Idempotent Idempotent_def by blast

  sublocale utp_po: partial_order "utp_order \<H>"
    by (unfold_locales, simp_all add: utp_order_def)

  text \<open> We need to remove some transitivity rules to stop them being applied in calculations \<close>

  declare utp_po.trans [trans del]

end

locale utp_theory_lattice = utp_theory + 
  assumes uthy_lattice: "complete_lattice (utp_order \<H>)"
begin

sublocale complete_lattice "utp_order \<H>"
  by (simp add: uthy_lattice)

declare top_closed [simp del]
declare bottom_closed [simp del]

text \<open> The healthiness conditions of a UTP theory lattice form a complete lattice, and allows us to make
  use of complete lattice results from HOL-Algebra~\cite{Ballarin17}, such as the Knaster-Tarski theorem. We can also
  retrieve lattice operators as below. \<close>

abbreviation utp_top ("\<^bold>\<top>")
where "utp_top \<equiv> top (utp_order \<H>)"

abbreviation utp_bottom ("\<^bold>\<bottom>")
where "utp_bottom \<equiv> bottom (utp_order \<H>)"

abbreviation utp_join (infixl "\<^bold>\<squnion>" 65) where
"utp_join \<equiv> join (utp_order \<H>)"

abbreviation utp_meet (infixl "\<^bold>\<sqinter>" 70) where
"utp_meet \<equiv> meet (utp_order \<H>)"

abbreviation utp_sup ("\<^bold>\<Squnion>_" [90] 90) where
"utp_sup \<equiv> Lattice.sup (utp_order \<H>)"

abbreviation utp_inf ("\<^bold>\<Sqinter>_" [90] 90) where
"utp_inf \<equiv> Lattice.inf (utp_order \<H>)"

abbreviation utp_gfp ("\<^bold>\<nu>") where
"utp_gfp \<equiv> GREATEST_FP (utp_order \<H>)"

abbreviation utp_lfp ("\<^bold>\<mu>") where
"utp_lfp \<equiv> LEAST_FP (utp_order \<H>)"

end

syntax
  "_tmu" :: "logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>\<mu>\<index> _ \<bullet> _" [0, 10] 10)
  "_tnu" :: "logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>\<nu>\<index> _ \<bullet> _" [0, 10] 10)

notation gfp ("\<mu>")
notation lfp ("\<nu>")

translations
  "\<^bold>\<mu>\<^bsub>H\<^esub> X \<bullet> P" == "CONST LEAST_FP (CONST utp_order H) (\<lambda> X. P)"  
  "\<^bold>\<nu>\<^bsub>H\<^esub> X \<bullet> P" == "CONST GREATEST_FP (CONST utp_order H) (\<lambda> X. P)"

thm Sup_least Sup_upper UNIV_I antisym_conv subsetI upred_lattice.weak.inf_greatest upred_lattice.weak.inf_lower upred_lattice_carrier upred_lattice_le
                                                                                                                                                

lemma upred_lattice_inf:
  "Lattice.inf \<P> A = \<Sqinter> A"
  apply (rule antisym)
  apply (metis (mono_tags, opaque_lifting) UNIV_I gorder.simps(1) pred_refine_iff predicate1I ref_lattice.Inf_lower top.extremum upred_lattice.inf_greatest upred_lattice_carrier upred_lattice_def)
  apply (metis greatest_Lower_below ref_by_pred_is_leq ref_lattice.le_Inf_iff top.extremum upred_lattice.weak_complete_lattice_axioms upred_lattice_carrier upred_lattice_le weak_complete_lattice.inf_glb)
  done

text \<open> We can then derive a number of properties about these operators, as below. \<close>

context utp_theory_lattice
begin

  lemma LFP_healthy_comp: "\<^bold>\<mu> F = \<^bold>\<mu> (F \<circ> \<H>)"
  proof -
    have "{P. (P is \<H>) \<and> F P \<sqsubseteq> P} = {P. (P is \<H>) \<and> F (\<H> P) \<sqsubseteq> P}"
      by (auto simp add: Healthy_def)
    thus ?thesis
      by (simp add: LEAST_FP_def)
  qed

  lemma GFP_healthy_comp: "\<^bold>\<nu> F = \<^bold>\<nu> (F \<circ> \<H>)"
  proof -
    have "{P. (P is \<H>) \<and> P \<sqsubseteq> F P} = {P. (P is \<H>) \<and> P \<sqsubseteq> F (\<H> P)}"
      by (auto simp add: Healthy_def)
    thus ?thesis
      by (simp add: GREATEST_FP_def)
  qed

  lemma top_healthy [closure]: "\<^bold>\<top> is \<H>"
    using weak.top_closed by auto

  lemma bottom_healthy [closure]: "\<^bold>\<bottom> is \<H>"
    using weak.bottom_closed by auto

  lemma utp_top: "P is \<H> \<Longrightarrow> P \<sqsubseteq> \<^bold>\<top>"
    using weak.top_higher by auto

  lemma utp_bottom: "P is \<H> \<Longrightarrow> \<^bold>\<bottom> \<sqsubseteq> P"
    using weak.bottom_lower by auto

end

lemma upred_top: "\<top>\<^bsub>\<P>\<^esub> = false"
  by fastforce

lemma upred_bottom: "\<bottom>\<^bsub>\<P>\<^esub> = true"
  by fastforce

text \<open> One way of obtaining a complete lattice is showing that the healthiness conditions
  are monotone, which the below locale characterises. \<close>

locale utp_theory_mono = utp_theory +
  assumes HCond_Mono [closure,intro]: "Monotonic \<H>"

sublocale utp_theory_mono \<subseteq> utp_theory_lattice
proof -
  interpret weak_complete_lattice "fpl \<P> \<H>"
    by (rule Knaster_Tarski, auto)

  have "complete_lattice (fpl \<P> \<H>)"
    by (unfold_locales, simp add: fps_def sup_exists, (blast intro: sup_exists inf_exists)+)

  hence "complete_lattice (utp_order \<H>)"
    by (simp add: utp_order_def, simp add: upred_lattice_def)

  thus "utp_theory_lattice \<H>"
    by (simp add: utp_theory_axioms utp_theory_lattice.intro utp_theory_lattice_axioms.intro)
qed

text \<open> In a monotone theory, the top and bottom can always be obtained by applying the healthiness
  condition to the predicate top and bottom, respectively. \<close>

context utp_theory_mono
begin

lemma healthy_top: "\<^bold>\<top> = \<H>(false)"
proof -
  have "\<^bold>\<top> = \<top>\<^bsub>fpl \<P> \<H>\<^esub>"
    by (simp add: utp_order_fpl)
  also have "... = \<H> \<top>\<^bsub>\<P>\<^esub>"
    using Knaster_Tarski_idem_extremes(1)[of \<P> \<H>]
    by (simp add: HCond_Idempotent HCond_Mono)
  also have "... = \<H> false"
    by (simp add: upred_top)
  finally show ?thesis .
qed

lemma healthy_bottom: "\<^bold>\<bottom> = \<H>(true)"
proof -
  have "\<^bold>\<bottom> = \<bottom>\<^bsub>fpl \<P> \<H>\<^esub>"
    by (simp add: utp_order_fpl)
  also have "... = \<H> \<bottom>\<^bsub>\<P>\<^esub>"
    using Knaster_Tarski_idem_extremes(2)[of \<P> \<H>]
    by (simp add: HCond_Idempotent HCond_Mono)
  also have "... = \<H> true"
    by (simp add: upred_bottom)
   finally show ?thesis .
qed

lemma healthy_inf:
  assumes "A \<subseteq> \<lbrakk>\<H>\<rbrakk>\<^sub>H"
  shows "\<^bold>\<Sqinter> A = \<H> (\<Sqinter> A)"
  using Knaster_Tarski_idem_inf_eq[OF upred_weak_complete_lattice, of "\<H>"]
  by (simp, metis HCond_Idempotent HCond_Mono assms partial_object.simps(3) upred_lattice_def upred_lattice_inf utp_order_def)

end

locale utp_theory_continuous = utp_theory +
  assumes HCond_Cont [closure,intro]: "Continuous \<H>"

sublocale utp_theory_continuous \<subseteq> utp_theory_mono
proof
  show "Monotonic \<H>"
    by (simp add: Continuous_Monotonic HCond_Cont)
qed

context utp_theory_continuous
begin

  lemma healthy_inf_cont:
    assumes "A \<subseteq> \<lbrakk>\<H>\<rbrakk>\<^sub>H" "A \<noteq> {}"
    shows "\<^bold>\<Sqinter> A = \<Sqinter> A"
  proof -
    have "\<^bold>\<Sqinter> A = \<Sqinter> (\<H>`A)"
      using Continuous_def HCond_Cont assms(1) assms(2) healthy_inf by auto
    also have "... = \<Sqinter> A"
      by (unfold Healthy_carrier_image[OF assms(1)], simp)
    finally show ?thesis .
  qed

  lemma healthy_inf_def:
    assumes "A \<subseteq> \<lbrakk>\<H>\<rbrakk>\<^sub>H"
    shows "\<^bold>\<Sqinter> A = (if (A = {}) then \<^bold>\<top> else (\<Sqinter> A))"
    using assms healthy_inf_cont weak.weak_inf_empty by auto

  lemma healthy_meet_cont:
    assumes "P is \<H>" "Q is \<H>"
    shows "P \<^bold>\<sqinter> Q = P \<sqinter> Q"
    using healthy_inf_cont[of "{P, Q}"] assms
    by (simp add: Healthy_if meet_def)

  lemma meet_is_healthy [closure]:
    assumes "P is \<H>" "Q is \<H>"
    shows "P \<sqinter> Q is \<H>"
    using Continuous_Disjunctous[OF HCond_Cont] assms
    by (simp add: Disjunctuous_def Healthy_def' disj_pred_def)

  lemma meet_bottom [simp]:
    assumes "P is \<H>"
    shows "P \<sqinter> \<^bold>\<bottom> = \<^bold>\<bottom>"
    using assms ref_lattice.inf.absorb_iff2 utp_bottom by blast

  lemma meet_top [simp]:
    assumes "P is \<H>"
    shows "P \<sqinter> \<^bold>\<top> = P"
    using assms utp_top by auto

  text \<open> The UTP theory lfp operator can be rewritten to the alphabetised predicate lfp when
    in a continuous context. \<close>

  theorem utp_lfp_def:
    assumes "Monotonic F" "F \<in> \<lbrakk>\<H>\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<H>\<rbrakk>\<^sub>H"
    shows "\<^bold>\<mu> F = (\<mu> X \<bullet> F(\<H>(X)))"
  proof (rule ref_antisym)
    have ne: "{P. (P is \<H>) \<and> F P \<sqsubseteq> P} \<noteq> {}"
    proof -
      have "F \<^bold>\<top> \<sqsubseteq> \<^bold>\<top>"
        using assms(2) utp_top weak.top_closed by force
      thus ?thesis
        by (auto, rule_tac x="\<^bold>\<top>" in exI, auto simp add: top_healthy)
    qed
    show "\<^bold>\<mu> F \<sqsubseteq> (\<mu> X \<bullet> F (\<H> X))"
    proof -
      have "\<Sqinter>{P. (P is \<H>) \<and> F(P) \<sqsubseteq> P} \<sqsubseteq> \<Sqinter>{P. F(\<H>(P)) \<sqsubseteq> P}"
      proof -
        have 1: "\<And> P. F(\<H>(P)) = \<H>(F(\<H>(P)))"
          by (metis HCond_Idem Healthy_def assms(2) funcset_mem mem_Collect_eq)
        show ?thesis
        proof (rule ref_lattice.Inf_greatest, auto)
          fix P
          assume a: "F (\<H> P) \<sqsubseteq> P"
          hence F: "(F (\<H> P)) \<sqsubseteq> (\<H> P)"
            by (metis "1" HCond_Mono Monotonic_refine)
          show "\<Sqinter>{P. (P is \<H>) \<and> F P \<sqsubseteq> P} \<sqsubseteq> P"
          proof (rule ref_lattice.Inf_lower2[of "F (\<H> P)"])
            show "F (\<H> P) \<in> {P. (P is \<H>) \<and> F P \<sqsubseteq> P}"
            proof (auto)
              show "F (\<H> P) is \<H>"
                by (metis 1 Healthy_def)
              show "F (F (\<H> P)) \<sqsubseteq> F (\<H> P)"
                using F Monotonic_refine assms(1) by blast
            qed
            show "F (\<H> P) \<sqsubseteq> P"
              by (simp add: a)
          qed
        qed
      qed

      with ne show ?thesis
        by (simp add: LEAST_FP_def ref_lattice.gfp_def, subst healthy_inf_cont, auto simp add: gfp_is_ref_lfp ref_lattice.lfp_def)
    qed
    from ne show "(\<mu> X \<bullet> F (\<H> X)) \<sqsubseteq> \<^bold>\<mu> F"
      apply (simp add: LEAST_FP_def ref_lattice.gfp_def, subst healthy_inf_cont, auto simp add: gfp_is_ref_lfp)
      apply (rule ref_lattice.Inf_greatest)
      apply (auto simp add: Healthy_def Inf_lower ref_lattice.lfp_lowerbound)
      done
  qed

  lemma UINF_ind_Healthy [closure]:
    assumes "\<And> i. P(i) is \<H>"
    shows "(\<Sqinter> i. P(i)) is \<H>"
    by (simp add: closure assms)

end

text \<open> In another direction, we can also characterise UTP theories that are relational. Minimally
  this requires that the healthiness condition is closed under sequential composition. \<close>

locale utp_theory_rel =
  utp_theory +
  assumes Healthy_Sequence [closure]: "\<lbrakk> P is \<H>; Q is \<H> \<rbrakk> \<Longrightarrow> (P ;; Q) is \<H>"
begin

lemma upower_Suc_Healthy [closure]:
  assumes "P is \<H>"
  shows "P \<^bold>^ Suc n is \<H>"
  by (induct n, simp_all add: closure assms upred_semiring.power_Suc)

end

locale utp_theory_cont_rel = utp_theory_rel + utp_theory_continuous
begin

  lemma seq_cont_Sup_distl:
    assumes "P is \<H>" "A \<subseteq> \<lbrakk>\<H>\<rbrakk>\<^sub>H" "A \<noteq> {}"
    shows "P ;; (\<^bold>\<Sqinter> A) = \<^bold>\<Sqinter> {P ;; Q | Q. Q \<in> A }"
  proof -
    have "{P ;; Q | Q. Q \<in> A } \<subseteq> \<lbrakk>\<H>\<rbrakk>\<^sub>H"
      using Healthy_Sequence assms(1) assms(2) by (auto)
    thus ?thesis
      by (simp add: healthy_inf_cont seq_Sup_distl setcompr_eq_image assms)
  qed

  lemma seq_cont_Sup_distr:
    assumes "Q is \<H>" "A \<subseteq> \<lbrakk>\<H>\<rbrakk>\<^sub>H" "A \<noteq> {}"
    shows "(\<^bold>\<Sqinter> A) ;; Q = \<^bold>\<Sqinter> {P ;; Q | P. P \<in> A }"
  proof -
    have "{P ;; Q | P. P \<in> A } \<subseteq> \<lbrakk>\<H>\<rbrakk>\<^sub>H"
      using Healthy_Sequence assms(1) assms(2) by (auto)
    thus ?thesis
      by (simp add: healthy_inf_cont seq_Sup_distr setcompr_eq_image assms)
  qed

  lemma uplus_healthy [closure]:
    assumes "P is \<H>"  
    shows "P\<^bold>+ is \<H>"
    by (simp add: uplus_power_def closure assms)
  
end

text \<open> There also exist UTP theories with units. Not all theories have both a left and a right unit 
  (e.g. H1-H2 designs) and so we split up the locale into two cases. \<close>

locale utp_theory_units =
  utp_theory_rel +
  fixes utp_unit ("\<I>\<I>")
  assumes Healthy_Unit [closure]: "\<I>\<I> is \<H>"
begin

text \<open> We can characterise the theory Kleene star by lifting the relational one. \<close>

definition utp_star ("_\<^bold>\<star>" [999] 999) where
[pred]: "utp_star P = (P\<^sup>\<star> ;; \<I>\<I>)"

text \<open> We can then characterise tests as refinements of units. \<close>

definition utp_test :: "'a hrel \<Rightarrow> bool" where
[pred]: "utp_test b = (\<I>\<I> \<sqsubseteq> b)"

end

locale utp_theory_left_unital =
  utp_theory_units +
  assumes Unit_Left: "P is \<H> \<Longrightarrow> (\<I>\<I> ;; P) = P"

locale utp_theory_right_unital =
  utp_theory_units +
  assumes Unit_Right: "P is \<H> \<Longrightarrow> (P ;; \<I>\<I>) = P"

locale utp_theory_unital =
  utp_theory_left_unital + utp_theory_right_unital
begin

lemma Unit_self [simp]:
  "\<I>\<I> ;; \<I>\<I> = \<I>\<I>"
  by (simp add: Healthy_Unit Unit_Right)

lemma utest_intro:
  "\<I>\<I> \<sqsubseteq> P \<Longrightarrow> utp_test P"
  by (simp add: utp_test_def)

lemma utest_Unit [closure]:
  "utp_test \<I>\<I>"
  by (simp add: utp_test_def)

end

locale utp_theory_mono_unital = utp_theory_unital + utp_theory_mono
begin

lemma utest_Top [closure]: "utp_test \<^bold>\<top>"
  by (simp add: Healthy_Unit utp_test_def utp_top)

end

locale utp_theory_cont_unital = utp_theory_cont_rel + utp_theory_unital

sublocale utp_theory_cont_unital \<subseteq> utp_theory_mono_unital
  by (simp add: utp_theory_mono_axioms utp_theory_mono_unital_def utp_theory_unital_axioms)

locale utp_theory_unital_zerol =
  utp_theory_unital +
  utp_theory_lattice +
  assumes Top_Left_Zero: "P is \<H> \<Longrightarrow> \<^bold>\<top> ;; P = \<^bold>\<top>"

locale utp_theory_cont_unital_zerol =
  utp_theory_cont_unital + utp_theory_unital_zerol
begin
  
lemma Top_test_Right_Zero:
  assumes "b is \<H>" "utp_test b"
  shows "b ;; \<^bold>\<top> = \<^bold>\<top>"
proof -
  have "b \<sqinter> \<I>\<I> = \<I>\<I>"
    using assms(2) utp_test_def by auto
  then show ?thesis
    by (metis (no_types) Top_Left_Zero Unit_Left assms(1) meet_top top_healthy upred_semiring.distrib_right)
qed

end

subsection \<open> Kleene UTP theories \<close>

locale utp_theory_kleene = utp_theory_cont_unital_zerol
begin                                             

lemma Star_def: "P\<^bold>\<star> = P\<^sup>\<star> ;; \<I>\<I>"
  by (simp add: utp_star_def)
  
lemma Star_alt_def:
  assumes "P is \<H>"
  shows "P\<^bold>\<star> = \<I>\<I> \<sqinter> P\<^bold>+"
proof -
  from assms have "P\<^bold>+ = P\<^sup>\<star> ;; P ;; \<I>\<I>"
    by (simp add: Unit_Right uplus_alt_def)
  then show ?thesis
    by (metis seqr_assoc uplus_alt_def uplus_def upred_semiring.distrib_right upred_semiring.mult.left_neutral ustar_unfoldl utp_star_def)
qed

lemma Star_Healthy [closure]:
  assumes "P is \<H>"
  shows "P\<^bold>\<star> is \<H>"
  by (simp add: assms closure Star_alt_def)

lemma Star_unfoldl:
  "P\<^bold>\<star> \<sqsubseteq> \<I>\<I> \<sqinter> (P ;; P\<^bold>\<star>)"
  by (metis (no_types, lifting) ref_lattice.inf.absorb_iff2 seqr_assoc sup.idem upred_semiring.distrib_right upred_semiring.mult.left_neutral ustar_unfoldl utp_star_def)

lemma Star_inductl:
  assumes "R is \<H>" "Q \<sqsubseteq> (P ;; Q) \<sqinter> R"
  shows "Q \<sqsubseteq> P\<^bold>\<star>;;R"
proof -
  from assms(2) have "Q \<sqsubseteq> R" "Q \<sqsubseteq> P ;; Q"
    by auto
  thus ?thesis
    by (simp add: Unit_Left assms(1) seqr_assoc ustar_inductl utp_star_def)
qed

lemma Star_invol:
  assumes "P is \<H>"
  shows "P\<^bold>\<star>\<^bold>\<star> = P\<^bold>\<star>"
proof -
  have "P\<^bold>\<star>\<^bold>\<star> \<sqsubseteq> P\<^bold>\<star>"
    by (metis Star_Healthy Star_alt_def Star_unfoldl Unit_Right assms ref_lattice.le_infE upred_semiring.distrib_left)
  moreover have "P\<^bold>\<star> \<sqsubseteq> P\<^bold>\<star>\<^bold>\<star>"
    by (metis Star_Healthy Star_inductl Star_unfoldl assms ref_lattice.inf.absorb_iff2 ref_lattice.le_infE ustar_inductl utp_star_def)
  ultimately show ?thesis
    using pred_ba.dual_order.eq_iff by blast
qed

lemma Star_test: 
  assumes "P is \<H>" "utp_test P"
  shows "P\<^bold>\<star> = \<I>\<I>"
  by (metis Star_alt_def assms ref_lattice.inf.absorb1 uplus_alt_def ustar_inductl utp_test_def utp_theory_right_unital.Unit_Right utp_theory_right_unital_axioms)

lemma Star_lemma_1:
  "P is \<H> \<Longrightarrow> \<I>\<I> ;; P\<^sup>\<star> ;; \<I>\<I> = P\<^sup>\<star> ;; \<I>\<I>"
  by (metis utp_star_def Star_Healthy Unit_Left)


lemma Star_lemma_2:
  assumes "P is \<H>" "Q is \<H>"
  shows "(P\<^sup>\<star> ;; Q\<^sup>\<star> ;; \<I>\<I>)\<^sup>\<star> ;; \<I>\<I> = (P\<^sup>\<star> ;; Q\<^sup>\<star>)\<^sup>\<star> ;; \<I>\<I>"
  by (metis (no_types, lifting) Star_lemma_1 Unit_self assms seqr_assoc ustar_sim)

lemma Star_denest:
  assumes "P is \<H>" "Q is \<H>"
  shows "(P \<sqinter> Q)\<^bold>\<star> = (P\<^bold>\<star> ;; Q\<^bold>\<star>)\<^bold>\<star>"
  by (metis (no_types, lifting) seqr_assoc utp_star_def Star_lemma_1 Star_lemma_2 assms ustar_denest)  

lemma Star_denest_disj: 
  assumes "P is \<H>" "Q is \<H>"
  shows "(P \<or> Q)\<^bold>\<star> = (P\<^bold>\<star> ;; Q\<^bold>\<star>)\<^bold>\<star>"
  by (simp add: Star_denest assms disj_pred_def)


lemma Star_unfoldl_eq: 
  assumes "P is \<H>"
  shows "\<I>\<I> \<sqinter> (P ;; P\<^bold>\<star>) = P\<^bold>\<star>"
  by (metis (no_types, lifting) seqr_assoc upred_semiring.distrib_right upred_semiring.mult.left_neutral ustar_unfoldl utp_star_def)


lemma uplus_Star_def:
  assumes "P is \<H>"
  shows "P\<^bold>+ = (P ;; P\<^bold>\<star>)"
  by (metis Star_alt_def Unit_Right assms seqr_right_unit uplus_def upred_semiring.distrib_left ustar_unfoldl)

lemma Star_trade_skip:
  "P is \<H> \<Longrightarrow> \<I>\<I> ;; P\<^sup>\<star> = P\<^sup>\<star> ;; \<I>\<I>"
  by (simp add: Unit_Left Unit_Right ustar_sim)

lemma Star_slide:
  assumes "P is \<H>"
  shows "(P ;; P\<^bold>\<star>) = (P\<^bold>\<star> ;; P)" (is "?lhs = ?rhs")
proof -
  have "?lhs = P ;; P\<^sup>\<star> ;; \<I>\<I>"
    by (simp add: utp_star_def)
  also have "... = P ;; \<I>\<I> ;; P\<^sup>\<star>"
    by (simp add: Star_trade_skip assms)
  also have "... = P ;; P\<^sup>\<star>"
    by (metis Unit_Right assms seqr_assoc)
  also have "... = P\<^sup>\<star> ;; P"
    by (simp add: ustar_sim)
  also have "... = ?rhs"
    by (simp add: Unit_Left assms seqr_assoc utp_star_def)
  finally show ?thesis .
qed

lemma Star_unfoldr_eq:
  assumes "P is \<H>"
  shows "\<I>\<I> \<sqinter> (P\<^bold>\<star> ;; P) = P\<^bold>\<star>"
  using Star_slide Star_unfoldl_eq assms by auto

lemma Star_inductr:
  assumes "P is \<H>" "R is \<H>" "Q \<sqsubseteq> P \<sqinter> (Q ;; R)"
  shows "Q \<sqsubseteq> P;;R\<^bold>\<star>"
  by (metis Star_trade_skip Unit_Right assms ref_lattice.le_inf_iff seqr_assoc ustar_inductr utp_star_def)

lemma Star_Top: "\<^bold>\<top>\<^bold>\<star> = \<I>\<I>"
  by (simp add: Star_test top_healthy utest_Top)

end

subsection \<open> Theory of relations \<close>

interpretation rel_theory: utp_theory_mono_unital id skip
  rewrites "rel_theory.utp_top = false"
  and "rel_theory.utp_bottom = true"
  and "carrier (utp_order id) = UNIV"
  and "(P is id) = True"
proof -
  show "utp_theory_mono_unital id II"
    by (unfold_locales, simp_all add: Healthy_def)
  then interpret utp_theory_mono_unital id skip
    by simp
  show "utp_top = false" "utp_bottom = true"
    by (simp_all add: healthy_top healthy_bottom)
  show "carrier (utp_order id) = UNIV" "(P is id) = True"
    by (auto simp add: utp_order_def Healthy_def)
qed

thm rel_theory.GFP_unfold

subsection \<open> Theory links \<close>

text \<open> We can also describe links between theories, such a Galois connections and retractions,
  using the following notation. \<close>

definition mk_conn ("_ \<Leftarrow>\<langle>_,_\<rangle>\<Rightarrow> _" [90,0,0,91] 91) where
"H1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H2 \<equiv> \<lparr> orderA = utp_order H1, orderB = utp_order H2, lower = \<H>\<^sub>2, upper = \<H>\<^sub>1 \<rparr>"

lemma mk_conn_orderA [simp]: "\<X>\<^bsub>H1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H2\<^esub> = utp_order H1"
  by (simp add:mk_conn_def)

lemma mk_conn_orderB [simp]: "\<Y>\<^bsub>H1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H2\<^esub> = utp_order H2"
  by (simp add:mk_conn_def)

lemma mk_conn_lower [simp]:  "\<pi>\<^sub>*\<^bsub>H1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H2\<^esub> = \<H>\<^sub>1"
  by (simp add: mk_conn_def)

lemma mk_conn_upper [simp]:  "\<pi>\<^sup>*\<^bsub>H1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H2\<^esub> = \<H>\<^sub>2"
  by (simp add: mk_conn_def)

lemma galois_comp: "(H\<^sub>2 \<Leftarrow>\<langle>\<H>\<^sub>3,\<H>\<^sub>4\<rangle>\<Rightarrow> H\<^sub>3) \<circ>\<^sub>g (H\<^sub>1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H\<^sub>2) = H\<^sub>1 \<Leftarrow>\<langle>\<H>\<^sub>1\<circ>\<H>\<^sub>3,\<H>\<^sub>4\<circ>\<H>\<^sub>2\<rangle>\<Rightarrow> H\<^sub>3"
  by (simp add: comp_galcon_def mk_conn_def)

text \<open> Example Galois connection / retract: Existential quantification \<close>

lemma Idempotent_ex: "mwb_lens x \<Longrightarrow> Idempotent (ex_expr x)"
  by (simp add: Idempotent_def)

lemma Monotonic_ex: "mwb_lens x \<Longrightarrow> Monotonic (ex_expr x)"
  by (auto simp add: mono_def expr_defs)

lemma ex_closed_unrest:
  "vwb_lens x \<Longrightarrow> \<lbrakk>ex_expr x\<rbrakk>\<^sub>H = {P. $x \<sharp> P}"
  by (simp add: Healthy_def ex_is_liberation unrest_liberate_iff)

text \<open> Any theory can be composed with an existential quantification to produce a Galois connection \<close>

theorem ex_retract:
  assumes "vwb_lens x" "Idempotent H" "ex_expr x \<circ> H = H \<circ> ex_expr x"
  shows "retract ((ex_expr x \<circ> H) \<Leftarrow>\<langle>ex_expr x, H\<rangle>\<Rightarrow> H)"
proof (unfold_locales, simp_all)
  show "H \<in> \<lbrakk>ex_expr x \<circ> H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>H\<rbrakk>\<^sub>H"
    using Healthy_Idempotent assms by blast
  from assms(1) assms(3)[THEN sym] show "ex_expr x \<in> \<lbrakk>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>ex_expr x \<circ> H\<rbrakk>\<^sub>H"
    by (simp add: Pi_iff Healthy_def)
       (metis comp_eq_dest ex_twice vwb_lens_mwb)
  fix P Q
  assume "P is (ex_expr x \<circ> H)" "Q is H"
  thus "(H P \<sqsubseteq> Q) = (P \<sqsubseteq> (\<exists> x \<Zspot> Q))"
    apply (pred_auto; expr_simp add: comp_def)
     apply (metis surj_pair)
    apply (metis (no_types, opaque_lifting) Healthy_Idempotent Healthy_def Idempotent_ex \<open>P is ex_expr x \<circ> H\<close> assms(1) assms(3) comp_apply vwb_lens.axioms(1) vwb_lens_mwb wb_lens.get_put)
    done
next
  fix P
  assume "P is (ex_expr x \<circ> H)"
  thus "(\<exists> x \<Zspot> H P) \<sqsubseteq> P"
    by (simp add: Healthy_def)
qed

corollary ex_retract_id:
  assumes "vwb_lens x"
  shows "retract (ex_expr x \<Leftarrow>\<langle>ex_expr x, id\<rangle>\<Rightarrow> id)"
  using assms ex_retract[where H="id"] by (auto)

end