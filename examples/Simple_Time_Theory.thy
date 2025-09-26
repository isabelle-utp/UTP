section \<open> A Simple Time UTP Theory \<close>

theory Simple_Time_Theory
  imports "UTP2.utp"
begin

text \<open> We first create our alphabet, which has components for the time and state. \<close>

alphabet 's time_alpha =
  time  :: "nat"
  state :: "'s"

text \<open> A timed relation is a homogeneous relation over this alphabet type. \<close>

type_synonym 's time_rel = "'s time_alpha hrel"

text \<open> We define an operator for introducing a delay of $n$ time unit, by incrementing time and
  leaving the state unchanged. \<close>

definition Delay :: "nat \<Rightarrow> 's time_alpha hrel" where
[pred]: "Delay(n) = (time\<^sup>> = time\<^sup>< + \<guillemotleft>n\<guillemotright> \<and> state\<^sup>> = state\<^sup><)\<^sub>e"

text \<open> We also define an assignment operator that applies an assignment substitution function
  to the state, and leaves time unchanged. \<close>

definition assigns_trel :: "'s subst \<Rightarrow> 's time_rel" where
[pred]: "assigns_trel \<sigma> = (state\<^sup>> = \<guillemotleft>\<sigma>\<guillemotright>(state\<^sup><) \<and> time\<^sup>> = time\<^sup><)\<^sub>e"

text \<open> We also define a healthiness condition that ensure that time monotonically increases. \<close>

definition HT :: "'s time_alpha hrel \<Rightarrow> 's time_alpha hrel" where
[pred]: "HT(P) = (P \<and> (time\<^sup>< \<le> time\<^sup>>)\<^sub>e)"

text \<open> We can then prove that @{const Delay} is a healthy operator, since it increments time. This
  is done as an Isar proof, but it could be fully automated by Isabelle. \<close>

lemma Delay_HT [closure]: "Delay(n) is HT"
proof (rule Healthy_intro)
  have "HT (Delay n) = ((time\<^sup>> = time\<^sup>< + \<guillemotleft>n\<guillemotright> \<and> state\<^sup>> = state\<^sup><)\<^sub>e \<and> (time\<^sup>< \<le> time\<^sup>>)\<^sub>e)"
    by (simp add: HT_def Delay_def)
  also have "... = (time\<^sup>> = time\<^sup>< + \<guillemotleft>n\<guillemotright> \<and> state\<^sup>> = state\<^sup><)\<^sub>e"
    by pred_auto
  finally show "HT (Delay n) = Delay n"
    by (simp add: Delay_def)
qed

text \<open> Similarly, assignment is healthy, using the proof method @{method pred_auto}. \<close>

lemma assigns_HT: "assigns_trel \<sigma> is HT"
  by (pred_auto)

text \<open> If we wish, we can give an Isar proof that @{const HT} is idempotent, as shown below: \<close>

lemma HT_idem: "Idempotent HT"
proof (rule IdempotentI)
  fix P :: "'a time_rel"
  have "HT(HT(P)) = ((P \<and> (time\<^sup>< \<le> time\<^sup>>)\<^sub>e) \<and> (time\<^sup>< \<le> time\<^sup>>)\<^sub>e)"
    by (simp add: HT_def)
  also have "... =  (P \<and> (time\<^sup>< \<le> time\<^sup>> \<and> time\<^sup>< \<le> time\<^sup>>)\<^sub>e)"
    by (simp)
  also have "... =  (P \<and> (time\<^sup>< \<le> time\<^sup>>)\<^sub>e)"
    by (simp only: conj_absorb)
  also have "... = HT(P)"
    by (simp add: HT_def)
  finally show "HT(HT(P)) = HT(P)" .
qed

text \<open> However, in reality this is a fairly trivial proof that Isabelle can automate: \<close>

lemma HT_idem': "Idempotent HT"
  by (simp add: Idempotent_def HT_def)

lemma HT_mono: "Monotonic HT"
proof (rule MonotonicI)
  fix P Q :: "'a time_rel"
  assume "P \<sqsubseteq> Q"
  thus "HT(P) \<sqsubseteq> HT(Q)"
    by pred_simp
qed

text \<open> We can prove that @{const HT} is closed under sequential composition. \<close>

lemma HT_seq:
  assumes "P is HT" "Q is HT"
  shows "P ;; Q is HT"
  using assms
  by (pred_simp, meson le_trans)

lemma Delay_Delay: "Delay(m) ;; Delay(n) = Delay(m + n)"
  by (pred_auto)

end