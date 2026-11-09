section \<open> Associativity of Parallel by Merge \<close>

theory utp_concurrency_assoc
  imports utp_concurrency
begin

text \<open> We want to have nested parallel, so need associativity of the form:
(P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R).
\<close>

subsection \<open> Associativity Evaluation Iff \<close>

(* AssocMerge M \<longleftrightarrow>
     (\<forall>x p q r z. (\<exists>u. M(x,p,q,u) \<and> M(x,u,r,z)) = (\<exists>u. M(x,q,r,u) \<and> M(x,u,p,z))) *)
lemma AssocMerge_iff:
  "AssocMerge M \<longleftrightarrow>
    (\<forall>x p q r z.
      (\<exists>u. merge_eval M x p q u \<and> merge_eval M x u r z) =
      (\<exists>u. merge_eval M x q r u \<and> merge_eval M x u p z))"
  by (simp add: AssocMerge_def fun_eq_iff; pred_auto; blast)

subsection \<open> Symmetric Associative Merges \<close>

lemma par_by_merge_cyclic:
  assumes "AssocMerge M"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) \<parallel>\<^bsub>M\<^esub> R = (Q \<parallel>\<^bsub>M\<^esub> R) \<parallel>\<^bsub>M\<^esub> P"
  by (rule ext, clarify; simp only: par_by_merge_eval;
      use assms[unfolded AssocMerge_iff] in blast)

lemma par_by_merge_assoc:
  assumes "M is SymMerge" "AssocMerge M"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) \<parallel>\<^bsub>M\<^esub> R = P \<parallel>\<^bsub>M\<^esub> (Q \<parallel>\<^bsub>M\<^esub> R)"
  by (subst par_by_merge_cyclic[OF assms(2)], rule par_by_merge_comm[OF assms(1)])

subsection \<open> Guarded Merges \<close>

text \<open>@{term "merge_guard G M"} restricts @{term M} to branches (i.e. operands) 
satisfying @{term G}. It is used to prove associativity for non-divergent operands.\<close>

(* merge_guard G M (x,p,q,z) = G(x,p) \<and> G(x,q) \<and> M(x,p,q,z) *)
definition merge_guard ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (('a, 'b, 'b) mrg, 'c) urel \<Rightarrow> (('a, 'b, 'b) mrg, 'c) urel"
where "merge_guard G M \<equiv> (\<lambda>(m,z).
  G (mrg_prior\<^sub>v m) (mrg_left\<^sub>v m) \<and> G (mrg_prior\<^sub>v m) (mrg_right\<^sub>v m) \<and> M (m,z))"

lemma merge_guard_eval:
  "merge_eval (merge_guard G M) x p q z = (G x p \<and> G x q \<and> merge_eval M x p q z)"
  by (simp add: merge_guard_def)

lemma merge_guard_cong:
  assumes "\<And>x p q z. \<lbrakk> G x p; G x q \<rbrakk> \<Longrightarrow> merge_eval M x p q z = merge_eval N x p q z"
  shows "merge_guard G M = merge_guard G N"
  apply (rule ext, clarify)
  subgoal for m z by (cases m; use assms in \<open>auto simp: merge_guard_def\<close>)
  done

lemma AssocMerge_merge_guard:
  assumes "AssocMerge M"
    and "\<And>x p q z. \<lbrakk> G x p; G x q; merge_eval M x p q z \<rbrakk> \<Longrightarrow> G x z"
  shows "AssocMerge (merge_guard G M)"
  using assms unfolding AssocMerge_iff merge_guard_eval
  by (intro allI) blast

lemma SymMerge_merge_guard:
  "M is SymMerge \<Longrightarrow> merge_guard G M is SymMerge"
  by (simp add: SymMerge_eval merge_guard_eval; blast)

text \<open> On operands satisfying @{term G}, the guarded merge gives the same parallel. \<close>

lemma par_by_merge_guard:
  assumes "\<And>x z. P (x,z) \<Longrightarrow> G x z" "\<And>x z. Q (x,z) \<Longrightarrow> G x z"
  shows "P \<parallel>\<^bsub>merge_guard G M\<^esub> Q = P \<parallel>\<^bsub>M\<^esub> Q"
  by (rule ext, clarify; simp only: par_by_merge_eval merge_guard_eval; use assms in blast)

lemma par_by_merge_assoc_guard:
  assumes sym: "merge_guard G M is SymMerge"
    and assoc: "AssocMerge (merge_guard G M)"
    and closed: "\<And>x p q z. \<lbrakk> G x p; G x q; merge_eval M x p q z \<rbrakk> \<Longrightarrow> G x z"
    and operands: "\<And>x z. P (x,z) \<Longrightarrow> G x z"
      "\<And>x z. Q (x,z) \<Longrightarrow> G x z"
      "\<And>x z. R (x,z) \<Longrightarrow> G x z"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) \<parallel>\<^bsub>M\<^esub> R = P \<parallel>\<^bsub>M\<^esub> (Q \<parallel>\<^bsub>M\<^esub> R)"
proof -
  have pq: "(P \<parallel>\<^bsub>M\<^esub> Q) (x,z) \<Longrightarrow> G x z"
    and qr: "(Q \<parallel>\<^bsub>M\<^esub> R) (x,z) \<Longrightarrow> G x z" for x z
    unfolding par_by_merge_eval using closed operands by blast+
  show ?thesis
    using par_by_merge_assoc[OF sym assoc, of P Q R]
    by (simp only: par_by_merge_guard[OF operands(1,2)] par_by_merge_guard[OF operands(2,3)]
        par_by_merge_guard[OF pq operands(3)] par_by_merge_guard[OF operands(1) qr])
qed

end
