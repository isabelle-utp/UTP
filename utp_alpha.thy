theory utp_alpha
  imports utp_subst
begin

named_theorems alpha

lemma unrest_aext_pred_lens [unrest]: "\<lbrakk> mwb_lens x; x \<bowtie> a \<rbrakk> \<Longrightarrow> $x \<sharp> (P :: 's set) \<up> a"
  by (pred_simp)

end
