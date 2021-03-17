subsection \<open> Liberation \<close>

theory utp_liberate
  imports utp_unrest
begin

definition liberate_pred :: "'s set \<Rightarrow> 's scene \<Rightarrow> 's set" where
"liberate_pred P x = {s. \<exists> s'. (s \<oplus>\<^sub>S s' on x) \<in> P}"

adhoc_overloading liberate liberate_pred

end