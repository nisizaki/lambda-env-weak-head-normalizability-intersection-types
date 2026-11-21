theory Main_Results
  imports Readback Soundness
begin

section \<open>Main results\<close>

text \<open>
  \<^item> \<open>main_characterization\<close>: \<open>Typ M \<longleftrightarrow> CFWHN M\<close> for all raw \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> terms.
  \<^item> \<open>E1\<close>: for pure \<open>\<lambda>\<close>-terms, \<open>\<lambda>\<close>-calculus weak-head normalizability of the
    readback coincides with \<open>CFWHN\<close> and with \<open>CFWHSN\<close>.
  \<^item> \<open>clash_not_Typ\<close>: clashes are not typable.
\<close>

theorem pure_characterization:
  assumes "pure M"
  shows "Typ M \<longleftrightarrow> lam_WHN (rb M DVar)"
  using main_characterization E1[OF assms] by blast

end
