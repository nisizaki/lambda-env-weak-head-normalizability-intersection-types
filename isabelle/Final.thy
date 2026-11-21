theory Final
  imports Uniform Classical Examples
begin

section \<open>Summary of the main results\<close>

text \<open>
  \<^item> \<open>main_characterization_full\<close>: \<open>Typ M \<longleftrightarrow> CFWHN M \<and> CFWHSN M\<close> for all raw terms.
  \<^item> \<open>CFWHN_imp_CFWHSN_general\<close>, \<open>WHNF_unique\<close>: weak and strong weak-head
    normalization coincide; the weak-head normal form is unique.
  \<^item> \<open>E1\<close>, \<open>pure_characterization\<close>: conservativity over the \<open>\<lambda>\<close>-calculus.
  \<^item> \<open>classical_WHN\<close>, \<open>E2\<close>: the classical CDV characterization and agreement of
    typability on pure terms.
\<close>

theorem lambda_env_WHN_characterization:
  "Typ M \<longleftrightarrow> CFWHN M"
  "Typ M \<longleftrightarrow> CFWHSN M"
  using main_characterization_full CFWHN_imp_CFWHSN_general CFWHSN_imp_CFWHN by blast+

end
