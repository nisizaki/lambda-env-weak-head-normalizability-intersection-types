theory Classical
  imports CDV Main_Results
begin

section \<open>E2: agreement with the classical intersection-type system\<close>

text \<open>
  Remark.  Theorem \<open>E2\<close> is obtained through the classical theorem
  \<open>classical_WHN\<close> (in \<open>CDV\<close>): both the \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> typability of a pure term and the CDV
  typability (with an essential type) of its readback characterize weak-head
  normalizability of the readback.  It is not a syntactic translation of
  derivations between the two systems.
\<close>

theorem E2:
  assumes "pure M"
  shows "Typ M \<longleftrightarrow> (\<exists>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>c rb M DVar : A \<and> cess A)"
  using pure_characterization[OF assms] classical_WHN by blast

end
