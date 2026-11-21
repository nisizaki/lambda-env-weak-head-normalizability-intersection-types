theory Reduction
  imports Syntax ARS
begin

section \<open>Weak-head reduction: full \<open>\<sigma>\<close> plus head \<open>\<beta>\<close> (with VarR)\<close>

text \<open>
  Weak-head reduction is the union of full \<open>\<sigma>\<close> (all root rules and all
  congruences) and head \<open>\<beta>\<close> (\<open>Beta1\<close>, \<open>Beta2\<close> with the congruences
  \<open>AppL\<close>, \<open>CompL\<close> and \<open>VarR\<close>).  \<open>VarR\<close> evaluates the environment of a
  variable lookup.
\<close>

inductive sig :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<sigma>" 50) where
  Ass: "Comp (Comp L M) N \<rightarrow>\<^sub>\<sigma> Comp L (Comp M N)"
| IdL: "Comp Id M \<rightarrow>\<^sub>\<sigma> M"
| IdR: "Comp M Id \<rightarrow>\<^sub>\<sigma> M"
| DExtn: "Comp (Extn L x M) N \<rightarrow>\<^sub>\<sigma> Extn (Comp L N) x (Comp M N)"
| VarRef: "Comp (Var x) (Extn M x N) \<rightarrow>\<^sub>\<sigma> M"
| VarSkip: "x \<noteq> y \<Longrightarrow> Comp (Var y) (Extn M x N) \<rightarrow>\<^sub>\<sigma> Comp (Var y) N"
| DApp: "Comp (App M1 M2) N \<rightarrow>\<^sub>\<sigma> App (Comp M1 N) (Comp M2 N)"
| AppL: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> App M L \<rightarrow>\<^sub>\<sigma> App N L"
| AppR: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> App L M \<rightarrow>\<^sub>\<sigma> App L N"
| Lam: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Lam x M \<rightarrow>\<^sub>\<sigma> Lam x N"
| CompL: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Comp M L \<rightarrow>\<^sub>\<sigma> Comp N L"
| CompR: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Comp L M \<rightarrow>\<^sub>\<sigma> Comp L N"
| ExtnL: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Extn M x L \<rightarrow>\<^sub>\<sigma> Extn N x L"
| ExtnR: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> Extn L x M \<rightarrow>\<^sub>\<sigma> Extn L x N"

inductive beta_h :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<beta>" 50) where
  Beta1: "App (Comp (Lam x M) L) N \<rightarrow>\<^sub>\<beta> Comp M (Extn N x L)"
| Beta2: "App (Lam x M) N \<rightarrow>\<^sub>\<beta> Comp M (Extn N x Id)"
| AppL: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> App M L \<rightarrow>\<^sub>\<beta> App N L"
| CompL: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> Comp M L \<rightarrow>\<^sub>\<beta> Comp N L"
| VarR: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> Comp (Var x) M \<rightarrow>\<^sub>\<beta> Comp (Var x) N"

definition wh :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>w\<^sub>h" 50) where
  "M \<rightarrow>\<^sub>w\<^sub>h N \<longleftrightarrow> M \<rightarrow>\<^sub>\<sigma> N \<or> M \<rightarrow>\<^sub>\<beta> N"

abbreviation wh_steps :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>w\<^sub>h\<^sup>*" 50) where
  "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<equiv> wh\<^sup>*\<^sup>* M N"

abbreviation WHNF :: "trm \<Rightarrow> bool" where "WHNF M \<equiv> normal wh M"
abbreviation WHSN :: "trm \<Rightarrow> bool" where "WHSN M \<equiv> SN_at wh M"
abbreviation sig_normal :: "trm \<Rightarrow> bool" where "sig_normal M \<equiv> normal sig M"

lemma sig_imp_wh: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h N" by (simp add: wh_def)
lemma beta_h_imp_wh: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h N" by (simp add: wh_def)

lemma wh_AppL: "M \<rightarrow>\<^sub>w\<^sub>h N \<Longrightarrow> App M L \<rightarrow>\<^sub>w\<^sub>h App N L"
  by (auto simp: wh_def intro: sig.AppL beta_h.AppL)
lemma wh_CompL: "M \<rightarrow>\<^sub>w\<^sub>h N \<Longrightarrow> Comp M L \<rightarrow>\<^sub>w\<^sub>h Comp N L"
  by (auto simp: wh_def intro: sig.CompL beta_h.CompL)
lemma wh_VarR: "M \<rightarrow>\<^sub>w\<^sub>h N \<Longrightarrow> Comp (Var x) M \<rightarrow>\<^sub>w\<^sub>h Comp (Var x) N"
  by (auto simp: wh_def intro: sig.CompR beta_h.VarR)

lemma WHNF_imp_sig_normal: "WHNF M \<Longrightarrow> sig_normal M"
  by (auto simp: normal_def wh_def)

subsection \<open>\<open>\<sigma>\<close> terminates (measure \<^verbatim>\<open>tlength\<close>)\<close>

lemma sig_tlength_decrease: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> tlength N < tlength M"
proof (induction rule: sig.induct)
  case (Ass L M N)
  have eq: "(tlength M + 1) * (tlength N + 1) = tlength M * (tlength N + 1) + tlength N + 1"
    by (simp add: algebra_simps)
  have "tlength M * (tlength N + 1) + 1 < (tlength M + 1) * (tlength N + 1)"
    using eq tlength_pos[of N] by linarith
  then have "tlength L * (tlength M * (tlength N + 1) + 1)
      < tlength L * ((tlength M + 1) * (tlength N + 1))"
    using tlength_pos[of L] by (rule mult_strict_left_mono)
  then show ?case
    by (simp only: tlength.simps mult.assoc)
next
  case (DExtn L x M N)
  then show ?case
    using tlength_pos[of N] by (simp add: algebra_simps)
next
  case (DApp M1 M2 N)
  then show ?case
    using tlength_pos[of N] by (simp add: algebra_simps)
next
  case (CompL M N L)
  have "tlength N * (tlength L + 1) < tlength M * (tlength L + 1)"
    using CompL.IH by (rule mult_strict_right_mono) simp
  then show ?case
    by (simp only: tlength.simps)
next
  case (CompR M N L)
  have "tlength L * (tlength N + 1) < tlength L * (tlength M + 1)"
    using CompR.IH tlength_pos[of L] by (intro mult_strict_left_mono) simp_all
  then show ?case
    by (simp only: tlength.simps)
qed simp_all

theorem sig_SN: "SN_at sig M"
proof (induction "tlength M" arbitrary: M rule: less_induct)
  case less
  show ?case
    by (rule SN_atI) (auto intro: less dest: sig_tlength_decrease)
qed

subsection \<open>Finite branching\<close>

fun wh_succs :: "trm \<Rightarrow> trm set" where
  "wh_succs (Var _) = {}"
| "wh_succs Id = {}"
| "wh_succs (Lam x M) = (\<lambda>M'. Lam x M') ` wh_succs M"
| "wh_succs (Extn M x L) = ((\<lambda>M'. Extn M' x L) ` wh_succs M) \<union> ((\<lambda>L'. Extn M x L') ` wh_succs L)"
| "wh_succs (App M N) =
    ((\<lambda>M'. App M' N) ` wh_succs M) \<union> ((\<lambda>N'. App M N') ` wh_succs N) \<union>
    (case M of Lam x P \<Rightarrow> {Comp P (Extn N x Id)}
      | Comp L K \<Rightarrow> (case L of Lam x P \<Rightarrow> {Comp P (Extn N x K)} | _ \<Rightarrow> {}) | _ \<Rightarrow> {})"
| "wh_succs (Comp M N) =
    ((\<lambda>M'. Comp M' N) ` wh_succs M) \<union> ((\<lambda>N'. Comp M N') ` wh_succs N) \<union>
    (case M of Comp L K \<Rightarrow> {Comp L (Comp K N)} | _ \<Rightarrow> {}) \<union>
    (if M = Id then {N} else {}) \<union> (if N = Id then {M} else {}) \<union>
    (case M of Extn L x K \<Rightarrow> {Extn (Comp L N) x (Comp K N)} | _ \<Rightarrow> {}) \<union>
    (case M of App M1 M2 \<Rightarrow> {App (Comp M1 N) (Comp M2 N)} | _ \<Rightarrow> {}) \<union>
    (case M of Var x \<Rightarrow> (case N of Extn L y K \<Rightarrow> (if y = x then {L} else {Comp (Var x) K}) | _ \<Rightarrow> {}) | _ \<Rightarrow> {})"

lemma finite_wh_succs [simp]: "finite (wh_succs M)"
  by (induction M) (auto split: trm.splits)

lemma sig_imp_wh_succs: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> N \<in> wh_succs M"
  by (induction rule: sig.induct) auto

lemma beta_h_imp_wh_succs: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> N \<in> wh_succs M"
  by (induction rule: beta_h.induct) auto

lemma finite_wh_successors: "finite {N. M \<rightarrow>\<^sub>w\<^sub>h N}"
proof -
  have "{N. M \<rightarrow>\<^sub>w\<^sub>h N} \<subseteq> wh_succs M"
    by (auto simp: wh_def dest: sig_imp_wh_succs beta_h_imp_wh_succs)
  then show ?thesis using finite_wh_succs finite_subset by blast
qed

end
