theory Readback
  imports WHNF_Classes Lambda
begin

section \<open>Readback into the \<open>\<lambda>\<close>-calculus and the extension theorem E1\<close>

subsection \<open>Sorted (proper) terms\<close>

text \<open>
  \<open>tm\<close>: term-sorted, \<open>en\<close>: environment-sorted.  Environments are built from
  \<open>id\<close>, extensions and compositions; there are no environment variables.
  Pure \<open>\<lambda>\<close>-terms are term-sorted, and sortedness is preserved by \<open>\<rightarrow>\<^sub>w\<^sub>h\<close>.
\<close>

fun tm :: "trm \<Rightarrow> bool" and en :: "trm \<Rightarrow> bool" where
  "tm (Var x) = True"
| "tm (Lam x M) = tm M"
| "tm (App M N) = (tm M \<and> tm N)"
| "tm (Comp M L) = (tm M \<and> en L)"
| "tm Id = False"
| "tm (Extn M x L) = False"
| "en (Var x) = False"
| "en (Lam x M) = False"
| "en (App M N) = False"
| "en (Comp L1 L2) = (en L1 \<and> en L2)"
| "en Id = True"
| "en (Extn M x L) = (tm M \<and> en L)"

fun pure :: "trm \<Rightarrow> bool" where
  "pure (Var x) = True"
| "pure (Lam x M) = pure M"
| "pure (App M N) = (pure M \<and> pure N)"
| "pure _ = False"

lemma pure_tm: "pure M \<Longrightarrow> tm M"
  by (induction M) auto

subsection \<open>Readback\<close>

text \<open>\<open>junk\<close> is used for ill-sorted positions; it is closed, so substitution fixes it.\<close>

definition junk :: dB where "junk = DAbs (DVar 0)"

lemma subst_junk [simp]: "junk[s/k] = junk"
  by (simp add: junk_def)

fun rb :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> dB" and rbe :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> (var \<Rightarrow> dB)" where
  "rb (Var x) \<rho> = \<rho> x"
| "rb (Lam x M) \<rho> = DAbs (rb M ((\<lambda>y. lift (\<rho> y) 0)(x := DVar 0)))"
| "rb (App M N) \<rho> = DApp (rb M \<rho>) (rb N \<rho>)"
| "rb (Comp M L) \<rho> = rb M (rbe L \<rho>)"
| "rb Id \<rho> = junk"
| "rb (Extn M x L) \<rho> = junk"
| "rbe (Var x) \<rho> = \<rho>"
| "rbe (Lam x M) \<rho> = \<rho>"
| "rbe (App M N) \<rho> = \<rho>"
| "rbe (Comp L1 L2) \<rho> = rbe L1 (rbe L2 \<rho>)"
| "rbe Id \<rho> = \<rho>"
| "rbe (Extn M x L) \<rho> = (rbe L \<rho>)(x := rb M \<rho>)"

lemma rb_subst:
  "(\<forall>\<sigma> s k. (rb M \<sigma>)[s/k] = rb M (\<lambda>y. (\<sigma> y)[s/k])) \<and>
   (\<forall>\<sigma> s k. rbe M (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe M \<sigma> y)[s/k]))"
proof (induction M)
  case (Var x)
  then show ?case by simp
next
  case (Lam x M)
  have "(rb (Lam x M) \<sigma>)[s/k] = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])" for \<sigma> s k
  proof -
    have fe: "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1])
            = (\<lambda>y. lift ((\<sigma> y)[s/k]) 0)(x := DVar 0)"
      by (rule ext) (simp add: lift_subst_lt)
    have "(rb (Lam x M) \<sigma>)[s/k]
        = DAbs ((rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[lift s 0 / k + 1])"
      by simp
    also have "\<dots> = DAbs (rb M (\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1]))"
      using Lam.IH by simp
    also have "\<dots> = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])"
      by (simp only: fe rb.simps)
    finally show ?thesis .
  qed
  then show ?case by simp
next
  case (App M N)
  then show ?case by simp
next
  case Id
  then show ?case by simp
next
  case (Extn M x L)
  have "rbe (Extn M x L) (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe (Extn M x L) \<sigma> y)[s/k])" for \<sigma> s k
    using Extn.IH by (auto intro!: ext)
  then show ?case by simp
next
  case (Comp M L)
  then show ?case by simp
qed

lemma beta_rb:
  "(rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[t/0] = rb M (\<sigma>(x := t))"
proof -
  have "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[t/0]) = \<sigma>(x := t)"
    by (rule ext) simp
  then show ?thesis
    using rb_subst[of M] by simp
qed

subsection \<open>Simulation\<close>

lemma sig_sorted:
  "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow>
     (tm M \<longrightarrow> tm N \<and> (\<forall>\<rho>. rb N \<rho> = rb M \<rho>)) \<and>
     (en M \<longrightarrow> en N \<and> (\<forall>\<rho>. rbe N \<rho> = rbe M \<rho>))"
  by (induction rule: sig.induct) (auto simp: fun_upd_def)

lemma beta_not_en: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> \<not> en M"
  by (induction rule: beta_h.induct) auto

lemma beta_sorted:
  "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> tm M \<Longrightarrow> tm N \<and> (\<forall>\<rho>. rb M \<rho> \<rightarrow>\<^sub>h rb N \<rho>)"
proof (induction rule: beta_h.induct)
  case (Beta1 x M L N)
  have "rb (App (Comp (Lam x M) L) N) \<rho> \<rightarrow>\<^sub>h rb (Comp M (Extn N x L)) \<rho>" for \<rho>
    using hbeta[of "rb M ((\<lambda>y. lift (rbe L \<rho> y) 0)(x := DVar 0))" "rb N \<rho>"]
    by (simp add: beta_rb)
  then show ?case using Beta1 by simp
next
  case (Beta2 x M N)
  have "rb (App (Lam x M) N) \<rho> \<rightarrow>\<^sub>h rb (Comp M (Extn N x Id)) \<rho>" for \<rho>
    using hbeta[of "rb M ((\<lambda>y. lift (\<rho> y) 0)(x := DVar 0))" "rb N \<rho>"]
    by (simp add: beta_rb)
  then show ?case using Beta2 by simp
next
  case (AppL M N L)
  then show ?case by (auto intro: happ)
next
  case (CompL M N L)
  then show ?case by auto
next
  case (VarR M N x)
  then show ?case using beta_not_en by auto
qed

lemma wh_sorted:
  assumes "M \<rightarrow>\<^sub>w\<^sub>h N" "tm M"
  shows "tm N \<and> ((\<forall>\<rho>. rb N \<rho> = rb M \<rho>) \<and> tlength N < tlength M \<or> (\<forall>\<rho>. rb M \<rho> \<rightarrow>\<^sub>h rb N \<rho>))"
  using assms sig_sorted beta_sorted sig_tlength_decrease by (auto simp: wh_def)

lemma wh_steps_sorted:
  "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<Longrightarrow> tm M \<Longrightarrow> tm N \<and> hred\<^sup>*\<^sup>* (rb M \<rho>) (rb N \<rho>)"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step N P)
  then show ?case
    using wh_sorted[of N P] by (auto intro: rtranclp.rtrancl_into_rtrancl)
qed

subsection \<open>Normal forms\<close>

lemma sorted_not_clash: "clash M \<Longrightarrow> \<not> tm M \<and> \<not> en M"
  by (induction rule: clash.induct) auto

inductive hneu :: "dB \<Rightarrow> bool" where
  "hneu (DVar i)"
| "hneu s \<Longrightarrow> hneu (DApp s t)"

lemma hneu_normal: "hneu s \<Longrightarrow> normal hred s"
proof (induction rule: hneu.induct)
  case (1 i)
  then show ?case by (auto simp: normal_def elim: hred.cases)
next
  case (2 s t)
  then show ?case by (auto simp: normal_def elim: hred.cases hneu.cases)
qed

lemma DAbs_normal: "normal hred (DAbs s)"
  by (auto simp: normal_def elim: hred.cases)

lemma neu_not_en: "neu M \<Longrightarrow> \<not> en M"
  by (induction rule: neu.induct) auto

lemma neu_rb: "neu M \<Longrightarrow> tm M \<Longrightarrow> hneu (rb M DVar)"
proof (induction rule: neu.induct)
  case (NVar x)
  then show ?case by (simp add: hneu.intros)
next
  case (NApp M N)
  then show ?case by (simp add: hneu.intros)
next
  case (NComp M x)
  then show ?case using neu_not_en by simp
qed

theorem rb_WHNF: "tm M \<Longrightarrow> WHNF M \<Longrightarrow> normal hred (rb M DVar)"
proof -
  assume t: "tm M" and n: "WHNF M"
  from n consider "neu M" | "val M" | "clash M" by (auto simp: WHNF_iff_classes)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using t neu_rb hneu_normal by blast
  next
    case 2
    then show ?thesis using t by (cases rule: val.cases) (simp_all add: DAbs_normal)
  next
    case 3
    then show ?thesis using t sorted_not_clash by blast
  qed
qed

subsection \<open>E1\<close>

lemma SN_at_normal_reachable: "SN_at R a \<Longrightarrow> \<exists>b. R\<^sup>*\<^sup>* a b \<and> normal R b"
proof (induction rule: SN_at_induct)
  case (step a)
  show ?case
  proof (cases "normal R a")
    case True
    then show ?thesis by blast
  next
    case False
    then obtain b where "R a b" by (auto simp: normal_def)
    with step.IH[OF this] show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed
qed

lemma CFWHSN_imp_CFWHN:
  assumes "CFWHSN M"
  shows "CFWHN M"
proof -
  have sn: "WHSN M" and cf: "\<And>N. M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<Longrightarrow> WHNF N \<Longrightarrow> \<not> clash N"
    using assms by (auto simp: CFWHSN_def)
  obtain N where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and n: "WHNF N"
    using SN_at_normal_reachable[OF sn] by blast
  show ?thesis
    unfolding CFWHN_def using r n cf[OF r n] by blast
qed

lemma CFWHN_imp_lam_WHN:
  assumes t: "tm M" and c: "CFWHN M"
  shows "lam_WHN (rb M DVar)"
proof -
  obtain N where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and n: "WHNF N"
    using c by (auto simp: CFWHN_def)
  from wh_steps_sorted[OF r t] have tN: "tm N" and h: "hred\<^sup>*\<^sup>* (rb M DVar) (rb N DVar)"
    by blast+
  show ?thesis
    unfolding lam_WHN_def using h rb_WHNF[OF tN n] by blast
qed

lemma hdist_imp_WHSN: "hdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> WHSN M"
proof (induction n arbitrary: M rule: less_induct)
  case (less n)
  note IHn = less.IH
  have "\<And>M. hdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> WHSN M"
  proof -
    fix M
    show "hdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> WHSN M"
    proof (induction "tlength M" arbitrary: M rule: less_induct)
      case less
      show ?case
      proof (rule SN_atI)
        fix N
        assume s: "M \<rightarrow>\<^sub>w\<^sub>h N"
        from wh_sorted[OF s \<open>tm M\<close>] have tN: "tm N"
          and c: "(\<forall>\<rho>. rb N \<rho> = rb M \<rho>) \<and> tlength N < tlength M \<or> (\<forall>\<rho>. rb M \<rho> \<rightarrow>\<^sub>h rb N \<rho>)"
          by blast+
        from c show "WHSN N"
        proof
          assume a: "(\<forall>\<rho>. rb N \<rho> = rb M \<rho>) \<and> tlength N < tlength M"
          then have "hdist (rb N DVar) n" using less.prems(1) by simp
          then show "WHSN N" using less.hyps a tN by blast
        next
          assume "\<forall>\<rho>. rb M \<rho> \<rightarrow>\<^sub>h rb N \<rho>"
          then obtain m where "n = Suc m" "hdist (rb N DVar) m"
            using hdist_step less.prems(1) by blast
          then show "WHSN N" using IHn tN by blast
        qed
      qed
    qed
  qed
  then show ?case using less.prems by blast
qed

lemma lam_WHN_imp_CFWHSN: "tm M \<Longrightarrow> lam_WHN (rb M DVar) \<Longrightarrow> CFWHSN M"
proof -
  assume t: "tm M" and w: "lam_WHN (rb M DVar)"
  then obtain n where "hdist (rb M DVar) n" using lam_WHN_hdist by blast
  then have "WHSN M" using t hdist_imp_WHSN by blast
  moreover have "\<not> clash N" if r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" for N
  proof -
    have "tm N" using wh_steps_sorted[OF r t] by blast
    then show ?thesis using sorted_not_clash by blast
  qed
  ultimately show ?thesis by (auto simp: CFWHSN_def)
qed

theorem E1_sorted:
  assumes "tm M"
  shows "(lam_WHN (rb M DVar) \<longleftrightarrow> CFWHN M) \<and> (CFWHN M \<longleftrightarrow> CFWHSN M)"
  using assms CFWHN_imp_lam_WHN lam_WHN_imp_CFWHSN CFWHSN_imp_CFWHN by blast

theorem E1:
  assumes "pure M"
  shows "(lam_WHN (rb M DVar) \<longleftrightarrow> CFWHN M) \<and> (CFWHN M \<longleftrightarrow> CFWHSN M)"
  using E1_sorted pure_tm assms by blast

end
