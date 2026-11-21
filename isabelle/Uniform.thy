theory Uniform
  imports Sig_Confluence Main_Results
begin

section \<open>Uniform normalization: \<open>CFWHN M \<Longrightarrow> CFWHSN M\<close>\<close>

text \<open>
  \<open>\<rightarrow>\<^sub>\<beta>\<close> (head \<open>\<beta>\<close>) is deterministic, \<open>\<sigma>\<close> is terminating and confluent, and a
  \<open>\<sigma>\<close>-step commutes with the \<open>\<beta>\<close>-step (\<open>beta_sig_commute\<close>).  Hence every
  \<open>\<rightarrow>\<^sub>w\<^sub>h\<close>-path follows one deterministic chain of \<open>\<sigma>\<close>-normal forms, and the number of
  \<open>\<beta>\<close>-steps on any path is bounded by the length of that chain.
\<close>

subsection \<open>Head \<open>\<beta>\<close> is deterministic\<close>

lemma Var_no_beta: "Var x \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> False"
  by (auto elim: beta_h.cases)
lemma Id_no_beta: "Id \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> False"
  by (auto elim: beta_h.cases)
lemma Lam_no_beta: "Lam x M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> False"
  by (auto elim: beta_h.cases)
lemma Extn_no_beta: "Extn M x L \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> False"
  by (auto elim: beta_h.cases)
lemma Clo_no_beta: "Comp (Lam x M) L \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> False"
  by (auto elim: beta_h.cases dest: Lam_no_beta)

lemma beta_det: "M \<rightarrow>\<^sub>\<beta> N1 \<Longrightarrow> M \<rightarrow>\<^sub>\<beta> N2 \<Longrightarrow> N1 = N2"
proof (induction arbitrary: N2 rule: beta_h.induct)
  case (Beta1 x M L N)
  from Beta1.prems show ?case
    by (cases rule: beta_h.cases) (auto dest: Clo_no_beta)
next
  case (Beta2 x M N)
  from Beta2.prems show ?case
    by (cases rule: beta_h.cases) (auto dest: Lam_no_beta)
next
  case (AppL M N L)
  note IH = AppL.IH and h = AppL.hyps
  from AppL.prems show ?case
  proof (cases rule: beta_h.cases)
    case (Beta1 x B K)
    then have "Comp (Lam x B) K \<rightarrow>\<^sub>\<beta> N" using h by simp
    then show ?thesis by (rule Clo_no_beta[THEN FalseE])
  next
    case (Beta2 x B)
    then have "Lam x B \<rightarrow>\<^sub>\<beta> N" using h by simp
    then show ?thesis by (rule Lam_no_beta[THEN FalseE])
  next
    case (AppL N')
    then show ?thesis using IH by simp
  qed
next
  case (CompL M N L)
  note IH = CompL.IH and h = CompL.hyps
  from CompL.prems show ?case
  proof (cases rule: beta_h.cases)
    case (CompL N')
    then show ?thesis using IH by simp
  next
    case VarR
    then obtain x0 where "M = Var x0" by blast
    then have "Var x0 \<rightarrow>\<^sub>\<beta> N" using h by simp
    then show ?thesis by (rule Var_no_beta[THEN FalseE])
  qed
next
  case (VarR M N x)
  note IH = VarR.IH and h = VarR.hyps
  from VarR.prems show ?case
  proof (cases rule: beta_h.cases)
    case (CompL N')
    then have "Var x \<rightarrow>\<^sub>\<beta> N'" by simp
    then show ?thesis by (rule Var_no_beta[THEN FalseE])
  next
    case VarR
    then show ?thesis using IH by simp
  qed
qed

subsection \<open>Congruences for \<open>\<sigma>\<^sup>*\<close>\<close>

lemma ss_lift:
  assumes "\<And>P Q. P \<rightarrow>\<^sub>\<sigma> Q \<Longrightarrow> f P \<rightarrow>\<^sub>\<sigma> f Q"
  shows "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (f M) (f N)"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl assms)

lemma ss_AppL: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (App M L) (App N L)"
  by (rule ss_lift[of "\<lambda>P. App P L"]) (rule sig.AppL)
lemma ss_CompR: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp L M) (Comp L N)"
  by (rule ss_lift[of "\<lambda>P. Comp L P"]) (rule sig.CompR)
lemma ss_CompL: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp M L) (Comp N L)"
  by (rule ss_lift[of "\<lambda>P. Comp P L"]) (rule sig.CompL)

lemma ss1: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> sig\<^sup>*\<^sup>* M N" by (rule r_into_rtranclp)

subsection \<open>Commutation of a \<open>\<sigma>\<close>-step with the \<open>\<beta>\<close>-step\<close>

lemma Lam_sig_inv: "Lam x B \<rightarrow>\<^sub>\<sigma> P \<Longrightarrow> \<exists>B'. P = Lam x B' \<and> B \<rightarrow>\<^sub>\<sigma> B'"
  by (auto elim: sig.cases)

lemma Clo_sig_inv:
  assumes "Comp (Lam x B) K \<rightarrow>\<^sub>\<sigma> P"
  shows "(\<exists>B'. P = Comp (Lam x B') K \<and> B \<rightarrow>\<^sub>\<sigma> B') \<or> (\<exists>K'. P = Comp (Lam x B) K' \<and> K \<rightarrow>\<^sub>\<sigma> K') \<or>
     (K = Id \<and> P = Lam x B)"
  using assms
proof (cases rule: sig.cases)
  case (CompL B0)
  then show ?thesis using Lam_sig_inv by blast
next
  case (CompR K')
  then show ?thesis by blast
next
  case IdR
  then show ?thesis by blast
qed

definition comm :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "comm M1 M2 \<longleftrightarrow> (\<exists>M1' M3. sig\<^sup>*\<^sup>* M1 M1' \<and> M1' \<rightarrow>\<^sub>\<beta> M3 \<and> sig\<^sup>*\<^sup>* M2 M3)"

lemma commI: "sig\<^sup>*\<^sup>* M1 M1' \<Longrightarrow> M1' \<rightarrow>\<^sub>\<beta> M3 \<Longrightarrow> sig\<^sup>*\<^sup>* M2 M3 \<Longrightarrow> comm M1 M2"
  unfolding comm_def by blast

lemma comm_direct: "M1 \<rightarrow>\<^sub>\<beta> M3 \<Longrightarrow> sig\<^sup>*\<^sup>* M2 M3 \<Longrightarrow> comm M1 M2"
  by (rule commI[OF rtranclp.rtrancl_refl])

lemma beta_sig_commute: "M \<rightarrow>\<^sub>\<beta> M2 \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> M1 \<Longrightarrow> comm M1 M2"
proof (induction arbitrary: M1 rule: beta_h.induct)
  case (Beta1 x B K N)
  from Beta1.prems show ?case
  proof (cases rule: sig.cases)
    case (AppL P)
    from Clo_sig_inv[OF AppL(2)] show ?thesis
    proof (elim disjE exE conjE)
      fix B' assume "P = Comp (Lam x B') K" "B \<rightarrow>\<^sub>\<sigma> B'"
      then show ?thesis using AppL
        by (auto intro!: comm_direct beta_h.Beta1 ss1 sig.CompL)
    next
      fix K' assume "P = Comp (Lam x B) K'" "K \<rightarrow>\<^sub>\<sigma> K'"
      then show ?thesis using AppL
        by (auto intro!: comm_direct beta_h.Beta1 ss1 sig.CompR sig.ExtnR)
    next
      assume "K = Id" "P = Lam x B"
      then show ?thesis using AppL
        by (auto intro!: comm_direct beta_h.Beta2)
    qed
  next
    case (AppR N')
    then show ?thesis by (auto intro!: comm_direct beta_h.Beta1 ss1 sig.CompR sig.ExtnL)
  qed
next
  case (Beta2 x B N)
  from Beta2.prems show ?case
  proof (cases rule: sig.cases)
    case (AppL P)
    then obtain B' where "P = Lam x B'" "B \<rightarrow>\<^sub>\<sigma> B'" using Lam_sig_inv by blast
    then show ?thesis using AppL by (auto intro!: comm_direct beta_h.Beta2 ss1 sig.CompL)
  next
    case (AppR N')
    then show ?thesis by (auto intro!: comm_direct beta_h.Beta2 ss1 sig.CompR sig.ExtnL)
  qed
next
  case (AppL M M' L)
  from AppL.prems show ?case
  proof (cases rule: sig.cases)
    case (AppL M1a)
    from AppL.IH[OF AppL(2)] obtain M1' M3 where
      a: "sig\<^sup>*\<^sup>* M1a M1'" "M1' \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3"
      by (auto simp: comm_def)
    show ?thesis
      using AppL(1) ss_AppL[OF a(1)] beta_h.AppL[OF a(2)] ss_AppL[OF a(3)]
      by (auto intro: commI)
  next
    case (AppR L')
    then show ?thesis using AppL.hyps by (auto intro!: comm_direct beta_h.AppL ss1 sig.AppR)
  qed
next
  case (CompL M M' L)
  note hyp = CompL.hyps and IH = CompL.IH
  from CompL.prems show ?case
  proof (cases rule: sig.cases)
    case (Ass Ma Mb)
    have hM: "M = Comp Ma Mb" using Ass by simp
    from hyp have "Comp Ma Mb \<rightarrow>\<^sub>\<beta> M'" using hM by simp
    then show ?thesis
    proof (cases rule: beta_h.cases)
      case (CompL Ma')
      then show ?thesis using Ass
        by (auto intro!: comm_direct beta_h.CompL ss1 sig.Ass)
    next
      case (VarR Mb' x)
      then show ?thesis using Ass
        by (auto intro!: comm_direct beta_h.VarR beta_h.CompL ss1 sig.Ass)
    qed
  next
    case IdL
    then show ?thesis using hyp by (auto dest: Id_no_beta)
  next
    case IdR
    have "sig\<^sup>*\<^sup>* (Comp M' Id) M'" by (rule ss1[OF sig.IdR])
    then show ?thesis using IdR hyp by (auto intro: comm_direct)
  next
    case DExtn
    then show ?thesis using hyp by (auto dest: Extn_no_beta)
  next
    case VarRef
    then show ?thesis using hyp by (auto dest: Var_no_beta)
  next
    case VarSkip
    then show ?thesis using hyp by (auto dest: Var_no_beta)
  next
    case (DApp P Q)
    have hM: "M = App P Q" using DApp by simp
    from hyp have "App P Q \<rightarrow>\<^sub>\<beta> M'" using hM by simp
    then show ?thesis
    proof (cases rule: beta_h.cases)
      case (Beta1 x B K)
      have s1: "sig\<^sup>*\<^sup>* M1 (App (Comp (Lam x B) (Comp K L)) (Comp Q L))"
        using DApp Beta1 by (auto intro!: ss1 sig.AppL sig.Ass)
      have b: "App (Comp (Lam x B) (Comp K L)) (Comp Q L) \<rightarrow>\<^sub>\<beta> Comp B (Extn (Comp Q L) x (Comp K L))"
        by (rule beta_h.Beta1)
      have s2: "sig\<^sup>*\<^sup>* (Comp (Comp B (Extn Q x K)) L) (Comp B (Extn (Comp Q L) x (Comp K L)))"
      proof -
        have "Comp (Comp B (Extn Q x K)) L \<rightarrow>\<^sub>\<sigma> Comp B (Comp (Extn Q x K) L)" by (rule sig.Ass)
        moreover have "Comp B (Comp (Extn Q x K) L) \<rightarrow>\<^sub>\<sigma> Comp B (Extn (Comp Q L) x (Comp K L))"
          by (rule sig.CompR[OF sig.DExtn])
        ultimately show ?thesis by (meson converse_rtranclp_into_rtranclp ss1)
      qed
      show ?thesis using s1 b s2 Beta1 DApp by (auto intro: commI)
    next
      case (Beta2 x B)
      have b: "M1 \<rightarrow>\<^sub>\<beta> Comp B (Extn (Comp Q L) x L)"
        using DApp Beta2 by (auto intro: beta_h.Beta1)
      have s2: "sig\<^sup>*\<^sup>* (Comp (Comp B (Extn Q x Id)) L) (Comp B (Extn (Comp Q L) x L))"
      proof -
        have 1: "Comp (Comp B (Extn Q x Id)) L \<rightarrow>\<^sub>\<sigma> Comp B (Comp (Extn Q x Id) L)" by (rule sig.Ass)
        have 2: "Comp B (Comp (Extn Q x Id) L) \<rightarrow>\<^sub>\<sigma> Comp B (Extn (Comp Q L) x (Comp Id L))"
          by (rule sig.CompR[OF sig.DExtn])
        have 3: "Comp B (Extn (Comp Q L) x (Comp Id L)) \<rightarrow>\<^sub>\<sigma> Comp B (Extn (Comp Q L) x L)"
          by (rule sig.CompR[OF sig.ExtnR[OF sig.IdL]])
        from 1 2 3 show ?thesis by (meson converse_rtranclp_into_rtranclp ss1)
      qed
      show ?thesis using b s2 Beta2 DApp by (auto intro: comm_direct)
    next
      case (AppL P')
      then show ?thesis using DApp
        by (auto intro!: comm_direct beta_h.AppL beta_h.CompL ss1 sig.DApp)
    qed
  next
    case (CompL M1a)
    from IH[OF CompL(2)] obtain M1' M3 where
      a: "sig\<^sup>*\<^sup>* M1a M1'" "M1' \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3"
      by (auto simp: comm_def)
    show ?thesis
      using CompL(1) ss_CompL[OF a(1)] beta_h.CompL[OF a(2)] ss_CompL[OF a(3)]
      by (auto intro: commI)
  next
    case (CompR L')
    then show ?thesis using hyp by (auto intro!: comm_direct beta_h.CompL ss1 sig.CompR)
  qed
next
  case (VarR M M' x)
  note hyp = VarR.hyps and IH = VarR.IH
  from VarR.prems show ?case
  proof (cases rule: sig.cases)
    case (CompR M1a)
    from IH[OF CompR(2)] obtain M1' M3 where
      a: "sig\<^sup>*\<^sup>* M1a M1'" "M1' \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3"
      by (auto simp: comm_def)
    show ?thesis
      using CompR(1) ss_CompR[OF a(1)] beta_h.VarR[OF a(2)] ss_CompR[OF a(3)]
      by (auto intro: commI)
  qed (use hyp in \<open>auto dest: Id_no_beta Extn_no_beta Var_no_beta elim: sig.cases\<close>)
qed

subsection \<open>\<open>\<sigma>\<close>-normal forms\<close>

lemma sig_steps_tlength: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> tlength N \<le> tlength M"
  by (induction rule: rtranclp_induct) (auto dest: sig_tlength_decrease)

definition snf :: "trm \<Rightarrow> trm" where
  "snf M = (SOME N. sig\<^sup>*\<^sup>* M N \<and> sig_normal N)"

lemma snf_spec: "sig\<^sup>*\<^sup>* M (snf M) \<and> sig_normal (snf M)"
  unfolding snf_def using sig_nf by (rule someI_ex)

lemma snf_unique: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig_normal N \<Longrightarrow> snf M = N"
proof -
  assume r: "sig\<^sup>*\<^sup>* M N" and n: "sig_normal N"
  obtain P where p1: "sig\<^sup>*\<^sup>* (snf M) P" and p2: "sig\<^sup>*\<^sup>* N P"
    using sig_confluent[OF snf_spec[THEN conjunct1] r] by blast
  have "P = snf M" using normal_rtranclp[OF snf_spec[THEN conjunct2] p1] .
  moreover have "P = N" using normal_rtranclp[OF n p2] .
  ultimately show ?thesis by simp
qed

lemma snf_steps: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> snf M' = snf M"
proof -
  assume r: "sig\<^sup>*\<^sup>* M M'"
  have "sig\<^sup>*\<^sup>* M (snf M')" using r snf_spec[of M'] by (meson rtranclp_trans)
  then have "snf M = snf M'" using snf_unique snf_spec by blast
  then show ?thesis by simp
qed

lemma snf_beta:
  "M \<rightarrow>\<^sub>\<beta> M' \<Longrightarrow> \<exists>M3. snf M \<rightarrow>\<^sub>\<beta> M3 \<and> sig\<^sup>*\<^sup>* M' M3"
proof (induction "tlength M" arbitrary: M M' rule: less_induct)
  case less
  show ?case
  proof (cases "sig_normal M")
    case True
    then have "snf M = M" using snf_unique by blast
    then show ?thesis using less.prems by auto
  next
    case False
    then obtain M1 where s: "M \<rightarrow>\<^sub>\<sigma> M1" by (auto simp: normal_def)
    from beta_sig_commute[OF less.prems s] obtain M1' M3' where
      a: "sig\<^sup>*\<^sup>* M1 M1'" "M1' \<rightarrow>\<^sub>\<beta> M3'" "sig\<^sup>*\<^sup>* M' M3'"
      by (auto simp: comm_def)
    have lt: "tlength M1' < tlength M"
      using sig_tlength_decrease[OF s] sig_steps_tlength[OF a(1)] by simp
    from less.hyps[OF lt a(2)] obtain M3 where b: "snf M1' \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M3' M3"
      by blast
    have "snf M1' = snf M"
      using snf_steps[OF converse_rtranclp_into_rtranclp[OF s a(1)]] .
    then show ?thesis using b a(3) by (metis rtranclp_trans)
  qed
qed

subsection \<open>The deterministic chain\<close>

inductive cd :: "trm \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> bool" where
  cd0: "normal beta_h (snf M) \<Longrightarrow> cd M 0 (snf M)"
| cdS: "snf M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> cd N n E \<Longrightarrow> cd M (Suc n) E"

lemma cd_snf: "cd A n E \<Longrightarrow> snf A = snf B \<Longrightarrow> cd B n E"
proof (cases rule: cd.cases)
  assume "cd A n E" "snf A = snf B"
  {
    assume "normal beta_h (snf A)" "n = 0" "E = snf A"
    then show ?thesis using \<open>snf A = snf B\<close> by (metis cd0)
  }
  {
    fix N m assume "n = Suc m" "snf A \<rightarrow>\<^sub>\<beta> N" "cd N m E"
    then show ?thesis using \<open>snf A = snf B\<close> by (metis cdS)
  }
qed

lemma cd_det: "cd M n E \<Longrightarrow> cd M n' E' \<Longrightarrow> n = n' \<and> E = E'"
proof (induction arbitrary: n' E' rule: cd.induct)
  case (cd0 M)
  from cd0.prems show ?case
    by (cases rule: cd.cases) (use cd0.hyps in \<open>auto simp: normal_def\<close>)
next
  case (cdS M N n E)
  note h = cdS.hyps(1) and IH = cdS.IH
  from cdS.prems show ?case
  proof (cases rule: cd.cases)
    case cd0
    then show ?thesis using h by (auto simp: normal_def)
  next
    case (cdS N' m)
    then have "N' = N" using beta_det h by blast
    then show ?thesis using IH cdS by blast
  qed
qed

lemma cd_back_sig: "M \<rightarrow>\<^sub>\<sigma> M' \<Longrightarrow> cd M' n E \<Longrightarrow> cd M n E"
  using cd_snf snf_steps[OF ss1] by metis

lemma cd_fwd_sig: "M \<rightarrow>\<^sub>\<sigma> M' \<Longrightarrow> cd M n E \<Longrightarrow> cd M' n E"
  using cd_snf snf_steps[OF ss1] by metis

lemma cd_back_beta: "M \<rightarrow>\<^sub>\<beta> M' \<Longrightarrow> cd M' n E \<Longrightarrow> cd M (Suc n) E"
proof -
  assume b: "M \<rightarrow>\<^sub>\<beta> M'" and c: "cd M' n E"
  from snf_beta[OF b] obtain M3 where m3: "snf M \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3" by blast
  have "cd M3 n E" using cd_snf[OF c] snf_steps[OF m3(2)] by simp
  then show ?thesis by (rule cdS[OF m3(1)])
qed

lemma cd_fwd_beta: "M \<rightarrow>\<^sub>\<beta> M' \<Longrightarrow> cd M n E \<Longrightarrow> \<exists>m. n = Suc m \<and> cd M' m E"
proof -
  assume b: "M \<rightarrow>\<^sub>\<beta> M'" and c: "cd M n E"
  from snf_beta[OF b] obtain M3 where m3: "snf M \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3" by blast
  from c show ?thesis
  proof (cases rule: cd.cases)
    case cd0
    then show ?thesis using m3(1) by (auto simp: normal_def)
  next
    case (cdS N m)
    then have "N = M3" using beta_det m3(1) by blast
    then have "cd M3 m E" using cdS by simp
    then have "cd M' m E" using cd_snf snf_steps[OF m3(2)] by metis
    then show ?thesis using cdS by blast
  qed
qed

lemma WHNF_cd: "WHNF N \<Longrightarrow> cd N 0 N"
proof -
  assume n: "WHNF N"
  have sn: "snf N = N" using snf_unique[OF rtranclp.rtrancl_refl WHNF_imp_sig_normal[OF n]] .
  have "normal beta_h N" using n by (auto simp: normal_def wh_def)
  then show ?thesis using cd0[of N] sn by simp
qed

lemma steps_cd: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<Longrightarrow> WHNF N \<Longrightarrow> \<exists>k. cd M k N"
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case using WHNF_cd by blast
next
  case (step M M')
  then obtain k where c: "cd M' k N" by blast
  from step.hyps(1) consider "M \<rightarrow>\<^sub>\<sigma> M'" | "M \<rightarrow>\<^sub>\<beta> M'" by (auto simp: wh_def)
  then show ?case
  proof cases
    case 1 then show ?thesis using cd_back_sig c by blast
  next
    case 2 then show ?thesis using cd_back_beta c by blast
  qed
qed

lemma cd_WHSN: "cd M n E \<Longrightarrow> WHSN M"
proof (induction n arbitrary: M rule: less_induct)
  case (less n)
  note IHn = less.IH
  have "\<And>M. cd M n E \<Longrightarrow> WHSN M"
  proof -
    fix M
    show "cd M n E \<Longrightarrow> WHSN M"
    proof (induction "tlength M" arbitrary: M rule: less_induct)
      case less
      show ?case
      proof (rule SN_atI)
        fix N
        assume s: "M \<rightarrow>\<^sub>w\<^sub>h N"
        then consider "M \<rightarrow>\<^sub>\<sigma> N" | "M \<rightarrow>\<^sub>\<beta> N" by (auto simp: wh_def)
        then show "WHSN N"
        proof cases
          case 1
          have "cd N n E" using cd_fwd_sig[OF 1 less.prems] .
          moreover have "tlength N < tlength M" using sig_tlength_decrease[OF 1] .
          ultimately show ?thesis using less.hyps by blast
        next
          case 2
          then obtain m where "n = Suc m" "cd N m E" using cd_fwd_beta less.prems by blast
          then show ?thesis using IHn by blast
        qed
      qed
    qed
  qed
  then show ?case using less.prems by blast
qed

lemma cd_reach_end: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N' \<Longrightarrow> cd M n E \<Longrightarrow> WHNF N' \<Longrightarrow> N' = E"
proof (induction arbitrary: n rule: converse_rtranclp_induct)
  case base
  then show ?case using WHNF_cd cd_det by blast
next
  case (step M M')
  from step.hyps(1) consider "M \<rightarrow>\<^sub>\<sigma> M'" | "M \<rightarrow>\<^sub>\<beta> M'" by (auto simp: wh_def)
  then show ?case
  proof cases
    case 1 then show ?thesis using cd_fwd_sig step.prems step.IH by blast
  next
    case 2 then show ?thesis using cd_fwd_beta step.prems step.IH by blast
  qed
qed

theorem CFWHN_imp_CFWHSN_general: "CFWHN M \<Longrightarrow> CFWHSN M"
proof -
  assume "CFWHN M"
  then obtain N where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and n: "WHNF N" and c: "\<not> clash N"
    by (auto simp: CFWHN_def)
  from steps_cd[OF r n] obtain k where cdM: "cd M k N" by blast
  have "WHSN M" by (rule cd_WHSN[OF cdM])
  moreover have "\<not> clash N'" if "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N'" "WHNF N'" for N'
    using cd_reach_end[OF that(1) cdM that(2)] c by simp
  ultimately show "CFWHSN M" by (auto simp: CFWHSN_def)
qed

theorem WHNF_unique: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N1 \<Longrightarrow> WHNF N1 \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N2 \<Longrightarrow> WHNF N2 \<Longrightarrow> N1 = N2"
proof -
  assume r1: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N1" and n1: "WHNF N1" and r2: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N2" and n2: "WHNF N2"
  from steps_cd[OF r1 n1] obtain k where "cd M k N1" by blast
  then show ?thesis using cd_reach_end[OF r2 _ n2] by metis
qed

theorem main_characterization_full: "Typ M \<longleftrightarrow> CFWHN M \<and> CFWHSN M"
  using main_characterization CFWHN_imp_CFWHSN_general CFWHSN_imp_CFWHN by blast

end
