theory WHNF_Classes
  imports Reduction
begin

section \<open>Weak-head normal forms: neutral, value, clash\<close>

inductive neu :: "trm \<Rightarrow> bool" where
  NVar: "neu (Var x)"
| NApp: "neu M \<Longrightarrow> sig_normal N \<Longrightarrow> neu (App M N)"
| NComp: "neu M \<Longrightarrow> neu (Comp (Var x) M)"

inductive val :: "trm \<Rightarrow> bool" where
  VLam: "sig_normal M \<Longrightarrow> val (Lam x M)"
| VClo: "sig_normal M \<Longrightarrow> sig_normal L \<Longrightarrow> L \<noteq> Id \<Longrightarrow> val (Comp (Lam x M) L)"
| VId: "val Id"
| VExtn: "sig_normal M \<Longrightarrow> sig_normal L \<Longrightarrow> val (Extn M x L)"

inductive clash :: "trm \<Rightarrow> bool" where
  CId: "sig_normal N \<Longrightarrow> clash (App Id N)"
| CExtn: "sig_normal M \<Longrightarrow> sig_normal L \<Longrightarrow> sig_normal N \<Longrightarrow> clash (App (Extn M x L) N)"
| CApp: "clash M \<Longrightarrow> sig_normal N \<Longrightarrow> clash (App M N)"
| CLam: "sig_normal M \<Longrightarrow> clash (Comp (Var x) (Lam y M))"
| CClo: "sig_normal M \<Longrightarrow> sig_normal L \<Longrightarrow> L \<noteq> Id \<Longrightarrow>
    clash (Comp (Var x) (Comp (Lam y M) L))"
| CComp: "clash M \<Longrightarrow> clash (Comp (Var x) M)"

definition cf_whnf :: "trm \<Rightarrow> bool" where
  "cf_whnf M \<longleftrightarrow> neu M \<or> val M"

subsection \<open>WHNF of each constructor\<close>

lemma WHNF_Var: "WHNF (Var x)"
  by (auto simp: normal_def wh_def elim: sig.cases beta_h.cases)

lemma WHNF_Id: "WHNF Id"
  by (auto simp: normal_def wh_def elim: sig.cases beta_h.cases)

lemma WHNF_Lam_iff: "WHNF (Lam x M) \<longleftrightarrow> sig_normal M"
proof
  assume "WHNF (Lam x M)"
  then show "sig_normal M"
    by (auto simp: normal_def wh_def intro: sig.Lam)
next
  assume "sig_normal M"
  then show "WHNF (Lam x M)"
    by (auto simp: normal_def wh_def elim: sig.cases beta_h.cases)
qed

lemma WHNF_Extn_iff: "WHNF (Extn M x L) \<longleftrightarrow> sig_normal M \<and> sig_normal L"
proof
  assume "WHNF (Extn M x L)"
  then show "sig_normal M \<and> sig_normal L"
    by (auto simp: normal_def wh_def intro: sig.ExtnL sig.ExtnR)
next
  assume "sig_normal M \<and> sig_normal L"
  then show "WHNF (Extn M x L)"
    by (auto simp: normal_def wh_def elim: sig.cases beta_h.cases)
qed

lemma WHNF_App_iff:
  "WHNF (App M N) \<longleftrightarrow>
     WHNF M \<and> sig_normal N \<and> (\<forall>x P. M \<noteq> Lam x P) \<and> (\<forall>x P L. M \<noteq> Comp (Lam x P) L)"
proof
  assume nf: "WHNF (App M N)"
  have "WHNF M"
    using nf by (auto simp: normal_def dest: wh_AppL)
  moreover have "sig_normal N"
    using nf by (auto simp: normal_def wh_def intro: sig.AppR)
  moreover have "M \<noteq> Lam x P" for x P
    using nf by (auto simp: normal_def wh_def intro: beta_h.Beta2)
  moreover have "M \<noteq> Comp (Lam x P) L" for x P L
    using nf by (auto simp: normal_def wh_def intro: beta_h.Beta1)
  ultimately show "WHNF M \<and> sig_normal N \<and> (\<forall>x P. M \<noteq> Lam x P) \<and> (\<forall>x P L. M \<noteq> Comp (Lam x P) L)"
    by blast
next
  assume a: "WHNF M \<and> sig_normal N \<and> (\<forall>x P. M \<noteq> Lam x P) \<and> (\<forall>x P L. M \<noteq> Comp (Lam x P) L)"
  show "WHNF (App M N)"
  proof (rule normalI)
    fix Q
    show "\<not> App M N \<rightarrow>\<^sub>w\<^sub>h Q"
    proof
      assume "App M N \<rightarrow>\<^sub>w\<^sub>h Q"
      then consider "App M N \<rightarrow>\<^sub>\<sigma> Q" | "App M N \<rightarrow>\<^sub>\<beta> Q"
        by (auto simp: wh_def)
      then show False
      proof cases
        case 1
        then show False
          using a by (cases rule: sig.cases) (auto simp: normal_def wh_def)
      next
        case 2
        then show False
          using a by (cases rule: beta_h.cases) (auto simp: normal_def wh_def)
      qed
    qed
  qed
qed

text \<open>No root \<open>\<sigma>\<close>-redex at a composition.\<close>

definition comp_root_ok :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "comp_root_ok M N \<longleftrightarrow>
     (\<forall>L K. M \<noteq> Comp L K) \<and> M \<noteq> Id \<and> N \<noteq> Id \<and> (\<forall>L x K. M \<noteq> Extn L x K) \<and>
     (\<forall>M1 M2. M \<noteq> App M1 M2) \<and> (\<forall>x L y K. \<not> (M = Var x \<and> N = Extn L y K))"

lemma WHNF_Comp_iff:
  "WHNF (Comp M N) \<longleftrightarrow>
     WHNF M \<and> sig_normal N \<and> comp_root_ok M N \<and> (\<forall>x. M = Var x \<longrightarrow> WHNF N)"
proof
  assume nf: "WHNF (Comp M N)"
  have "WHNF M"
    using nf by (auto simp: normal_def dest: wh_CompL)
  moreover have "sig_normal N"
    using nf by (auto simp: normal_def wh_def intro: sig.CompR)
  moreover have "comp_root_ok M N"
  proof -
    have r: "\<not> Comp M N \<rightarrow>\<^sub>\<sigma> Q" for Q
      using nf by (auto simp: normal_def wh_def)
    show ?thesis
      unfolding comp_root_ok_def
    proof (intro conjI allI notI)
      fix L K assume "M = Comp L K" then show False using r[of "Comp L (Comp K N)"] sig.Ass by blast
    next
      assume "M = Id" then show False using r[of N] sig.IdL by blast
    next
      assume "N = Id" then show False using r[of M] sig.IdR by blast
    next
      fix L x K assume "M = Extn L x K"
      then show False using r[of "Extn (Comp L N) x (Comp K N)"] sig.DExtn by blast
    next
      fix M1 M2 assume "M = App M1 M2"
      then show False using r[of "App (Comp M1 N) (Comp M2 N)"] sig.DApp by blast
    next
      fix x L y K assume e: "M = Var x \<and> N = Extn L y K"
      show False
      proof (cases "y = x")
        case True
        then show False using e r[of L] sig.VarRef by blast
      next
        case False
        then show False using e r[of "Comp (Var x) K"] sig.VarSkip by blast
      qed
    qed
  qed
  moreover have "WHNF N" if "M = Var x" for x
    using nf that by (auto simp: normal_def dest: wh_VarR)
  ultimately show "WHNF M \<and> sig_normal N \<and> comp_root_ok M N \<and> (\<forall>x. M = Var x \<longrightarrow> WHNF N)"
    by blast
next
  assume a: "WHNF M \<and> sig_normal N \<and> comp_root_ok M N \<and> (\<forall>x. M = Var x \<longrightarrow> WHNF N)"
  show "WHNF (Comp M N)"
  proof (rule normalI)
    fix Q
    show "\<not> Comp M N \<rightarrow>\<^sub>w\<^sub>h Q"
    proof
      assume "Comp M N \<rightarrow>\<^sub>w\<^sub>h Q"
      then consider "Comp M N \<rightarrow>\<^sub>\<sigma> Q" | "Comp M N \<rightarrow>\<^sub>\<beta> Q"
        by (auto simp: wh_def)
      then show False
      proof cases
        case 1
        then show False
          using a by (cases rule: sig.cases) (auto simp: normal_def wh_def comp_root_ok_def)
      next
        case 2
        then show False
          using a by (cases rule: beta_h.cases) (auto simp: normal_def wh_def)
      qed
    qed
  qed
qed

subsection \<open>Classification theorem\<close>

lemma neu_not_Id: "neu M \<Longrightarrow> M \<noteq> Id"
  by (auto elim: neu.cases)

lemma neu_not_Extn: "neu M \<Longrightarrow> M \<noteq> Extn L x K"
  by (auto elim: neu.cases)

lemma neu_not_Lam: "neu M \<Longrightarrow> M \<noteq> Lam x P"
  by (auto elim: neu.cases)

lemma neu_not_Clo: "neu M \<Longrightarrow> M \<noteq> Comp (Lam x P) L"
  by (auto elim: neu.cases)

lemma clash_not_Id: "clash M \<Longrightarrow> M \<noteq> Id"
  by (auto elim: clash.cases)

lemma clash_not_Extn: "clash M \<Longrightarrow> M \<noteq> Extn L x K"
  by (auto elim: clash.cases)

lemma clash_not_Lam: "clash M \<Longrightarrow> M \<noteq> Lam x P"
  by (auto elim: clash.cases)

lemma clash_not_Clo: "clash M \<Longrightarrow> M \<noteq> Comp (Lam x P) L"
  by (auto elim: clash.cases)

lemma val_Clo_WHNF:
  assumes "sig_normal P" "sig_normal L" "L \<noteq> Id"
  shows "WHNF (Comp (Lam x P) L)"
  using assms by (simp add: WHNF_Comp_iff WHNF_Lam_iff comp_root_ok_def)

lemma neu_WHNF: "neu M \<Longrightarrow> WHNF M"
proof (induction rule: neu.induct)
  case (NVar x)
  then show ?case by (rule WHNF_Var)
next
  case (NApp M N)
  then show ?case
    by (auto simp: WHNF_App_iff dest: neu_not_Lam neu_not_Clo)
next
  case (NComp M x)
  then show ?case
    by (auto simp: WHNF_Comp_iff comp_root_ok_def WHNF_Var WHNF_imp_sig_normal
        dest: neu_not_Id neu_not_Extn)
qed

lemma val_WHNF: "val M \<Longrightarrow> WHNF M"
  by (induction rule: val.induct)
     (auto simp: WHNF_Lam_iff WHNF_Extn_iff WHNF_Id intro: val_Clo_WHNF)

lemma clash_WHNF: "clash M \<Longrightarrow> WHNF M"
proof (induction rule: clash.induct)
  case (CId N)
  then show ?case by (simp add: WHNF_App_iff WHNF_Id)
next
  case (CExtn M L N x)
  then show ?case by (simp add: WHNF_App_iff WHNF_Extn_iff)
next
  case (CApp M N)
  then show ?case
    by (auto simp: WHNF_App_iff dest: clash_not_Lam clash_not_Clo)
next
  case (CLam M x y)
  then show ?case
    by (simp add: WHNF_Comp_iff comp_root_ok_def WHNF_Var WHNF_Lam_iff
        WHNF_imp_sig_normal[OF iffD2[OF WHNF_Lam_iff]])
next
  case (CClo M L x y)
  have "WHNF (Comp (Lam y M) L)"
    using CClo by (rule val_Clo_WHNF)
  then show ?case
    using CClo by (simp add: WHNF_Comp_iff comp_root_ok_def WHNF_Var WHNF_imp_sig_normal)
next
  case (CComp M x)
  then show ?case
    by (auto simp: WHNF_Comp_iff comp_root_ok_def WHNF_Var WHNF_imp_sig_normal
        dest: clash_not_Id clash_not_Extn)
qed

lemma WHNF_cases: "WHNF M \<Longrightarrow> neu M \<or> val M \<or> clash M"
proof (induction M)
  case (Var x)
  then show ?case by (auto intro: neu.intros)
next
  case (Lam x M)
  then show ?case by (auto simp: WHNF_Lam_iff intro: val.intros)
next
  case (App M N)
  then have hM: "WHNF M" and hN: "sig_normal N"
    and nL: "\<And>x P. M \<noteq> Lam x P" and nC: "\<And>x P L. M \<noteq> Comp (Lam x P) L"
    by (auto simp: WHNF_App_iff)
  from App.IH(1)[OF hM] consider "neu M" | "val M" | "clash M" by blast
  then show ?case
  proof cases
    case 1 then show ?thesis using hN by (auto intro: neu.intros)
  next
    case 2 then show ?thesis using hN nL nC
      by (cases rule: val.cases) (auto intro: clash.intros)
  next
    case 3 then show ?thesis using hN by (auto intro: clash.intros)
  qed
next
  case Id
  then show ?case by (auto intro: val.intros)
next
  case (Extn M x L)
  then show ?case by (auto simp: WHNF_Extn_iff intro: val.intros)
next
  case (Comp M N)
  then have hM: "WHNF M" and hN: "sig_normal N" and ok: "comp_root_ok M N"
    and hV: "\<And>x. M = Var x \<Longrightarrow> WHNF N"
    by (auto simp: WHNF_Comp_iff)
  show ?case
  proof (cases M)
    case (Var x)
    then have nN: "WHNF N" using hV by blast
    have nId: "N \<noteq> Id" and nE: "\<And>L y K. N \<noteq> Extn L y K"
      using ok Var by (auto simp: comp_root_ok_def)
    from Comp.IH(2)[OF nN] consider "neu N" | "val N" | "clash N" by blast
    then show ?thesis
    proof cases
      case 1 then show ?thesis using Var by (auto intro: neu.intros)
    next
      case 2 then show ?thesis using Var nId nE
        by (cases rule: val.cases) (auto intro: clash.intros)
    next
      case 3 then show ?thesis using Var by (auto intro: clash.intros)
    qed
  next
    case (Lam x P)
    then show ?thesis
      using hM hN ok by (auto simp: WHNF_Lam_iff comp_root_ok_def intro: val.intros)
  qed (use ok in \<open>auto simp: comp_root_ok_def\<close>)
qed

theorem WHNF_iff_classes: "WHNF M \<longleftrightarrow> neu M \<or> val M \<or> clash M"
  using WHNF_cases neu_WHNF val_WHNF clash_WHNF by blast

subsection \<open>Clash-free normalization predicates\<close>

definition CFWHN :: "trm \<Rightarrow> bool" where
  "CFWHN M \<longleftrightarrow> (\<exists>N. M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<and> WHNF N \<and> \<not> clash N)"

definition CFWHSN :: "trm \<Rightarrow> bool" where
  "CFWHSN M \<longleftrightarrow> WHSN M \<and> (\<forall>N. M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<longrightarrow> WHNF N \<longrightarrow> \<not> clash N)"

end
