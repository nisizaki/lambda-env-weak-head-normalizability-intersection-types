theory Examples
  imports Main_Results
begin

section \<open>Examples\<close>

text \<open>Variables are numbers: x = 0, y = 1, z = 1, w = 5 etc.\<close>

subsection \<open>Helper lemmas: \<open>sig\<close>-normality of concrete shapes\<close>

lemma sn_Var: "sig_normal (Var x)"
  by (auto simp: normal_def elim: sig.cases)

lemma sn_Id: "sig_normal Id"
  by (auto simp: normal_def elim: sig.cases)

lemma sn_Lam: "sig_normal M \<Longrightarrow> sig_normal (Lam x M)"
  by (auto simp: normal_def elim: sig.cases)

lemma sn_App: "sig_normal M \<Longrightarrow> sig_normal N \<Longrightarrow> sig_normal (App M N)"
  by (auto simp: normal_def elim: sig.cases)

lemma sn_Comp_VarVar: "sig_normal (Comp (Var x) (Var y))"
  by (auto simp: normal_def elim: sig.cases)

lemma Typ_expand: "M \<rightarrow>\<^sub>w\<^sub>h N \<Longrightarrow> Typ N \<Longrightarrow> Typ M"
  unfolding Typ_def using subject_expansion by blast

lemma Typ_expand_steps: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<Longrightarrow> Typ N \<Longrightarrow> Typ M"
  unfolding Typ_def using subject_expansion_steps by blast

subsection \<open>Row 1: \<open>(id/x)\<cdot>(\<lambda>y.id)\<close>\<close>

lemma ex1_val: "val (Extn Id 0 (Lam 1 Id))"
  by (rule VExtn[OF sn_Id sn_Lam[OF sn_Id]])

lemma ex1_WHNF: "WHNF (Extn Id 0 (Lam 1 Id))"
  by (rule val_WHNF[OF ex1_val])

lemma ex1_derivation: "Env [] True \<turnstile> Extn Id 0 (Lam 1 Id) : Env [(0, Om)] False"
  by (rule TExtn[OF TOm typ_env_om])

lemma ex1_Typ: "Typ (Extn Id 0 (Lam 1 Id))"
  using ex1_derivation unfolding Typ_def by force

subsection \<open>Row 2: \<open>(\<lambda>y.id)\<circ>(\<lambda>y.id)\<close>\<close>

lemma ex2_val: "val (Comp (Lam 1 Id) (Lam 1 Id))"
  by (rule VClo[OF sn_Id sn_Lam[OF sn_Id]]) simp

lemma ex2_derivation: "Env [] True \<turnstile> Comp (Lam 1 Id) (Lam 1 Id) : Arr Om Om"
  by (rule TComp[OF typ_env_om lam_typable[OF s_refl]])

lemma ex2_Typ: "Typ (Comp (Lam 1 Id) (Lam 1 Id))"
  using ex2_derivation unfolding Typ_def by force

subsection \<open>Row 3: \<open>id\<circ>(\<lambda>x.id)\<close>\<close>

lemma ex3_step: "Comp Id (Lam 0 Id) \<rightarrow>\<^sub>w\<^sub>h Lam 0 Id"
  by (rule sig_imp_wh[OF sig.IdL])

lemma ex3_not_WHNF: "\<not> WHNF (Comp Id (Lam 0 Id))"
  using ex3_step by (auto simp: normal_def)

lemma ex3_Typ: "Typ (Comp Id (Lam 0 Id))"
  by (rule Typ_expand[OF ex3_step val_Typ[OF VLam[OF sn_Id]]])

subsection \<open>Row 4: \<open>id N\<close>\<close>

lemma ex4_clash: "clash (App Id (Var 0))"
  by (rule CId[OF sn_Var])

lemma ex4_WHNF: "WHNF (App Id (Var 0))"
  by (rule clash_WHNF[OF ex4_clash])

lemma ex4_not_Typ: "\<not> Typ (App Id (Var 0))"
  by (rule clash_not_Typ[OF ex4_WHNF ex4_clash])

subsection \<open>Row 5: \<open>(x y)\<circ>w \<rightarrow> (x\<circ>w)(y\<circ>w)\<close>\<close>

lemma ex5_step:
  "Comp (App (Var 0) (Var 1)) (Var 5) \<rightarrow>\<^sub>w\<^sub>h App (Comp (Var 0) (Var 5)) (Comp (Var 1) (Var 5))"
  by (rule sig_imp_wh[OF sig.DApp])

lemma ex5_neu: "neu (App (Comp (Var 0) (Var 5)) (Comp (Var 1) (Var 5)))"
  by (rule NApp[OF NComp[OF NVar] sn_Comp_VarVar])

lemma ex5_Typ_reduct: "Typ (App (Comp (Var 0) (Var 5)) (Comp (Var 1) (Var 5)))"
  by (rule neu_Typ[OF ex5_neu])

lemma ex5_Typ: "Typ (Comp (App (Var 0) (Var 1)) (Var 5))"
  by (rule Typ_expand[OF ex5_step ex5_Typ_reduct])

subsection \<open>Row 6: \<open>x\<circ>(\<lambda>y.M)\<close>\<close>

lemma ex6_clash: "clash (Comp (Var 0) (Lam 1 (Var 1)))"
  by (rule CLam[OF sn_Var])

lemma ex6_not_Typ: "\<not> Typ (Comp (Var 0) (Lam 1 (Var 1)))"
  by (rule clash_not_Typ[OF clash_WHNF[OF ex6_clash] ex6_clash])

subsection \<open>Row 7: \<open>x\<circ>((\<lambda>z.(z/x)\<cdot>id) y)\<close> with x = 0, z = 1, y = 2\<close>

lemma ex7_reduction:
  "Comp (Var 0) (App (Lam 1 (Extn (Var 1) 0 Id)) (Var 2)) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Var 2"
proof -
  let ?E = "Extn (Var 2) 1 Id"
  have s1: "Comp (Var 0) (App (Lam 1 (Extn (Var 1) 0 Id)) (Var 2))
      \<rightarrow>\<^sub>w\<^sub>h Comp (Var 0) (Comp (Extn (Var 1) 0 Id) ?E)"
    by (rule wh_VarR[OF beta_h_imp_wh[OF beta_h.Beta2]])
  have s2: "Comp (Var 0) (Comp (Extn (Var 1) 0 Id) ?E)
      \<rightarrow>\<^sub>w\<^sub>h Comp (Var 0) (Extn (Comp (Var 1) ?E) 0 (Comp Id ?E))"
    by (rule wh_VarR[OF sig_imp_wh[OF sig.DExtn]])
  have s3: "Comp (Var 0) (Extn (Comp (Var 1) ?E) 0 (Comp Id ?E)) \<rightarrow>\<^sub>w\<^sub>h Comp (Var 1) ?E"
    by (rule sig_imp_wh[OF sig.VarRef])
  have s4: "Comp (Var 1) ?E \<rightarrow>\<^sub>w\<^sub>h Var 2"
    by (rule sig_imp_wh[OF sig.VarRef])
  show ?thesis
    using s1 s2 s3 s4 by (meson converse_rtranclp_into_rtranclp r_into_rtranclp)
qed

lemma ex7_Typ: "Typ (Comp (Var 0) (App (Lam 1 (Extn (Var 1) 0 Id)) (Var 2)))"
  by (rule Typ_expand_steps[OF ex7_reduction neu_Typ[OF NVar]])

subsection \<open>Row 8: \<open>x\<circ>((id/x)\<cdot>id) \<rightarrow> id\<close>\<close>

lemma ex8_step: "Comp (Var 0) (Extn Id 0 Id) \<rightarrow>\<^sub>w\<^sub>h Id"
  by (rule sig_imp_wh[OF sig.VarRef])

lemma ex8_Typ: "Typ (Comp (Var 0) (Extn Id 0 Id))"
  by (rule Typ_expand[OF ex8_step val_Typ[OF VId]])

subsection \<open>Rows 9--11: \<open>\<Omega>\<close>, \<open>\<lambda>x.\<Omega>\<close>, \<open>x \<Omega>\<close>\<close>

definition Omega :: trm where
  "Omega = App (Lam 0 (App (Var 0) (Var 0))) (Lam 0 (App (Var 0) (Var 0)))"

definition dw :: dB where "dw = DAbs (DApp (DVar 0) (DVar 0))"

lemma pure_Omega: "pure Omega"
  by (simp add: Omega_def)

lemma rb_Omega: "rb Omega DVar = DApp dw dw"
  by (simp add: Omega_def dw_def)

lemma dOmega_step: "DApp dw dw \<rightarrow>\<^sub>h DApp dw dw"
proof -
  have "DApp (DAbs (DApp (DVar 0) (DVar 0))) dw \<rightarrow>\<^sub>h (DApp (DVar 0) (DVar 0))[dw/0]"
    by (rule hbeta)
  then show ?thesis by (simp add: dw_def)
qed

lemma dOmega_reach: "hred\<^sup>*\<^sup>* (DApp dw dw) u \<Longrightarrow> u = DApp dw dw"
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  then have "y = DApp dw dw" by simp
  with step.hyps(2) have "DApp dw dw \<rightarrow>\<^sub>h z" by simp
  from hred_det[OF this dOmega_step] show ?case .
qed

lemma not_lam_WHN_Omega: "\<not> lam_WHN (rb Omega DVar)"
proof
  assume "lam_WHN (rb Omega DVar)"
  then obtain u where r: "hred\<^sup>*\<^sup>* (DApp dw dw) u" and n: "normal hred u"
    by (auto simp: lam_WHN_def rb_Omega)
  from dOmega_reach[OF r] n dOmega_step show False by (auto simp: normal_def)
qed

lemma ex9_not_CFWHN: "\<not> CFWHN Omega"
  using E1[OF pure_Omega] not_lam_WHN_Omega by blast

lemma ex9_not_Typ: "\<not> Typ Omega"
  using main_characterization ex9_not_CFWHN by blast

lemma sn_Omega: "sig_normal Omega"
  by (simp add: Omega_def sn_App sn_Lam sn_Var)

lemma ex10_val: "val (Lam 0 Omega)"
  by (rule VLam[OF sn_Omega])

lemma ex10_derivation: "Env [] True \<turnstile> Lam 0 Omega : Arr Om Om"
  by (rule lam_typable[OF s_refl])

lemma ex10_Typ: "Typ (Lam 0 Omega)"
  using ex10_derivation unfolding Typ_def by force

lemma ex11_neu: "neu (App (Var 0) Omega)"
  by (rule NApp[OF NVar sn_Omega])

lemma ex11_derivation: "Env [(0, Arr Om (TV 0))] True \<turnstile> App (Var 0) Omega : TV 0"
  by (rule TApp[OF TVar[OF s_refl] TOm]) simp

lemma ex11_Typ: "Typ (App (Var 0) Omega)"
  by (rule neu_Typ[OF ex11_neu])

end
