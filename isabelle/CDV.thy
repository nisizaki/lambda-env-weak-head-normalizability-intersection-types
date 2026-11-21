theory CDV
  imports Lambda
begin

section \<open>Classical intersection types (CDV style, with \<open>\<omega>\<close> and \<open>\<le>\<^sub>0\<close>) on de Bruijn terms\<close>

text \<open>
  Types, the subtyping relation \<open>\<le>\<^sub>0\<close> (without \<open>\<omega> \<le> \<omega> \<rightarrow> \<omega>\<close> and without arrow
  distributivity), essential types, and the typing relation.  Main result
  \<open>classical_WHN\<close>: a term is weak-head normalizable iff it has an essential type.
\<close>

datatype cty = CTV nat | COm | CArr cty cty | CInter cty cty

inductive csub :: "cty \<Rightarrow> cty \<Rightarrow> bool" (infix "\<le>\<^sub>0" 50) where
  cs_refl: "A \<le>\<^sub>0 A"
| cs_trans: "A \<le>\<^sub>0 B \<Longrightarrow> B \<le>\<^sub>0 C \<Longrightarrow> A \<le>\<^sub>0 C"
| cs_om: "A \<le>\<^sub>0 COm"
| cs_inter1: "CInter A B \<le>\<^sub>0 A"
| cs_inter2: "CInter A B \<le>\<^sub>0 B"
| cs_glb: "A \<le>\<^sub>0 B \<Longrightarrow> A \<le>\<^sub>0 C \<Longrightarrow> A \<le>\<^sub>0 CInter B C"
| cs_arr: "A' \<le>\<^sub>0 A \<Longrightarrow> B \<le>\<^sub>0 B' \<Longrightarrow> CArr A B \<le>\<^sub>0 CArr A' B'"

fun cess :: "cty \<Rightarrow> bool" where
  "cess (CTV a) = True"
| "cess COm = False"
| "cess (CArr A B) = True"
| "cess (CInter A B) = (cess A \<or> cess B)"

definition scons :: "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" (infixr "##" 65) where
  "scons a f = (\<lambda>i. case i of 0 \<Rightarrow> a | Suc j \<Rightarrow> f j)"

lemma scons_0 [simp]: "(a ## f) 0 = a"
  by (simp add: scons_def)

lemma scons_Suc [simp]: "(a ## f) (Suc j) = f j"
  by (simp add: scons_def)

lemma scons_comp_Suc [simp]: "(a ## f) \<circ> Suc = f"
  by (rule ext) simp

lemma scons_eta: "(f 0 ## (\<lambda>i. f (Suc i))) = f"
proof (rule ext)
  fix i show "(f 0 ## (\<lambda>i. f (Suc i))) i = f i" by (cases i) simp_all
qed

inductive cty_of :: "(nat \<Rightarrow> cty) \<Rightarrow> dB \<Rightarrow> cty \<Rightarrow> bool" ("_ \<turnstile>\<^sub>c _ : _" [50, 0, 50] 50) where
  cVar: "\<Gamma> i = A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c DVar i : A"
| cAbs: "(A ## \<Gamma>) \<turnstile>\<^sub>c t : B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c DAbs t : CArr A B"
| cApp: "\<Gamma> \<turnstile>\<^sub>c s : CArr A B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c u : A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c DApp s u : B"
| cOm: "\<Gamma> \<turnstile>\<^sub>c t : COm"
| cInter: "\<Gamma> \<turnstile>\<^sub>c t : A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c t : B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c t : CInter A B"
| cSub: "\<Gamma> \<turnstile>\<^sub>c t : A \<Longrightarrow> A \<le>\<^sub>0 B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c t : B"

subsection \<open>Renamings and simultaneous substitution\<close>

definition rup :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "rup r = (\<lambda>i. case i of 0 \<Rightarrow> 0 | Suc j \<Rightarrow> Suc (r j))"

lemma rup_0 [simp]: "rup r 0 = 0"
  by (simp add: rup_def)

lemma rup_Suc [simp]: "rup r (Suc j) = Suc (r j)"
  by (simp add: rup_def)

primrec dbren :: "dB \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> dB" where
  "dbren (DVar i) r = DVar (r i)"
| "dbren (DApp s t) r = DApp (dbren s r) (dbren t r)"
| "dbren (DAbs s) r = DAbs (dbren s (rup r))"

definition dbup :: "(nat \<Rightarrow> dB) \<Rightarrow> nat \<Rightarrow> dB" where
  "dbup s = (\<lambda>i. case i of 0 \<Rightarrow> DVar 0 | Suc j \<Rightarrow> dbren (s j) Suc)"

lemma dbup_0 [simp]: "dbup s 0 = DVar 0"
  by (simp add: dbup_def)

lemma dbup_Suc [simp]: "dbup s (Suc j) = dbren (s j) Suc"
  by (simp add: dbup_def)

primrec dbsub :: "dB \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> dB" where
  "dbsub (DVar i) s = s i"
| "dbsub (DApp t u) s = DApp (dbsub t s) (dbsub u s)"
| "dbsub (DAbs t) s = DAbs (dbsub t (dbup s))"

lemma rup_comp: "rup r' \<circ> rup r = rup (r' \<circ> r)"
proof (rule ext)
  fix i show "(rup r' \<circ> rup r) i = rup (r' \<circ> r) i" by (cases i) simp_all
qed

lemma ren_ren: "dbren (dbren t r) r' = dbren t (r' \<circ> r)"
  by (induct t arbitrary: r r') (simp_all add: rup_comp)

lemma dbup_rup: "dbup s \<circ> rup r = dbup (s \<circ> r)"
proof (rule ext)
  fix i show "(dbup s \<circ> rup r) i = dbup (s \<circ> r) i" by (cases i) simp_all
qed

lemma sub_ren: "dbsub (dbren t r) s = dbsub t (s \<circ> r)"
  by (induct t arbitrary: r s) (simp_all add: dbup_rup)

lemma ren_dbup: "(\<lambda>i. dbren (dbup s i) (rup r)) = dbup (\<lambda>i. dbren (s i) r)"
proof (rule ext)
  fix i show "dbren (dbup s i) (rup r) = dbup (\<lambda>i. dbren (s i) r) i"
    by (cases i) (simp_all add: ren_ren comp_def)
qed

lemma ren_sub: "dbren (dbsub t s) r = dbsub t (\<lambda>i. dbren (s i) r)"
  by (induct t arbitrary: r s) (simp_all add: ren_dbup)

lemma sub_dbup: "(\<lambda>i. dbsub (dbup s i) (dbup \<tau>)) = dbup (\<lambda>i. dbsub (s i) \<tau>)"
proof (rule ext)
  fix i show "dbsub (dbup s i) (dbup \<tau>) = dbup (\<lambda>i. dbsub (s i) \<tau>) i"
  proof (cases i)
    case 0 then show ?thesis by simp
  next
    case (Suc j)
    have "dbsub (dbren (s j) Suc) (dbup \<tau>) = dbsub (s j) (dbup \<tau> \<circ> Suc)"
      by (rule sub_ren)
    also have "dbup \<tau> \<circ> Suc = (\<lambda>i. dbren (\<tau> i) Suc)" by (rule ext) simp
    also have "dbsub (s j) (\<lambda>i. dbren (\<tau> i) Suc) = dbren (dbsub (s j) \<tau>) Suc"
      by (rule ren_sub[symmetric])
    finally show ?thesis using Suc by simp
  qed
qed

lemma sub_sub: "dbsub (dbsub t s) \<tau> = dbsub t (\<lambda>i. dbsub (s i) \<tau>)"
  by (induct t arbitrary: s \<tau>) (simp_all add: sub_dbup)

lemma dbup_var: "dbup DVar = DVar"
proof (rule ext)
  fix i show "dbup DVar i = DVar i" by (cases i) simp_all
qed

lemma sub_var [simp]: "dbsub t DVar = t"
  by (induct t) (simp_all add: dbup_var)

definition dl :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "dl k = (\<lambda>i. if i < k then i else Suc i)"

lemma dl_simp [simp]: "dl k i = (if i < k then i else Suc i)"
  by (simp add: dl_def)

lemma rup_dl: "rup (dl k) = dl (Suc k)"
proof (rule ext)
  fix i show "rup (dl k) i = dl (Suc k) i" by (cases i) simp_all
qed

lemma lift_ren: "lift t k = dbren t (dl k)"
  by (induct t arbitrary: k) (simp_all add: rup_dl)

lemma dl_0: "dl 0 = Suc"
  by (rule ext) simp

definition ins :: "nat \<Rightarrow> dB \<Rightarrow> nat \<Rightarrow> dB" where
  "ins k u i = (if i < k then DVar i else if i = k then u else DVar (i - 1))"

lemma dbup_ins: "dbup (ins k u) = ins (Suc k) (lift u 0)"
proof (rule ext)
  fix i show "dbup (ins k u) i = ins (Suc k) (lift u 0) i"
  proof (cases i)
    case 0 then show ?thesis by (simp add: ins_def)
  next
    case (Suc j)
    show ?thesis
    proof (cases "j < k")
      case True with Suc show ?thesis by (simp add: ins_def)
    next
      case False
      show ?thesis
      proof (cases "j = k")
        case True with Suc show ?thesis by (simp add: ins_def lift_ren dl_0)
      next
        case False with \<open>\<not> j < k\<close> Suc show ?thesis
          by (cases j) (simp_all add: ins_def)
      qed
    qed
  qed
qed

lemma subst_sub: "t[u/k] = dbsub t (ins k u)"
  by (induct t arbitrary: k u) (simp_all add: subst_Var dbup_ins ins_def)

lemma lift_subst0: "lift (s[t/0]) k = (lift s (Suc k))[lift t k/0]"
proof -
  have "lift (s[t/0]) k = dbren (dbsub s (ins 0 t)) (dl k)"
    by (simp add: subst_sub lift_ren)
  also have "\<dots> = dbsub s (\<lambda>i. dbren (ins 0 t i) (dl k))" by (rule ren_sub)
  also have "(\<lambda>i. dbren (ins 0 t i) (dl k)) = ins 0 (lift t k) \<circ> dl (Suc k)"
  proof (rule ext)
    fix i show "dbren (ins 0 t i) (dl k) = (ins 0 (lift t k) \<circ> dl (Suc k)) i"
      by (cases i) (simp_all add: ins_def lift_ren)
  qed
  also have "dbsub s (ins 0 (lift t k) \<circ> dl (Suc k)) = dbsub (dbren s (dl (Suc k))) (ins 0 (lift t k))"
    by (rule sub_ren[symmetric])
  also have "\<dots> = (lift s (Suc k))[lift t k/0]" by (simp add: subst_sub lift_ren)
  finally show ?thesis .
qed

lemma sub_up: "(dbsub t (dbup \<sigma>))[u/0] = dbsub t (u ## \<sigma>)"
proof -
  have "(dbsub t (dbup \<sigma>))[u/0] = dbsub (dbsub t (dbup \<sigma>)) (ins 0 u)"
    by (rule subst_sub)
  also have "\<dots> = dbsub t (\<lambda>i. dbsub (dbup \<sigma> i) (ins 0 u))" by (rule sub_sub)
  also have "(\<lambda>i. dbsub (dbup \<sigma> i) (ins 0 u)) = (u ## \<sigma>)"
  proof (rule ext)
    fix i show "dbsub (dbup \<sigma> i) (ins 0 u) = (u ## \<sigma>) i"
    proof (cases i)
      case 0 then show ?thesis by (simp add: ins_def)
    next
      case (Suc j)
      have "ins 0 u \<circ> Suc = DVar" by (rule ext) (simp add: ins_def)
      then show ?thesis using Suc by (simp add: sub_ren)
    qed
  qed
  finally show ?thesis .
qed

subsection \<open>Reduction, lifting, neutral terms\<close>

lemma hred_lift: "s \<rightarrow>\<^sub>h t \<Longrightarrow> lift s k \<rightarrow>\<^sub>h lift t k"
proof (induction arbitrary: k rule: hred.induct)
  case (hbeta s t)
  show ?case using hred.hbeta[of "lift s (Suc k)" "lift t k"] by (simp add: lift_subst0)
next
  case (happ s s' t)
  then show ?case by (simp add: hred.happ)
qed

lemma hred_lift_star: "hred\<^sup>*\<^sup>* s t \<Longrightarrow> hred\<^sup>*\<^sup>* (lift s k) (lift t k)"
  by (induction rule: rtranclp.induct) (auto intro: hred_lift rtranclp.rtrancl_into_rtrancl)

inductive neutral :: "dB \<Rightarrow> bool" where
  nvar: "neutral (DVar i)"
| napp: "neutral s \<Longrightarrow> neutral (DApp s u)"

lemma neutral_lift: "neutral n \<Longrightarrow> neutral (lift n k)"
  by (induction rule: neutral.induct) (simp_all add: neutral.intros)

lemma hred_app_inv: "DApp s u \<rightarrow>\<^sub>h b \<Longrightarrow> (\<exists>s0. s = DAbs s0) \<or> (\<exists>s'. s \<rightarrow>\<^sub>h s')"
  by (auto elim: hred.cases)

lemma neutral_normal: "neutral n \<Longrightarrow> normal hred n"
proof (induction rule: neutral.induct)
  case (nvar i)
  show ?case by (rule normalI) (auto elim: hred.cases)
next
  case (napp s u)
  show ?case
  proof (rule normalI)
    fix b
    show "\<not> DApp s u \<rightarrow>\<^sub>h b"
    proof (rule notI)
    assume h: "DApp s u \<rightarrow>\<^sub>h b"
    from hred_app_inv[OF h] have "(\<exists>s0. s = DAbs s0) \<or> (\<exists>s'. s \<rightarrow>\<^sub>h s')" .
    moreover have "\<not> (\<exists>s0. s = DAbs s0)" using napp.hyps by (auto elim: neutral.cases)
    moreover have "\<not> (\<exists>s'. s \<rightarrow>\<^sub>h s')" using napp.IH by (auto simp: normal_def)
    ultimately show False by blast
    qed
  qed
qed

lemma normal_shape: "normal hred u \<Longrightarrow> (\<exists>s. u = DAbs s) \<or> neutral u"
proof (induction u)
  case (DVar i) then show ?case by (simp add: neutral.nvar)
next
  case (DApp s t)
  have ns: "normal hred s"
  proof (rule normalI)
    fix b
    show "\<not> s \<rightarrow>\<^sub>h b"
    proof (rule notI)
    assume h: "s \<rightarrow>\<^sub>h b"
    have h2: "DApp s t \<rightarrow>\<^sub>h DApp b t" by (rule hred.happ[OF h])
    have "\<not> (DApp s t \<rightarrow>\<^sub>h DApp b t)" by (rule normalD[OF DApp.prems])
    with h2 show False by blast
    qed
  qed
  from DApp.IH(1)[OF ns] show ?case
  proof (rule disjE)
    assume "\<exists>x. s = DAbs x"
    then obtain x where "s = DAbs x" by blast
    then have h2: "DApp s t \<rightarrow>\<^sub>h subst x t 0" by (simp add: hred.hbeta)
    have "\<not> (DApp s t \<rightarrow>\<^sub>h subst x t 0)" by (rule normalD[OF DApp.prems])
    with h2 show ?thesis by blast
  next
    assume "neutral s" then show ?thesis by (simp add: neutral.napp)
  qed
next
  case (DAbs s) then show ?case by simp
qed

lemma whn_abs: "lam_WHN (DAbs s)"
  unfolding lam_WHN_def using DAbs_no_step by (auto intro!: exI[of _ "DAbs s"] normalI)

lemma whn_neutral: "neutral n \<Longrightarrow> lam_WHN n"
  unfolding lam_WHN_def using neutral_normal by blast

lemma whn_lift: "lam_WHN t \<Longrightarrow> lam_WHN (lift t k)"
proof -
  assume "lam_WHN t"
  then obtain u where r: "hred\<^sup>*\<^sup>* t u" and nf: "normal hred u" by (auto simp: lam_WHN_def)
  from normal_shape[OF nf] have "normal hred (lift u k)"
  proof
    assume "\<exists>s. u = DAbs s"
    then obtain s where "u = DAbs s" by blast
    then show ?thesis by (auto intro!: normalI dest: DAbs_no_step)
  next
    assume "neutral u"
    then show ?thesis by (intro neutral_normal neutral_lift)
  qed
  with hred_lift_star[OF r] show ?thesis unfolding lam_WHN_def by blast
qed

lemma whn_exp: "t \<rightarrow>\<^sub>h t' \<Longrightarrow> lam_WHN t' \<Longrightarrow> lam_WHN t"
  unfolding lam_WHN_def by (blast intro: converse_rtranclp_into_rtranclp)

primrec liftl :: "nat list \<Rightarrow> dB \<Rightarrow> dB" where
  "liftl [] t = t"
| "liftl (k # ks) t = liftl ks (lift t k)"

lemma liftl_hred: "s \<rightarrow>\<^sub>h t \<Longrightarrow> liftl ks s \<rightarrow>\<^sub>h liftl ks t"
  by (induct ks arbitrary: s t) (simp_all add: hred_lift)

lemma liftl_neutral: "neutral n \<Longrightarrow> neutral (liftl ks n)"
  by (induct ks arbitrary: n) (simp_all add: neutral_lift)

lemma liftl_sub: "liftl ks (dbsub t s) = dbsub t (\<lambda>i. liftl ks (s i))"
proof (induct ks arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons k ks)
  have "liftl (k # ks) (dbsub t s) = liftl ks (dbsub t (\<lambda>i. lift (s i) k))"
    by (simp add: lift_ren ren_sub)
  also have "\<dots> = dbsub t (\<lambda>i. liftl ks (lift (s i) k))" by (rule Cons.hyps)
  finally show ?case by simp
qed

subsection \<open>Realizability semantics\<close>

primrec csem :: "cty \<Rightarrow> dB set" where
  "csem (CTV a) = {t. lam_WHN t}"
| "csem COm = UNIV"
| "csem (CArr A B) =
    {t. lam_WHN t \<and> (\<forall>ks u. u \<in> csem A \<longrightarrow> DApp (liftl ks t) u \<in> csem B)}"
| "csem (CInter A B) = csem A \<inter> csem B"

lemma csem_lift: "t \<in> csem A \<Longrightarrow> lift t k \<in> csem A"
proof (induction A arbitrary: t k)
  case (CTV a) then show ?case by (simp add: whn_lift)
next
  case COm then show ?case by simp
next
  case (CArr A B)
  have w: "lam_WHN (lift t k)" using CArr.prems by (simp add: whn_lift)
  have "\<forall>ks u. u \<in> csem A \<longrightarrow> DApp (liftl ks (lift t k)) u \<in> csem B"
  proof (intro allI impI)
    fix ks u assume "u \<in> csem A"
    from CArr.prems have h: "\<forall>ks u. u \<in> csem A \<longrightarrow> DApp (liftl ks t) u \<in> csem B" by simp
    with \<open>u \<in> csem A\<close> have "DApp (liftl (k # ks) t) u \<in> csem B" by blast
    then show "DApp (liftl ks (lift t k)) u \<in> csem B" by simp
  qed
  with w show ?case by simp
next
  case (CInter A B) then show ?case by simp
qed

lemma csem_liftl: "t \<in> csem A \<Longrightarrow> liftl ks t \<in> csem A"
  by (induct ks arbitrary: t) (simp_all add: csem_lift)

lemma csem_neutral: "neutral n \<Longrightarrow> n \<in> csem A"
proof (induction A arbitrary: n)
  case (CTV a) then show ?case by (simp add: whn_neutral)
next
  case COm then show ?case by simp
next
  case (CArr A B)
  have "\<forall>ks u. u \<in> csem A \<longrightarrow> DApp (liftl ks n) u \<in> csem B"
  proof (intro allI impI)
    fix ks u
    from CArr.prems have "neutral (DApp (liftl ks n) u)"
      by (simp add: liftl_neutral neutral.napp)
    then show "DApp (liftl ks n) u \<in> csem B" by (rule CArr.IH(2))
  qed
  with CArr.prems show ?case by (simp add: whn_neutral)
next
  case (CInter A B) then show ?case by simp
qed

lemma csem_exp: "t \<rightarrow>\<^sub>h t' \<Longrightarrow> t' \<in> csem A \<Longrightarrow> t \<in> csem A"
proof (induction A arbitrary: t t')
  case (CTV a) then show ?case by (simp add: whn_exp)
next
  case COm then show ?case by simp
next
  case (CArr A B)
  from CArr.prems have w: "lam_WHN t'" and h: "\<forall>ks u. u \<in> csem A \<longrightarrow> DApp (liftl ks t') u \<in> csem B"
    by simp_all
  have "\<forall>ks u. u \<in> csem A \<longrightarrow> DApp (liftl ks t) u \<in> csem B"
  proof (intro allI impI)
    fix ks u assume "u \<in> csem A"
    with h have m: "DApp (liftl ks t') u \<in> csem B" by blast
    from CArr.prems(1) have st: "DApp (liftl ks t) u \<rightarrow>\<^sub>h DApp (liftl ks t') u"
      by (intro hred.happ liftl_hred)
    from CArr.IH(2)[OF st m] show "DApp (liftl ks t) u \<in> csem B" .
  qed
  moreover from CArr.prems(1) w have "lam_WHN t" by (rule whn_exp)
  ultimately show ?case by simp
next
  case (CInter A B) then show ?case by simp
qed

lemma csem_sub: "A \<le>\<^sub>0 B \<Longrightarrow> csem A \<subseteq> csem B"
proof (induction rule: csub.induct)
  case (cs_arr A' A B B')
  show ?case
  proof
    fix t assume "t \<in> csem (CArr A B)"
    then have w: "lam_WHN t" and h: "\<forall>ks u. u \<in> csem A \<longrightarrow> DApp (liftl ks t) u \<in> csem B"
      by simp_all
    have "\<forall>ks u. u \<in> csem A' \<longrightarrow> DApp (liftl ks t) u \<in> csem B'"
    proof (intro allI impI)
      fix ks u assume "u \<in> csem A'"
      with cs_arr.IH(1) have "u \<in> csem A" by blast
      with h have "DApp (liftl ks t) u \<in> csem B" by blast
      with cs_arr.IH(2) show "DApp (liftl ks t) u \<in> csem B'" by blast
    qed
    with w show "t \<in> csem (CArr A' B')" by simp
  qed
qed auto

lemma csem_ess: "cess A \<Longrightarrow> csem A \<subseteq> {t. lam_WHN t}"
  by (induct A) auto

lemma fund:
  assumes "\<Gamma> \<turnstile>\<^sub>c t : A"
  shows "\<forall>\<sigma>. (\<forall>i. \<sigma> i \<in> csem (\<Gamma> i)) \<longrightarrow> dbsub t \<sigma> \<in> csem A"
using assms
proof (induction rule: cty_of.induct)
  case (cVar \<Gamma> i A)
  then show ?case by auto
next
  case (cAbs A \<Gamma> t B)
  show ?case
  proof (intro allI impI)
    fix \<sigma> assume h: "\<forall>i. \<sigma> i \<in> csem (\<Gamma> i)"
    have "\<forall>ks u. u \<in> csem A \<longrightarrow> DApp (liftl ks (dbsub (DAbs t) \<sigma>)) u \<in> csem B"
    proof (intro allI impI)
      fix ks u assume hu: "u \<in> csem A"
      let ?s = "\<lambda>i. liftl ks (\<sigma> i)"
      have e: "liftl ks (dbsub (DAbs t) \<sigma>) = DAbs (dbsub t (dbup ?s))"
      proof -
        have "liftl ks (dbsub (DAbs t) \<sigma>) = dbsub (DAbs t) ?s" by (rule liftl_sub)
        also have "\<dots> = DAbs (dbsub t (dbup ?s))" by simp
        finally show ?thesis .
      qed
      have hs: "\<forall>i. (u ## ?s) i \<in> csem ((A ## \<Gamma>) i)"
      proof
        fix i show "(u ## ?s) i \<in> csem ((A ## \<Gamma>) i)"
          using hu h csem_liftl by (cases i) auto
      qed
      from cAbs.IH hs have "dbsub t (u ## ?s) \<in> csem B" by blast
      then have m: "(dbsub t (dbup ?s))[u/0] \<in> csem B" by (simp add: sub_up)
      have st: "DApp (DAbs (dbsub t (dbup ?s))) u \<rightarrow>\<^sub>h (dbsub t (dbup ?s))[u/0]"
        by (rule hred.hbeta)
      from csem_exp[OF st m] have "DApp (DAbs (dbsub t (dbup ?s))) u \<in> csem B" .
      then show "DApp (liftl ks (dbsub (DAbs t) \<sigma>)) u \<in> csem B" by (simp only: e)
    qed
    moreover have "lam_WHN (dbsub (DAbs t) \<sigma>)" by (simp add: whn_abs)
    ultimately show "dbsub (DAbs t) \<sigma> \<in> csem (CArr A B)" by simp
  qed
next
  case (cApp \<Gamma> s A B u)
  show ?case
  proof (intro allI impI)
    fix \<sigma> assume h: "\<forall>i. \<sigma> i \<in> csem (\<Gamma> i)"
    from cApp.IH(1) h have "dbsub s \<sigma> \<in> csem (CArr A B)" by blast
    then have f: "\<forall>ks u'. u' \<in> csem A \<longrightarrow> DApp (liftl ks (dbsub s \<sigma>)) u' \<in> csem B" by simp
    from cApp.IH(2) h have "dbsub u \<sigma> \<in> csem A" by blast
    with f have "DApp (liftl [] (dbsub s \<sigma>)) (dbsub u \<sigma>) \<in> csem B" by blast
    then show "dbsub (DApp s u) \<sigma> \<in> csem B" by simp
  qed
next
  case (cOm \<Gamma> t) then show ?case by simp
next
  case (cInter \<Gamma> t A B) then show ?case by auto
next
  case (cSub \<Gamma> t A B)
  then show ?case using csem_sub by blast
qed

theorem classical_sound:
  assumes "\<Gamma> \<turnstile>\<^sub>c t : A" and "cess A"
  shows "lam_WHN t"
proof -
  have "\<forall>i. DVar i \<in> csem (\<Gamma> i)" by (simp add: csem_neutral neutral.nvar)
  with fund[OF assms(1)] have "dbsub t DVar \<in> csem A" by blast
  then have "t \<in> csem A" by simp
  with csem_ess[OF assms(2)] show ?thesis by blast
qed

subsection \<open>Completeness: typing lemmas and subject expansion\<close>

lemma gen_var_aux: "\<Gamma> \<turnstile>\<^sub>c r : C \<Longrightarrow> \<forall>i. r = DVar i \<longrightarrow> \<Gamma> i \<le>\<^sub>0 C"
proof (induction rule: cty_of.induct)
  case (cVar \<Gamma> i A) then show ?case by (auto intro: csub.cs_refl)
next
  case (cAbs A \<Gamma> t B) then show ?case by simp
next
  case (cApp \<Gamma> s A B u) then show ?case by simp
next
  case (cOm \<Gamma> t) then show ?case by (auto intro: csub.cs_om)
next
  case (cInter \<Gamma> t A B) then show ?case by (auto intro: csub.cs_glb)
next
  case (cSub \<Gamma> t A B) then show ?case by (auto intro: csub.cs_trans)
qed

lemma gen_var: "\<Gamma> \<turnstile>\<^sub>c DVar i : C \<Longrightarrow> \<Gamma> i \<le>\<^sub>0 C"
  using gen_var_aux by blast

lemma ctx_mono_aux:
  assumes "\<Gamma> \<turnstile>\<^sub>c t : A"
  shows "\<forall>\<Gamma>'. (\<forall>i. \<Gamma>' i \<le>\<^sub>0 \<Gamma> i) \<longrightarrow> \<Gamma>' \<turnstile>\<^sub>c t : A"
using assms
proof (induction rule: cty_of.induct)
  case (cVar \<Gamma> i A)
  show ?case
  proof (intro allI impI)
    fix \<Gamma>' assume h: "\<forall>i. \<Gamma>' i \<le>\<^sub>0 \<Gamma> i"
    have "\<Gamma>' \<turnstile>\<^sub>c DVar i : \<Gamma>' i" by (rule cty_of.cVar) simp
    moreover from h cVar.hyps have "\<Gamma>' i \<le>\<^sub>0 A" by blast
    ultimately show "\<Gamma>' \<turnstile>\<^sub>c DVar i : A" by (rule cty_of.cSub)
  qed
next
  case (cAbs A \<Gamma> t B)
  show ?case
  proof (intro allI impI)
    fix \<Gamma>' assume h: "\<forall>i. \<Gamma>' i \<le>\<^sub>0 \<Gamma> i"
    have "\<forall>i. (A ## \<Gamma>') i \<le>\<^sub>0 (A ## \<Gamma>) i"
    proof
      fix i show "(A ## \<Gamma>') i \<le>\<^sub>0 (A ## \<Gamma>) i" using h by (cases i) (simp_all add: csub.cs_refl)
    qed
    with cAbs.IH have "(A ## \<Gamma>') \<turnstile>\<^sub>c t : B" by blast
    then show "\<Gamma>' \<turnstile>\<^sub>c DAbs t : CArr A B" by (rule cty_of.cAbs)
  qed
next
  case (cApp \<Gamma> s A B u)
  then show ?case by (blast intro: cty_of.cApp)
next
  case (cOm \<Gamma> t) then show ?case by (blast intro: cty_of.cOm)
next
  case (cInter \<Gamma> t A B) then show ?case by (blast intro: cty_of.cInter)
next
  case (cSub \<Gamma> t A B) then show ?case by (blast intro: cty_of.cSub)
qed

lemma ctx_mono: "\<Gamma> \<turnstile>\<^sub>c t : A \<Longrightarrow> (\<And>i. \<Gamma>' i \<le>\<^sub>0 \<Gamma> i) \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>c t : A"
  using ctx_mono_aux by blast

lemma strengthen_aux:
  assumes "\<Gamma> \<turnstile>\<^sub>c r : A"
  shows "\<forall>\<rho> t. r = dbren t \<rho> \<longrightarrow> (\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>c t : A"
using assms
proof (induction rule: cty_of.induct)
  case (cVar \<Gamma> i A)
  show ?case
  proof (intro allI impI)
    fix \<rho> t assume e: "DVar i = dbren t \<rho>"
    then obtain j where "t = DVar j" "\<rho> j = i" by (cases t) auto
    with cVar.hyps show "(\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>c t : A" by (auto intro: cty_of.cVar)
  qed
next
  case (cAbs A \<Gamma> t B)
  show ?case
  proof (intro allI impI)
    fix \<rho> s assume e: "DAbs t = dbren s \<rho>"
    then obtain s1 where s: "s = DAbs s1" and t: "t = dbren s1 (rup \<rho>)" by (cases s) auto
    from cAbs.IH t have "((A ## \<Gamma>) \<circ> rup \<rho>) \<turnstile>\<^sub>c s1 : B" by blast
    moreover have "(A ## \<Gamma>) \<circ> rup \<rho> = A ## (\<Gamma> \<circ> \<rho>)"
    proof (rule ext)
      fix i show "((A ## \<Gamma>) \<circ> rup \<rho>) i = (A ## (\<Gamma> \<circ> \<rho>)) i" by (cases i) simp_all
    qed
    ultimately have "(A ## (\<Gamma> \<circ> \<rho>)) \<turnstile>\<^sub>c s1 : B" by simp
    then show "(\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>c s : CArr A B" using s by (simp add: cty_of.cAbs)
  qed
next
  case (cApp \<Gamma> p A B q)
  show ?case
  proof (intro allI impI)
    fix \<rho> s assume e: "DApp p q = dbren s \<rho>"
    then obtain s1 s2 where s: "s = DApp s1 s2" and p: "p = dbren s1 \<rho>" and q: "q = dbren s2 \<rho>"
      by (cases s) auto
    from cApp.IH(1) p have "(\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>c s1 : CArr A B" by blast
    moreover from cApp.IH(2) q have "(\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>c s2 : A" by blast
    ultimately show "(\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>c s : B" using s by (simp add: cty_of.cApp)
  qed
next
  case (cOm \<Gamma> t) then show ?case by (blast intro: cty_of.cOm)
next
  case (cInter \<Gamma> t A B) then show ?case by (blast intro: cty_of.cInter)
next
  case (cSub \<Gamma> t A B) then show ?case by (blast intro: cty_of.cSub)
qed

lemma strengthen: "\<Gamma> \<turnstile>\<^sub>c dbren t \<rho> : A \<Longrightarrow> (\<Gamma> \<circ> \<rho>) \<turnstile>\<^sub>c t : A"
  using strengthen_aux by blast

lemma expand_var:
  assumes "\<Gamma> \<turnstile>\<^sub>c \<sigma> j : A"
  shows "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>c DVar j : A"
proof -
  let ?D = "\<lambda>k. if k = j then A else COm"
  have "\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : ?D i"
  proof
    fix i show "\<Gamma> \<turnstile>\<^sub>c \<sigma> i : ?D i" by (cases "i = j") (simp_all add: assms cty_of.cOm)
  qed
  moreover have "?D \<turnstile>\<^sub>c DVar j : A" by (rule cty_of.cVar) simp
  ultimately show ?thesis by (rule exI[of _ ?D, OF conjI])
qed

lemma expand_aux:
  assumes "\<Gamma> \<turnstile>\<^sub>c r : A"
  shows "\<forall>s \<sigma>. r = dbsub s \<sigma> \<longrightarrow> (\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>c s : A)"
using assms
proof (induction rule: cty_of.induct)
  case (cVar \<Gamma> i A)
  show ?case
  proof (intro allI impI)
    fix s \<sigma> assume e: "DVar i = dbsub s \<sigma>"
    then obtain j where sj: "s = DVar j" by (cases s) auto
    with e have "\<sigma> j = DVar i" by simp
    then have "\<Gamma> \<turnstile>\<^sub>c \<sigma> j : A" using cVar.hyps by (auto intro: cty_of.cVar)
    then show "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>c s : A" using sj expand_var by blast
  qed
next
  case (cAbs A \<Gamma> t B)
  show ?case
  proof (intro allI impI)
    fix s \<sigma> assume e: "DAbs t = dbsub s \<sigma>"
    show "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>c s : CArr A B"
    proof (cases s)
      case (DVar j)
      with e have "\<sigma> j = DAbs t" by simp
      then have "\<Gamma> \<turnstile>\<^sub>c \<sigma> j : CArr A B" using cAbs.hyps by (auto intro: cty_of.cAbs)
      then show ?thesis using DVar expand_var by blast
    next
      case (DApp p q) with e show ?thesis by simp
    next
      case (DAbs s1)
      with e have e1: "t = dbsub s1 (dbup \<sigma>)" by simp
      from cAbs.IH e1 obtain \<Delta>' where
        h1: "\<forall>i. (A ## \<Gamma>) \<turnstile>\<^sub>c dbup \<sigma> i : \<Delta>' i" and h2: "\<Delta>' \<turnstile>\<^sub>c s1 : B" by blast
      let ?C = "\<Delta>' 0"
      let ?D = "\<lambda>i. \<Delta>' (Suc i)"
      have h0: "(A ## \<Gamma>) \<turnstile>\<^sub>c DVar 0 : ?C" using h1 by (metis dbup_0)
      then have "(A ## \<Gamma>) 0 \<le>\<^sub>0 ?C" by (rule gen_var)
      then have AC: "A \<le>\<^sub>0 ?C" by simp
      have eta: "(?C ## ?D) = \<Delta>'" by (rule scons_eta)
      from h2 eta have "(?C ## ?D) \<turnstile>\<^sub>c s1 : B" by simp
      then have "?D \<turnstile>\<^sub>c DAbs s1 : CArr ?C B" by (rule cty_of.cAbs)
      then have d: "?D \<turnstile>\<^sub>c DAbs s1 : CArr A B"
        by (rule cty_of.cSub) (rule csub.cs_arr[OF AC csub.cs_refl])
      have "\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : ?D i"
      proof
        fix i
        have "(A ## \<Gamma>) \<turnstile>\<^sub>c dbup \<sigma> (Suc i) : \<Delta>' (Suc i)" using h1 by blast
        then have "(A ## \<Gamma>) \<turnstile>\<^sub>c dbren (\<sigma> i) Suc : ?D i" by simp
        then have "((A ## \<Gamma>) \<circ> Suc) \<turnstile>\<^sub>c \<sigma> i : ?D i" by (rule strengthen)
        then show "\<Gamma> \<turnstile>\<^sub>c \<sigma> i : ?D i" by simp
      qed
      have hs: "\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : ?D i" by fact
      show ?thesis unfolding DAbs by (rule exI[of _ ?D]) (rule conjI[OF hs d])
    qed
  qed
next
  case (cApp \<Gamma> p A B q)
  show ?case
  proof (intro allI impI)
    fix s \<sigma> assume e: "DApp p q = dbsub s \<sigma>"
    show "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>c s : B"
    proof (cases s)
      case (DVar j)
      with e have "\<sigma> j = DApp p q" by simp
      then have "\<Gamma> \<turnstile>\<^sub>c \<sigma> j : B" using cApp.hyps by (auto intro: cty_of.cApp)
      then show ?thesis using DVar expand_var by blast
    next
      case (DAbs s1) with e show ?thesis by simp
    next
      case (DApp s1 s2)
      with e have e1: "p = dbsub s1 \<sigma>" and e2: "q = dbsub s2 \<sigma>" by simp_all
      from cApp.IH(1) e1 obtain \<Delta>1 where
        a1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta>1 i" and a2: "\<Delta>1 \<turnstile>\<^sub>c s1 : CArr A B" by blast
      from cApp.IH(2) e2 obtain \<Delta>2 where
        b1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta>2 i" and b2: "\<Delta>2 \<turnstile>\<^sub>c s2 : A" by blast
      let ?D = "\<lambda>i. CInter (\<Delta>1 i) (\<Delta>2 i)"
      have hs: "\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : ?D i" using a1 b1 by (blast intro: cty_of.cInter)
      have d1: "?D \<turnstile>\<^sub>c s1 : CArr A B" using a2 by (rule ctx_mono) (rule csub.cs_inter1)
      have d2: "?D \<turnstile>\<^sub>c s2 : A" using b2 by (rule ctx_mono) (rule csub.cs_inter2)
      from d1 d2 have d: "?D \<turnstile>\<^sub>c DApp s1 s2 : B" by (rule cty_of.cApp)
      show ?thesis unfolding DApp by (rule exI[of _ ?D]) (rule conjI[OF hs d])
    qed
  qed
next
  case (cOm \<Gamma> t)
  show ?case
  proof (intro allI impI)
    fix s \<sigma> assume "t = dbsub s \<sigma>"
    have h1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : (\<lambda>_. COm) i" by (simp add: cty_of.cOm)
    have h2: "(\<lambda>_. COm) \<turnstile>\<^sub>c s : COm" by (rule cty_of.cOm)
    show "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>c s : COm"
      by (rule exI[of _ "\<lambda>_. COm"]) (rule conjI[OF h1 h2])
  qed
next
  case (cInter \<Gamma> t A B)
  show ?case
  proof (intro allI impI)
    fix s \<sigma> assume e: "t = dbsub s \<sigma>"
    from cInter.IH(1) e obtain \<Delta>1 where
      a1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta>1 i" and a2: "\<Delta>1 \<turnstile>\<^sub>c s : A" by blast
    from cInter.IH(2) e obtain \<Delta>2 where
      b1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta>2 i" and b2: "\<Delta>2 \<turnstile>\<^sub>c s : B" by blast
    let ?D = "\<lambda>i. CInter (\<Delta>1 i) (\<Delta>2 i)"
    have hs: "\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : ?D i" using a1 b1 by (blast intro: cty_of.cInter)
    have d1: "?D \<turnstile>\<^sub>c s : A" using a2 by (rule ctx_mono) (rule csub.cs_inter1)
    have d2: "?D \<turnstile>\<^sub>c s : B" using b2 by (rule ctx_mono) (rule csub.cs_inter2)
    from d1 d2 have d: "?D \<turnstile>\<^sub>c s : CInter A B" by (rule cty_of.cInter)
    show "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>c s : CInter A B"
      by (rule exI[of _ ?D]) (rule conjI[OF hs d])
  qed
next
  case (cSub \<Gamma> t A B)
  show ?case
  proof (intro allI impI)
    fix s \<sigma> assume e: "t = dbsub s \<sigma>"
    from cSub.IH e obtain \<Delta> where
      a1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta> i" and a2: "\<Delta> \<turnstile>\<^sub>c s : A" by blast
    from a2 cSub.hyps have d: "\<Delta> \<turnstile>\<^sub>c s : B" by (blast intro: cty_of.cSub)
    show "\<exists>\<Delta>. (\<forall>i. \<Gamma> \<turnstile>\<^sub>c \<sigma> i : \<Delta> i) \<and> \<Delta> \<turnstile>\<^sub>c s : B"
      by (rule exI[of _ \<Delta>]) (rule conjI[OF a1 d])
  qed
qed

lemma expand_beta:
  assumes "\<Gamma> \<turnstile>\<^sub>c subst s u 0 : A"
  shows "\<Gamma> \<turnstile>\<^sub>c DApp (DAbs s) u : A"
proof -
  from assms have h: "\<Gamma> \<turnstile>\<^sub>c dbsub s (ins 0 u) : A" by (simp add: subst_sub)
  from expand_aux[OF h] obtain \<Delta> where
    h1: "\<forall>i. \<Gamma> \<turnstile>\<^sub>c ins 0 u i : \<Delta> i" and h2: "\<Delta> \<turnstile>\<^sub>c s : A" by blast
  have h3: "\<forall>i. \<Gamma> i \<le>\<^sub>0 \<Delta> (Suc i)"
  proof
    fix i
    have "\<Gamma> \<turnstile>\<^sub>c ins 0 u (Suc i) : \<Delta> (Suc i)" using h1 by blast
    then have "\<Gamma> \<turnstile>\<^sub>c DVar i : \<Delta> (Suc i)" by (simp add: ins_def)
    then show "\<Gamma> i \<le>\<^sub>0 \<Delta> (Suc i)" by (rule gen_var)
  qed
  have "(\<Delta> 0 ## \<Gamma>) \<turnstile>\<^sub>c s : A"
  proof (rule ctx_mono[OF h2])
    fix i show "(\<Delta> 0 ## \<Gamma>) i \<le>\<^sub>0 \<Delta> i" using h3 by (cases i) (simp_all add: csub.cs_refl)
  qed
  then have "\<Gamma> \<turnstile>\<^sub>c DAbs s : CArr (\<Delta> 0) A" by (rule cty_of.cAbs)
  moreover have "\<Gamma> \<turnstile>\<^sub>c u : \<Delta> 0"
  proof -
    have "\<Gamma> \<turnstile>\<^sub>c ins 0 u 0 : \<Delta> 0" using h1 by blast
    then show ?thesis by (simp add: ins_def)
  qed
  ultimately show ?thesis by (rule cty_of.cApp)
qed

lemma expand_appL:
  assumes "\<Gamma> \<turnstile>\<^sub>c r : A"
    and IH: "\<And>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>c s' : A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c s : A"
  shows "r = DApp s' u \<longrightarrow> \<Gamma> \<turnstile>\<^sub>c DApp s u : A"
using assms(1)
proof (induction rule: cty_of.induct)
  case (cVar \<Gamma> i A) then show ?case by simp
next
  case (cAbs A \<Gamma> t B) then show ?case by simp
next
  case (cApp \<Gamma> p A B q)
  show ?case
  proof
    assume e: "DApp p q = DApp s' u"
    then have "p = s'" "q = u" by simp_all
    with cApp.hyps have "\<Gamma> \<turnstile>\<^sub>c s' : CArr A B" "\<Gamma> \<turnstile>\<^sub>c u : A" by simp_all
    then show "\<Gamma> \<turnstile>\<^sub>c DApp s u : B" by (blast intro: IH cty_of.cApp)
  qed
next
  case (cOm \<Gamma> t) then show ?case by (simp add: cty_of.cOm)
next
  case (cInter \<Gamma> t A B) then show ?case by (blast intro: cty_of.cInter)
next
  case (cSub \<Gamma> t A B) then show ?case by (blast intro: cty_of.cSub)
qed

lemma subject_expansion_hred:
  assumes "t \<rightarrow>\<^sub>h t'"
  shows "\<Gamma> \<turnstile>\<^sub>c t' : A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c t : A"
using assms
proof (induction arbitrary: \<Gamma> A rule: hred.induct)
  case (hbeta s t)
  from hbeta.prems show ?case by (rule expand_beta)
next
  case (happ s s' t)
  from expand_appL[OF happ.prems happ.IH] show ?case by blast
qed

subsection \<open>Completeness and the classical theorem\<close>

lemma neutral_typable: "neutral n \<Longrightarrow> \<forall>A. \<exists>\<Gamma>. \<Gamma> \<turnstile>\<^sub>c n : A"
proof (induction rule: neutral.induct)
  case (nvar i)
  show ?case
  proof
    fix A show "\<exists>\<Gamma>. \<Gamma> \<turnstile>\<^sub>c DVar i : A" by (rule exI[of _ "\<lambda>_. A"]) (rule cty_of.cVar, simp)
  qed
next
  case (napp s u)
  show ?case
  proof
    fix A
    from napp.IH obtain \<Gamma> where "\<Gamma> \<turnstile>\<^sub>c s : CArr COm A" by blast
    then have "\<Gamma> \<turnstile>\<^sub>c DApp s u : A" by (rule cty_of.cApp) (rule cty_of.cOm)
    then show "\<exists>\<Gamma>. \<Gamma> \<turnstile>\<^sub>c DApp s u : A" by blast
  qed
qed

lemma normal_typable: "normal hred u \<Longrightarrow> \<exists>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>c u : A \<and> cess A"
proof -
  assume nf: "normal hred u"
  from normal_shape[OF nf] show ?thesis
  proof (rule disjE)
    assume "\<exists>s. u = DAbs s"
    then obtain s where u: "u = DAbs s" by blast
    have h: "(\<lambda>_. COm) \<turnstile>\<^sub>c DAbs s : CArr COm COm"
      by (rule cty_of.cAbs) (rule cty_of.cOm)
    show ?thesis unfolding u
      by (rule exI[of _ "\<lambda>_. COm"], rule exI[of _ "CArr COm COm"], rule conjI[OF h]) simp
  next
    assume "neutral u"
    from neutral_typable[OF this] obtain \<Gamma> where h: "\<Gamma> \<turnstile>\<^sub>c u : CTV 0" by blast
    show ?thesis by (rule exI[of _ \<Gamma>], rule exI[of _ "CTV 0"], rule conjI[OF h]) simp
  qed
qed

theorem classical_complete:
  assumes "lam_WHN t"
  shows "\<exists>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>c t : A \<and> cess A"
proof -
  from assms obtain u where r: "hred\<^sup>*\<^sup>* t u" and nf: "normal hred u" by (auto simp: lam_WHN_def)
  from normal_typable[OF nf] have "\<exists>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>c u : A \<and> cess A" .
  with r show ?thesis
  proof (induction rule: converse_rtranclp_induct)
    case base then show ?case by blast
  next
    case (step y z)
    then show ?case using subject_expansion_hred by blast
  qed
qed

theorem classical_WHN:
  "lam_WHN t \<longleftrightarrow> (\<exists>\<Gamma> A. \<Gamma> \<turnstile>\<^sub>c t : A \<and> cess A)"
  using classical_complete classical_sound by blast

end
