section \<open> Productive Reactive Designs \<close>

theory utp_rdes_productive
  imports utp_rdes_parallel
begin

subsection \<open> Healthiness condition \<close>

text \<open> A reactive design is productive if it strictly increases the trace, whenever it terminates.
  If it does not terminate, it is also classed as productive. \<close>

definition Productive :: "('s, 't::trace, '\<alpha>) rsp_hrel \<Rightarrow> ('s, 't, '\<alpha>) rsp_hrel" where
[pred]: "Productive(P) = P \<parallel>\<^sub>R \<^bold>R\<^sub>s(true \<turnstile> true \<diamondop> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)"

lemma Productive_alt_def:
  "Productive(P) = P \<parallel>\<^sub>R \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> true\<^sub>r \<diamondop> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)" (is "_ = _ \<parallel>\<^sub>R ?P")
proof - 
  have "?P = \<^bold>R\<^sub>s(true \<turnstile> true \<diamondop> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)"
    by (pred_simp, blast)
  thus ?thesis by (simp add: Productive_def)
qed

lemma Productive_RHS_design_form:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>> \<sharp> R"
  shows "Productive(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> (R \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e))"
  using assms by (simp add: Productive_def RHS_tri_design_par unrest rpred)

text \<open> We use the @{term R4} healthiness condition to characterise that the postcondition must
  extend the trace for a reactive design to be productive. \<close>

lemma Productive_RHS_R4_design_form:
  assumes "P is RR" "Q is RR" "R is RR"
  shows "Productive(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R4(R))"
  by (simp add: Productive_RHS_design_form closure assms unrest R4_def)

lemma Productive_form:
  "Productive(SRD(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e))"
proof -
  have "Productive(SRD(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) \<parallel>\<^sub>R \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> true\<^sub>r \<diamondop> (($tr\<^sup>< < $tr\<^sup>>)\<^sub>e))"
    by (simp add: Productive_alt_def SRD_as_reactive_tri_design)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e))"
    by (simp add: RHS_tri_design_par unrest rpred, pred_auto)
  finally show ?thesis .
qed

text \<open> A reactive design is productive provided that the postcondition, under the precondition,
  strictly increases the trace. \<close>

lemma Productive_intro:
  assumes "P is SRD" "(($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(P))" "$wait\<^sup>> \<sharp> pre\<^sub>R(P)"
  shows "P is Productive"
proof -
  have P:"\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)) = P"
  proof -
    have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (pre\<^sub>R(P) \<and> peri\<^sub>R(P)) \<diamondop> (pre\<^sub>R(P) \<and> post\<^sub>R(P)))"
      by (metis (no_types, opaque_lifting) design_export_pre wait'_cond_conj_exchange wait'_cond_idem)
    also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (pre\<^sub>R(P) \<and> peri\<^sub>R(P)) \<diamondop> (pre\<^sub>R(P) \<and> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)))"
      by (metis (no_types) assms(2) pred_ba.inf.absorb_iff1 pred_ba.inf_assoc)
    also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e))"
      by (metis (no_types, lifting) assms(2) calculation pred_ba.inf_assoc pred_ba.le_iff_inf srdes_tri_eq_intro)
    finally show ?thesis
      by (simp add: SRD_reactive_tri_design assms(1))
  qed
  thus ?thesis
    by (metis (mono_tags, lifting) Healthy_if Healthy_intro Productive_form assms(1))
qed

lemma Productive_post_refines_tr_increase:
  assumes "P is SRD" "P is Productive" "$wait\<^sup>> \<sharp> pre\<^sub>R(P)"
  shows "(($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(P))"
proof -
  have "post\<^sub>R(P) = post\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)))"
    by (metis Healthy_def Productive_form assms(1) assms(2))
  also have "... = R1(R2c(pre\<^sub>R(P) \<Rightarrow> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)))"
    by (simp add: rea_post_RHS_design unrest usubst assms, pred_auto)
  also have "... = R1((pre\<^sub>R(P) \<Rightarrow> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)))"
    by (simp add: R2c_impl R2c_preR R2c_postR R2c_and R2c_tr_less_tr' assms)
  also have "(($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) \<sqsubseteq> (pre\<^sub>R(P) \<and> ...)"
    by (pred_auto)
  finally show ?thesis .
qed

lemma Continuous_Productive [closure]: "Continuous Productive"
  by (simp add: Continuous_def Productive_def, pred_auto)

subsection \<open> Reactive design calculations \<close>

lemma preR_Productive [rdes]:
  assumes "P is SRD"
  shows "pre\<^sub>R(Productive(P)) = pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(Productive(P)) = pre\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)))"
    by (metis Healthy_def Productive_form assms)
  thus ?thesis
    by (simp add: rea_pre_RHS_design usubst unrest R2c_not R2c_preR R1_preR Healthy_if assms)
qed

lemma periR_Productive [rdes]:
  assumes "P is NSRD"
  shows "peri\<^sub>R(Productive(P)) = peri\<^sub>R(P)"
proof -
  have "peri\<^sub>R(Productive(P)) = peri\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)))"
    by (metis Healthy_def NSRD_is_SRD Productive_form assms)
  also have "... = R1 (R2c (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))"
    by (simp add: rea_peri_RHS_design usubst unrest R2c_not assms closure)
  also have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)"
    by (simp add: R1_rea_impl R2c_rea_impl R2c_preR R2c_peri_SRD
                  R1_peri_SRD assms closure R1_tr_less_tr' R2c_tr_less_tr')
  finally show ?thesis
    by (simp add: SRD_peri_under_pre assms unrest closure)
qed

lemma postR_Productive [rdes]:
  assumes "P is NSRD"
  shows "post\<^sub>R(Productive(P)) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)"
proof -
  have "post\<^sub>R(Productive(P)) = post\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)))"
    by (metis Healthy_def NSRD_is_SRD Productive_form assms)
  also have "... = R1 (R2c (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr))"
    by (simp add: rea_post_RHS_design usubst unrest assms closure)
  also have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)"
    by (simp add: R1_rea_impl R2c_rea_impl R2c_preR R2c_and R1_extend_conj' R2c_post_SRD
             R1_post_SRD assms closure R1_tr_less_tr' R2c_tr_less_tr')
  finally show ?thesis .
qed

lemma preR_frame_seq_export:
  assumes "P is NSRD" "P is Productive" "Q is NSRD"
  shows "(pre\<^sub>R P \<and> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q) = (pre\<^sub>R P \<and> (post\<^sub>R P ;; Q))"
proof -
  have "(pre\<^sub>R P \<and> (post\<^sub>R P ;; Q)) = (pre\<^sub>R P \<and> ((pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; Q))"
    by (simp add: SRD_post_under_pre assms closure unrest)
  also have "... = (pre\<^sub>R P \<and> (((\<not>\<^sub>r pre\<^sub>R P) ;; Q \<or> (pre\<^sub>R P \<Rightarrow>\<^sub>r R1(post\<^sub>R P)) ;; Q)))"
    by (simp add: NSRD_is_SRD R1_post_SRD assms(1) rea_impl_def seqr_or_distl R1_preR Healthy_if)
  also have "... = (pre\<^sub>R P \<and> (((\<not>\<^sub>r pre\<^sub>R P) ;; Q \<or> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)))"
  proof -
    have "(pre\<^sub>R P \<or> \<not>\<^sub>r pre\<^sub>R P) = R1 true"
      by (simp add: R1_preR rea_not_or)
    then show ?thesis
      by (metis (no_types, lifting) R1_def conj_comm disj_comm disj_conj_distr rea_impl_def seqr_or_distl utp_pred_laws.inf_top_left utp_pred_laws.sup.left_idem)
  qed
  also have "... = (pre\<^sub>R P \<and> (((\<not>\<^sub>r pre\<^sub>R P) \<or> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)))"
    by (simp add: NSRD_neg_pre_left_zero assms closure SRD_healths)
  also have "... = (pre\<^sub>R P \<and> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)"
    by (rel_blast)
  finally show ?thesis ..
qed


subsection \<open> Closure laws \<close>

lemma Productive_rdes_intro:
  assumes "(($tr\<^sup>< < $tr\<^sup>>)\<^sub>e) \<sqsubseteq> R" "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>> \<sharp> R" "$wait \<sharp> P" "$wait\<^sup>> \<sharp> P"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) is Productive"
proof (rule Productive_intro)
  show "\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R) is SRD"
    by (simp add: RHS_tri_design_is_SRD assms)

  from assms(1) show "($tr\<acute> >\<^sub>u $tr) \<sqsubseteq> (pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R)) \<and> post\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R)))"
    apply (simp add: rea_pre_RHS_design rea_post_RHS_design usubst assms unrest)
    using assms(1) apply (pred_auto)
    apply fastforce
    done

  show "$wait\<^sup>> \<sharp> pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R))"
    by (simp add: rea_pre_RHS_design rea_post_RHS_design usubst R1_def R2c_def R2s_def assms unrest)
qed

lemma Productive_rdes_RR_intro [closure]:
  assumes "P is RR" "Q is RR" "R is RR" "R is R4"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) is Productive"
  using assms by (simp add: Productive_rdes_intro R4_iff_refine unrest)

lemma Productive_Miracle [closure]: "Miracle is Productive"
  unfolding Miracle_tri_def Healthy_def
  by (subst Productive_RHS_design_form, simp_all add: unrest closure)

lemma Productive_Chaos [closure]: "Chaos is Productive"
  unfolding Chaos_tri_def Healthy_def
  by (subst Productive_RHS_design_form, simp_all add: unrest closure)

lemma Productive_intChoice [closure]:
  assumes "P is SRD" "P is Productive" "Q is SRD" "Q is Productive"
  shows "P \<sqinter> Q is Productive"
proof -
  have "P \<sqinter> Q =
        \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)) \<sqinter> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e))"
    by (metis Healthy_if Productive_form assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> peri\<^sub>R Q) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) \<or> (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: RHS_tri_design_choice)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> peri\<^sub>R Q) \<diamondop> (((post\<^sub>R P) \<or> (post\<^sub>R Q)) \<and> $tr\<acute> >\<^sub>u $tr))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, pred_auto)
  also have "... is Productive"
    by (metis Healthy_def Productive_form assms(1) assms(3) calculation periR_inf postR_inf preR_inf srdes_theory.meet_is_healthy)
  finally show ?thesis .
qed

lemma cond_R1_closure [closure]: "\<lbrakk> P is R1; Q is R1 \<rbrakk> \<Longrightarrow> P \<triangleleft> b \<triangleright>\<^sub>R Q is R1"
  by (pred_auto)

lemma Productive_cond_rea [closure]:
  assumes "P is SRD" "P is Productive" "Q is SRD" "Q is Productive"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is Productive"
proof -
  have "P \<triangleleft> b \<triangleright>\<^sub>R Q =
        \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e))"
    by (metis Healthy_if Productive_form assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R peri\<^sub>R Q) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) \<triangleleft> b \<triangleright>\<^sub>R (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: cond_srea_form)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R peri\<^sub>R Q) \<diamondop> (((post\<^sub>R P) \<triangleleft> b \<triangleright>\<^sub>R (post\<^sub>R Q)) \<and> $tr\<acute> >\<^sub>u $tr))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, pred_auto)
  also have "... is Productive"
    by (simp add: Healthy_def, simp add: Productive_RHS_design_form closure unrest assms)
  finally show ?thesis .
qed

lemma Productive_seq_1 [closure]:
  assumes "P is NSRD" "P is Productive" "Q is NSRD"
  shows "P ;; Q is Productive"
proof -
  have "P ;; Q = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e)) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q)))"
    by (metis Healthy_def NSRD_is_SRD SRD_reactive_tri_design Productive_form assms(1) assms(2) assms(3))
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) wp\<^sub>r pre\<^sub>R Q) \<turnstile>
                       (peri\<^sub>R P \<or> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; peri\<^sub>R Q)) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; post\<^sub>R Q))"
    by (simp add: RHS_tri_design_composition_wp rpred unrest closure assms wp NSRD_neg_pre_left_zero  SRD_healths ex_unrest wp_rea_def disj_upred_def)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) wp\<^sub>r pre\<^sub>R Q) \<turnstile>
                       (peri\<^sub>R P \<or> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; peri\<^sub>R Q)) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr))"
  proof -
    have "((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; R1(post\<^sub>R Q)) = ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; R1(post\<^sub>R Q) \<and> $tr\<acute> >\<^sub>u $tr)"
      by (pred_auto)
    thus ?thesis
      by (simp add: NSRD_is_SRD R1_post_SRD assms)
  qed
  also have "... is Productive"
    by (rule Productive_rdes_intro, simp_all add: unrest assms closure wp_rea_def)
  finally show ?thesis .
qed

lemma Productive_seq_2 [closure]:
  assumes "P is NSRD" "Q is NSRD" "Q is Productive"
  shows "P ;; Q is Productive"
proof -
  have "P ;; Q = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P))) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e))"
    by (metis Healthy_def NSRD_is_SRD SRD_reactive_tri_design Productive_form assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: RHS_tri_design_composition_wp rpred unrest closure assms wp NSRD_neg_pre_left_zero  SRD_healths ex_unrest wp_rea_def disj_upred_def)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr) \<and> $tr\<acute> >\<^sub>u $tr))"
  proof -
    have "(R1(post\<^sub>R P) ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr) \<and> $tr\<acute> >\<^sub>u $tr) = (R1(post\<^sub>R P) ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr))"
      by (pred_auto)
    thus ?thesis
      by (simp add: NSRD_is_SRD R1_post_SRD assms)
  qed
  also have "... is Productive"
    by (rule Productive_rdes_intro, simp_all add: unrest assms closure wp_rea_def)
  finally show ?thesis .
qed

end