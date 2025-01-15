section \<open> Reactive design parallel-by-merge \<close>

theory utp_rdes_parallel
  imports 
    utp_rdes_normal 
    utp_rdes_tactics
begin

lemma par_by_merge_mono: "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2; M\<^sub>1 \<sqsubseteq> M\<^sub>2 \<rbrakk> \<Longrightarrow> P\<^sub>1 \<parallel>\<^bsub>M\<^sub>1\<^esub> Q\<^sub>1 \<sqsubseteq> P\<^sub>2 \<parallel>\<^bsub>M\<^sub>2\<^esub> Q\<^sub>2"
  by (pred_auto, metis)

text \<open> R3h implicitly depends on RD1, and therefore it requires that both sides be RD1. We also
  require that both sides are R3c, and that @{term "wait\<^sub>m"} is a quasi-unit, and @{term "div\<^sub>m"} yields
  divergence. \<close>

lemma st_U0_alpha: "\<lceil>\<exists> st\<^sup>< \<Zspot> II\<rceil>\<^sub>0 = (\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>0)"
  by (pred_auto)

lemma st_U1_alpha: "\<lceil>\<exists> st\<^sup>< \<Zspot> II\<rceil>\<^sub>1 = (\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>1)"
  by (pred_auto)

definition skip_rm :: "('s,'t::trace,'\<alpha>) rsp merge" ("II\<^sub>R\<^sub>M") where
  [pred]: "II\<^sub>R\<^sub>M = (\<exists> <:st\<^sup>< \<Zspot> skip\<^sub>m \<or> (\<not> $<:ok\<^sup>< \<and> $<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e)"

definition [pred]: "R3hm(M) = (II\<^sub>R\<^sub>M \<triangleleft> $<:wait\<^sup>< \<triangleright> M)"

lemma R3hm_idem: "R3hm(R3hm(P)) = R3hm(P)"
  by (pred_auto)

abbreviation copytype :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("CPTYPE'(_, _')") where "CPTYPE(A, B) \<equiv> B"

term "($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e"
term "($<\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e"
term "($\<^bold>v\<^sup>> = $<\<^sup><)\<^sub>e"
term "($<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e"

lemma R3h_par_by_merge [closure]:
  assumes "P is R3h" "Q is R3h" "M is R3hm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R3h"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>True/ok\<^sup><\<rbrakk> \<triangleleft> $ok\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>False/ok\<^sup><\<rbrakk>)\<lbrakk>True/wait\<^sup><\<rbrakk> \<triangleleft> $wait\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: expr_if_bool_var_left expr_if_bool_var_right)
  also have "... = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk> \<triangleleft> $ok\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>False,True/ok\<^sup><,wait\<^sup><\<rbrakk>) \<triangleleft> $wait\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: usubst)
  also have "... = (((\<exists> st\<^sup>< \<Zspot> II)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk> \<triangleleft> $ok\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>False,True/ok\<^sup><,wait\<^sup><\<rbrakk>) \<triangleleft> $wait\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
  proof -
    have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk> = ((\<lceil>P\<rceil>\<^sub>0 \<and> \<lceil>Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; R3hm(M))\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
      by (simp add: par_by_merge_def par_sep_def U0_as_alpha U1_as_alpha assms Healthy_if, rel_simp)
    also have "... = ((\<lceil>P\<rceil>\<^sub>0 \<and> \<lceil>Q\<rceil>\<^sub>1 \<and> ($<\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (\<exists> <:st\<^sup>< \<Zspot> CPTYPE(M,($\<^bold>v\<^sup>> = $<\<^sup><)\<^sub>e)))\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
      by (pred_simp, meson)
    also have "... = ((\<lceil>R3h(P)\<rceil>\<^sub>0 \<and> \<lceil>R3h(Q)\<rceil>\<^sub>1 \<and> ($<\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (\<exists> <:st\<^sup>< \<Zspot> CPTYPE(M, ($\<^bold>v\<^sup>> = $<\<^sup><)\<^sub>e)))\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
      by (simp add: assms Healthy_if)
    also have "... = (\<exists> st\<^sup>< \<Zspot> II)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
      by (pred_auto)
    finally show ?thesis by (simp add: closure assms unrest)
  qed
  also have "... = (((\<exists> st\<^sup>< \<Zspot> II)\<lbrakk>True,True/ok\<^sup><,wait\<^sup><\<rbrakk> \<triangleleft> $ok\<^sup>< \<triangleright> (R1(true))\<lbrakk>False,True/ok\<^sup><,wait\<^sup><\<rbrakk>) \<triangleleft> $wait\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
  proof -
    have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>False,True/ok\<^sup><,wait\<^sup><\<rbrakk> = ((\<lceil>P\<rceil>\<^sub>0 \<and> \<lceil>Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; R3hm(M))\<lbrakk>False,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
      by (simp add: par_by_merge_def U0_as_alpha U1_as_alpha assms Healthy_if, pred_simp)
    also have "... = ((\<lceil>P\<rceil>\<^sub>0 \<and> \<lceil>Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (CPTYPE(M, ($<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e)))\<lbrakk>False,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
      by (pred_simp, metis dual_order.refl)
    also have "... = ((\<lceil>R3h(P)\<rceil>\<^sub>0 \<and> \<lceil>R3h(Q)\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (CPTYPE(M, ($<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e)))\<lbrakk>False,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
      by (simp add: assms Healthy_if)
    also have "... = (R1(true))\<lbrakk>False,True/ok\<^sup><,wait\<^sup><\<rbrakk>"
      by (pred_auto; blast)
    finally show ?thesis by simp
  qed
  also have "... = (((\<exists> st\<^sup>< \<Zspot> II) \<triangleleft> $ok\<^sup>< \<triangleright> R1(true)) \<triangleleft> $wait\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (pred_auto)
  also have "... = R3h(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: R3h_cases)
  finally show ?thesis
    by (simp add: Healthy_def)
qed

definition [pred]: "RD1m(M) = (M \<or> (\<not> $<:ok\<^sup><)\<^sub>e \<and> ($<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e)"

lemma RD1_par_by_merge [closure]:
  assumes "P is R1" "Q is R1" "M is R1m" "P is RD1" "Q is RD1" "M is RD1m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD1"
proof -
  have 1: "(RD1(R1(P)) \<parallel>\<^bsub>RD1m(R1m(M))\<^esub> RD1(R1(Q)))\<lbrakk>False/ok\<^sup><\<rbrakk> = R1(true)"
    by (pred_auto; blast)
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>True/ok\<^sup><\<rbrakk> \<triangleleft> $ok\<^sup>< \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>False/ok\<^sup><\<rbrakk>"
    by (simp add: expr_if_bool_var_left expr_if_bool_var_right)
  also have "... = R1(P \<parallel>\<^bsub>M\<^esub> Q) \<triangleleft> $ok\<^sup>< \<triangleright> R1(true)"
    by (metis "1" Healthy_if R1_par_by_merge assms calculation 
              expr_if_bool_var_right expr_if_idem fst_vwb_lens ns_alpha_vwb ok_vwb_lens)
  also have "... = RD1(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: Healthy_if R1_par_by_merge RD1_alt_def assms(3))
  finally show ?thesis
    by (simp add: Healthy_def)
qed

lemma RD2_par_by_merge [closure]:
  assumes "M is RD2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD2"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = ((P \<parallel>\<^sub>s Q) ;; M)"
    by (simp add: par_by_merge_def)
  also from assms have "... = ((P \<parallel>\<^sub>s Q) ;; (M ;; J))"
    by (simp add: Healthy_def' RD2_def H2_def)
  also from assms have "... = (((P \<parallel>\<^sub>s Q) ;; M) ;; J)"
    by (simp add: seqr_assoc)
  also from assms have "... = RD2(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: RD2_def H2_def par_by_merge_def)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma SRD_par_by_merge:
  assumes "P is SRD" "Q is SRD" "M is R1m" "M is R2m" "M is R3hm" "M is RD1m" "M is RD2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is SRD"
  by (rule SRD_intro, simp_all add: assms closure SRD_healths)

definition nmerge_rd0 ("N\<^sub>0") where
[pred]: "N\<^sub>0(M) = (($wait\<^sup>> = ($0:wait\<^sup>< \<or> $1:wait\<^sup><) \<and> $<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e
                        \<and> (\<exists> (0:ok\<^sup><,1:ok\<^sup><,<:ok\<^sup><,ok\<^sup>>,0:wait\<^sup><,1:wait\<^sup><,<:wait\<^sup><,wait\<^sup>>) \<Zspot> M))"

expr_constructor nmerge_rd0

definition nmerge_rd1 ("N\<^sub>1") where
[pred]: "N\<^sub>1(M) = (($ok\<^sup>> = ($0:ok\<^sup>< \<and> $1:ok\<^sup><))\<^sub>e \<and> N\<^sub>0(M))"

definition nmerge_rd ("N\<^sub>R") where
[pred]: "N\<^sub>R(M) = ((\<exists> <:st\<^sup>< \<Zspot> ($\<^bold>v\<^sup>> = $<\<^sup><)\<^sub>e) \<triangleleft> $<:wait\<^sup>< \<triangleright> N\<^sub>1(M)) \<triangleleft> $<:ok\<^sup>< \<triangleright> (($<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e)"

definition merge_rd1 ("M\<^sub>1") where
[pred]: "M\<^sub>1(M) = (N\<^sub>1(M) ;; II\<^sub>R)"

definition merge_rd ("M\<^sub>R") where
[pred]: "M\<^sub>R(M) = N\<^sub>R(M) ;; II\<^sub>R"

abbreviation rdes_par ("_ \<parallel>\<^sub>R\<^bsub>_\<^esub> _" [85,0,86] 85) where
"P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q \<equiv> P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q"

text \<open> Healthiness condition for reactive design merge predicates \<close>

definition [pred]: "RDM(M) = R2m(\<exists> (0:ok\<^sup><,1:ok\<^sup><,<:ok\<^sup><,ok\<^sup>>,0:wait\<^sup><,1:wait\<^sup><,<:wait\<^sup><,wait\<^sup>>) \<Zspot> M)"

lemma nmerge_rd_is_R1m [closure]:
  "N\<^sub>R(M) is R1m"
  using dual_order.refl minus_zero_eq trace_class.diff_cancel 
  by (pred_simp, blast)

lemma R2m_nmerge_rd: "R2m(N\<^sub>R(R2m(M))) = N\<^sub>R(R2m(M))" 
  by (pred_simp, meson dual_order.refl minus_zero_eq trace_class.diff_cancel)
    
lemma nmerge_rd_is_R2m [closure]:
  "M is R2m \<Longrightarrow> N\<^sub>R(M) is R2m"
  by (metis Healthy_def' R2m_nmerge_rd)

lemma nmerge_rd_is_R3hm [closure]: "N\<^sub>R(M) is R3hm"
  by (pred_simp, meson dual_order.refl minus_zero_eq trace_class.diff_cancel)

lemma nmerge_rd_is_RD1m [closure]: "N\<^sub>R(M) is RD1m"
  by (pred_auto; blast)

lemma merge_rd_is_RD3: "M\<^sub>R(M) is RD3"
  by (metis Healthy_Idempotent RD3_Idempotent RD3_def merge_rd_def)

lemma merge_rd_is_RD2: "M\<^sub>R(M) is RD2"
  by (simp add: RD3_implies_RD2 merge_rd_is_RD3)
    
lemma par_rdes_NSRD [closure]:
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Q is NSRD"
proof -
  have "(P \<parallel>\<^bsub>N\<^sub>R M\<^esub> Q ;; II\<^sub>R) is NSRD"
    by (rule NSRD_intro', simp_all add: SRD_healths closure assms)
       (metis (no_types, lifting) Healthy_def R2_par_by_merge R2_seqr_closure R2m_nmerge_rd RDM_def SRD_healths(2) assms skip_srea_R2
       ,metis Healthy_Idempotent RD3_Idempotent RD3_def)
  thus ?thesis
    by (simp add: merge_rd_def par_by_merge_def seqr_assoc)
qed

lemma unrest_pair [unrest]:
  assumes "mwb_lens x" "mwb_lens y" "$x \<sharp> P" "$y \<sharp> P"
  shows "$(x, y) \<sharp> P"
  using assms
  by expr_simp (simp add: lens_override_def lens_scene.rep_eq scene_override.rep_eq)

lemma RDM_intro:
  assumes "M is R2m" "$0:ok\<^sup>< \<sharp> M" "$1:ok\<^sup>< \<sharp> M" "$<:ok\<^sup>< \<sharp> M" "$ok\<^sup>> \<sharp> M"
          "$0:wait\<^sup>< \<sharp> M" "$1:wait\<^sup>< \<sharp> M" "$<:wait\<^sup>< \<sharp> M" "$wait\<^sup>> \<sharp> M"
  shows "M is RDM"
  using assms
  by (simp add: Healthy_def RDM_def ex_unrest unrest)

lemma RDM_unrests [unrest]:
  assumes "M is RDM"
  shows "$0:ok\<^sup>< \<sharp> M" "$1:ok\<^sup>< \<sharp> M" "$<:ok\<^sup>< \<sharp> M" "$ok\<^sup>> \<sharp> M"
        "$0:wait\<^sup>< \<sharp> M" "$1:wait\<^sup>< \<sharp> M" "$<:wait\<^sup>< \<sharp> M" "$wait\<^sup>> \<sharp> M"
  by (subst Healthy_if[OF assms, THEN sym], simp_all add: RDM_def unrest, pred_auto)+

lemma RDM_R1m [closure]: "M is RDM \<Longrightarrow> M is R1m"
  by (metis (no_types, lifting) Healthy_if Healthy_intro R1m_idem R2m_def RDM_def)

lemma RDM_R2m [closure]: "M is RDM \<Longrightarrow> M is R2m"
  by (metis (no_types, opaque_lifting) Healthy_def R2m_idem RDM_def)

lemma ex_st'_R2m_closed [closure]: 
  assumes "P is R2m"
  shows "(\<exists> st\<^sup>> \<Zspot> P) is R2m"
proof -
  have "R2m(\<exists> st\<^sup>> \<Zspot> R2m P) = (\<exists> st\<^sup>> \<Zspot> R2m P)"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_def' assms) 
qed
    
lemma parallel_RR_closed: 
  assumes "P is RR" "Q is RR" "M is R2m" 
          "$<:ok\<^sup>< \<sharp> M" "$<:wait\<^sup>< \<sharp> M" "$ok\<^sup>> \<sharp> M" "$wait\<^sup>> \<sharp> M"
  shows "P \<parallel>\<^bsub>M\<^esub> Q is RR"
  by (rule RR_R2_intro, simp_all add: unrest assms RR_implies_R2 closure)

lemma parallel_ok_cases:
"P \<parallel>\<^bsub>M\<^esub> Q = (
  (P\<^sup>t \<parallel>\<^bsub>M\<lbrakk>True,True/0:ok\<^sup><,1:ok\<^sup><\<rbrakk>\<^esub> Q\<^sup>t) \<or>
  (P\<^sup>f \<parallel>\<^bsub>M\<lbrakk>False,True/0:ok\<^sup><,1:ok\<^sup><\<rbrakk>\<^esub> Q\<^sup>t) \<or>
  (P\<^sup>t \<parallel>\<^bsub>M\<lbrakk>True,False/0:ok\<^sup><,1:ok\<^sup><\<rbrakk>\<^esub> Q\<^sup>f) \<or>
  (P\<^sup>f \<parallel>\<^bsub>M\<lbrakk>False,False/0:ok\<^sup><,1:ok\<^sup><\<rbrakk>\<^esub> Q\<^sup>f))"
  by (pred_auto, (metis (full_types))+)

(*
lemma parallel_ok_cases:
"((P \<parallel>\<^sub>s Q) ;; M) = (
  ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>True,True/0:ok\<^sup><,1:ok\<^sup><\<rbrakk>)) \<or>
  ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>False,True/0:ok\<^sup><,1:ok\<^sup><\<rbrakk>)) \<or>
  ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>True,False/0:ok\<^sup><,1:ok\<^sup><\<rbrakk>)) \<or>
  ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>False,False/0:ok\<^sup><,1:ok\<^sup><\<rbrakk>)))"
  by (pred_auto, (metis (full_types))+)
*)

lemma skip_srea_ok_f [usubst]:
  "II\<^sub>R\<^sup>f = R1(\<not>ok\<^sup><)"
  by (pred_auto)

lemma nmerge0_rd_unrest [unrest]:
  "$0:ok\<^sup>< \<sharp> N\<^sub>0 M" "$1:ok\<^sup>< \<sharp> N\<^sub>0 M"
  by (pred_auto)+

term unrest

lemma subst_upd_lit_seql [usubst]: "\<sigma>(x\<^sup>< \<leadsto> \<guillemotleft>v\<guillemotright>) \<dagger> (P ;; Q) = \<sigma> \<dagger> (([x\<^sup>< \<leadsto> \<guillemotleft>v\<guillemotright>] \<dagger> P) ;; Q)"
  by pred_auto

lemma subst_upd_lit_seqr [usubst]: "\<sigma>(x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright>) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; [x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright>] \<dagger> Q)"
  by pred_auto

expr_constructor wait_f
expr_constructor wait_t

lemma parallel_assm_lemma:
  assumes "P is RD2"
  shows "pre\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (((pre\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (cmt\<^sub>s \<dagger> Q))
                                 \<or> ((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (pre\<^sub>s \<dagger> Q)))"
proof -
  have "pre\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (P\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<parallel>\<^bsub>N\<^sub>1(M) ;; R1(\<not> ok\<^sup><)\<^esub> Q\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>)"
    by (simp add: merge_rd_def nmerge_rd_def nmerge_rd1_def usubst unrest assms closure, pred_auto)

  also have "... = 
    (([ok\<^sup>< \<leadsto> True, wait\<^sup>< \<leadsto> False] \<dagger> P)\<lbrakk>True/ok\<^sup>>\<rbrakk> \<parallel>\<^bsub>[0:ok\<^sup>< \<leadsto> True, 1:ok\<^sup>< \<leadsto> True] \<dagger> (N\<^sub>1 M ;; R1 (\<not> ($ok)\<^sup><))\<^esub> ([ok\<^sup>< \<leadsto> True, wait\<^sup>< \<leadsto> False] \<dagger> Q)\<lbrakk>True/ok\<^sup>>\<rbrakk> \<or>
     ([ok\<^sup>< \<leadsto> True, wait\<^sup>< \<leadsto> False] \<dagger> P)\<lbrakk>False/ok\<^sup>>\<rbrakk> \<parallel>\<^bsub>[0:ok\<^sup>< \<leadsto> False, 1:ok\<^sup>< \<leadsto> True] \<dagger> (N\<^sub>1 M ;; R1 (\<not> ($ok)\<^sup><))\<^esub> ([ok\<^sup>< \<leadsto> True, wait\<^sup>< \<leadsto> False] \<dagger> Q)\<lbrakk>True/ok\<^sup>>\<rbrakk> \<or>
     ([ok\<^sup>< \<leadsto> True, wait\<^sup>< \<leadsto> False] \<dagger> P)\<lbrakk>True/ok\<^sup>>\<rbrakk> \<parallel>\<^bsub>[0:ok\<^sup>< \<leadsto> True, 1:ok\<^sup>< \<leadsto> False] \<dagger> (N\<^sub>1 M ;; R1 (\<not> ($ok)\<^sup><))\<^esub> ([ok\<^sup>< \<leadsto> True, wait\<^sup>< \<leadsto> False] \<dagger> Q)\<lbrakk>False/ok\<^sup>>\<rbrakk> \<or>
     ([ok\<^sup>< \<leadsto> True, wait\<^sup>< \<leadsto> False] \<dagger> P)\<lbrakk>False/ok\<^sup>>\<rbrakk> \<parallel>\<^bsub>[0:ok\<^sup>< \<leadsto> False, 1:ok\<^sup>< \<leadsto> False] \<dagger> (N\<^sub>1 M ;; R1 (\<not> ($ok)\<^sup><))\<^esub> ([ok\<^sup>< \<leadsto> True, wait\<^sup>< \<leadsto> False] \<dagger> Q)\<lbrakk>False/ok\<^sup>>\<rbrakk>)"
    (is "_ = ((?C1 :: _ pred) \<or> ?C2 \<or> ?C3 \<or> ?C4)")
    by (simp add: parallel_ok_cases[THEN sym])

  also have "... = (?C2 \<or> ?C3)"
  proof -
    have "?C1 = false"
      by (pred_auto)
    moreover have "?C3 \<sqsubseteq> ?C4" (* have "`?C4 \<longrightarrow> ?C3`" (is "`(?A ;; ?B) \<longrightarrow> (?C ;; ?D)`") *)
    proof -
      from assms have "`P\<^sup>f \<longrightarrow> P\<^sup>t`"
        by (simp add: H2_equivalence[THEN sym] RD2_def Healthy_def')
      hence P: "`P\<^sup>f\<lbrakk>False/wait\<^sup><\<rbrakk> \<longrightarrow> P\<^sup>t\<lbrakk>False/wait\<^sup><\<rbrakk>`"
        by (pred_auto)
      thus ?thesis
        by pred_simp metis
    qed
    ultimately show ?thesis
      by (simp add: pred_ba.sup_absorb1)
  qed
  also have "... = (
      (((pre\<^sub>s \<dagger> P) \<parallel>\<^sub>s (cmt\<^sub>s \<dagger> Q)) ;; ((N\<^sub>0 M ;; R1(true)))) \<or>
      (((cmt\<^sub>s \<dagger> P) \<parallel>\<^sub>s (pre\<^sub>s \<dagger> Q)) ;; ((N\<^sub>0 M ;; R1(true)))))"
    by (pred_auto)
  also have "... = (
      ((pre\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0 M ;; R1(true)\<^esub> (cmt\<^sub>s \<dagger> Q)) \<or>
      ((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0 M ;; R1(true)\<^esub> (pre\<^sub>s \<dagger> Q)))"
    by (simp add: par_by_merge_def)
  finally show ?thesis .
qed

(*
lemma parallel_assm:
  assumes "P is SRD"
  shows "pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (\<not> ((\<not> pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q)) \<and>
                                   \<not> (cmt\<^sub>R(P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (\<not> pre\<^sub>R(Q))))"
  by (simp add: pre\<^sub>R_def parallel_assm_lemma SRD_healths assms, pred_auto)
*)
  
lemma pre\<^sub>s_SRD:
  assumes "P is SRD"
  shows "pre\<^sub>s \<dagger> P = (\<not>\<^sub>r pre\<^sub>R(P))"
proof -
  have "pre\<^sub>s \<dagger> P = pre\<^sub>s \<dagger> \<^bold>R\<^sub>s(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (simp add: SRD_reactive_tri_design assms)
  also have "... = R1(R2c(\<not> pre\<^sub>s \<dagger> pre\<^sub>R P))"
    by (simp add: RHS_def usubst R3h_def pre\<^sub>s_design)
  also have "... = R1(R2c(\<not> pre\<^sub>R P))"
    by (pred_auto)
  also have "... = (\<not>\<^sub>r pre\<^sub>R P)"
    by (simp add: R2c_not R2c_preR assms rea_not_def)
  finally show ?thesis .
qed

lemma parallel_assm:
  assumes "P is SRD" "Q is SRD"
  shows "pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (\<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q)) \<and>
                                   \<not>\<^sub>r (cmt\<^sub>R(P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (\<not>\<^sub>r pre\<^sub>R(Q))))"
  (is "?lhs = ?rhs")
proof -
  have "pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (\<not>\<^sub>r (pre\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0 M ;; R1 true\<^esub> (cmt\<^sub>s \<dagger> Q) \<and>
                             \<not>\<^sub>r (cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0 M ;; R1 true\<^esub> (pre\<^sub>s \<dagger> Q))"
    by (simp add: pre\<^sub>R_def parallel_assm_lemma assms SRD_healths R1_conj rea_not_def[THEN sym])
  also have "... = ?rhs"
    by (simp add: pre\<^sub>s_SRD assms cmt\<^sub>R_def Healthy_if closure unrest)
  finally show ?thesis .
qed

lemma parallel_assm_unrest_wait' [unrest]:
  "\<lbrakk> P is SRD; Q is SRD \<rbrakk> \<Longrightarrow> $wait\<^sup>> \<sharp> pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q)"
  by (simp add: parallel_assm, simp add: par_by_merge_def unrest)



lemma JL1: "[0:ok\<^sup>< \<leadsto> False, 1:ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> True] \<dagger> M\<^sub>1 M = N\<^sub>0(M) ;; R1(true)"
  by (pred_auto; metis)

lemma JL2: "[0:ok\<^sup>< \<leadsto> True, 1:ok\<^sup>< \<leadsto> False, ok\<^sup>> \<leadsto> True] \<dagger> M\<^sub>1 M = N\<^sub>0(M) ;; R1(true)"
  by (pred_auto; metis)

lemma JL3: "[0:ok\<^sup>< \<leadsto> False, 1:ok\<^sup>< \<leadsto> False, ok\<^sup>> \<leadsto> True] \<dagger> M\<^sub>1 M = N\<^sub>0(M) ;; R1(true)"
  by (pred_auto; metis)

lemma JL4: "[0:ok\<^sup>< \<leadsto> True, 1:ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> True] \<dagger> M\<^sub>1 M = (ok\<^sup>> \<and> N\<^sub>0 M) ;; II\<^sub>R\<^sup>t"
  by (simp add: merge_rd1_def usubst nmerge_rd1_def unrest)

lemma parallel_commitment_lemma_1:
  assumes "P is RD2"
  shows "cmt\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (
  ((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>($ok\<^sup>> \<and> N\<^sub>0 M)\<^sub>e ;; II\<^sub>R\<^sup>t\<^esub> (cmt\<^sub>s \<dagger> Q)) \<or>
  ((pre\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (cmt\<^sub>s \<dagger> Q)) \<or>
  ((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (pre\<^sub>s \<dagger> Q)))"
proof -
  have "cmt\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (P\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<parallel>\<^bsub>(M\<^sub>1(M))\<^sup>t\<^esub> Q\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>)"
    by (simp add: usubst, pred_auto)
  also have "... = 
   ((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>[0:ok\<^sup>< \<leadsto> True, 1:ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> True] \<dagger> M\<^sub>1 M\<^esub> (cmt\<^sub>s \<dagger> Q) \<or>
     npre\<^sub>R P \<parallel>\<^bsub>[0:ok\<^sup>< \<leadsto> False, 1:ok\<^sup>< \<leadsto> True, ok\<^sup>> \<leadsto> True] \<dagger> M\<^sub>1 M\<^esub> (cmt\<^sub>s \<dagger> Q) \<or>
     (cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>[0:ok\<^sup>< \<leadsto> True, 1:ok\<^sup>< \<leadsto> False, ok\<^sup>> \<leadsto> True] \<dagger> M\<^sub>1 M\<^esub> npre\<^sub>R Q \<or> 
     npre\<^sub>R P \<parallel>\<^bsub>[0:ok\<^sup>< \<leadsto> False, 1:ok\<^sup>< \<leadsto> False, ok\<^sup>> \<leadsto> True] \<dagger> M\<^sub>1 M\<^esub> npre\<^sub>R Q)"
    by (subst parallel_ok_cases, simp add: usubst)
  also have "... = 
     ((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>[0:ok\<^sup>< \<leadsto> True, 1:ok\<^sup>< \<leadsto> True] \<dagger> M\<^sub>1 M\<lbrakk>True/ok\<^sup>>\<rbrakk>\<^esub> (cmt\<^sub>s \<dagger> Q) \<or>
      npre\<^sub>R P \<parallel>\<^bsub>N\<^sub>0 M ;; true\<^sub>r\<^esub> (cmt\<^sub>s \<dagger> Q) \<or> 
      (cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0 M ;; true\<^sub>r\<^esub> npre\<^sub>R Q \<or> 
      npre\<^sub>R P \<parallel>\<^bsub>N\<^sub>0 M ;; true\<^sub>r\<^esub> npre\<^sub>R Q)"
    (is "_ = ((?C1 :: _ pred) \<or> ?C2 \<or> ?C3 \<or> ?C4)")    
    by (simp add: JL1 JL2 JL3 usubst)
  also have "... = 
      ((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>[0:ok\<^sup>< \<leadsto> True, 1:ok\<^sup>< \<leadsto> True] \<dagger> M\<^sub>1 M\<lbrakk>True/ok\<^sup>>\<rbrakk>\<^esub> (cmt\<^sub>s \<dagger> Q) \<or> 
        npre\<^sub>R P \<parallel>\<^bsub>N\<^sub>0 M ;; true\<^sub>r\<^esub> (cmt\<^sub>s \<dagger> Q) \<or> 
        (cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>N\<^sub>0 M ;; true\<^sub>r\<^esub> npre\<^sub>R Q)"
  proof -
    from assms have "P\<^sup>t \<sqsubseteq> P\<^sup>f"
      by (metis H2_equiv Healthy_def RD2_def)
    hence "(cmt\<^sub>s \<dagger> P) \<sqsubseteq> (pre\<^sub>s \<dagger> P)"
      by (pred_auto)
    hence "?C3 \<sqsubseteq> ?C4"
      by (simp add: par_by_merge_mono)
    thus ?thesis
      by (simp add: pred_ba.sup_absorb1)
  qed
  finally show ?thesis
    by (simp add: JL4 usubst, pred_simp)
qed

lemma parallel_commitment_lemma_2:
  assumes "P is RD2"
  shows "cmt\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) =
         (((cmt\<^sub>s \<dagger> P) \<parallel>\<^bsub>(ok\<^sup>> \<and> N\<^sub>0 M) ;; II\<^sub>R\<^sup>t\<^esub> (cmt\<^sub>s \<dagger> Q)) \<or> pre\<^sub>s \<dagger> (P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q))"
  by (simp add: parallel_commitment_lemma_1 assms parallel_assm_lemma, pred_simp)
    
lemma parallel_commitment_lemma_3:
  "M is R1m \<Longrightarrow> (ok\<^sup>> \<and> N\<^sub>0 M) ;; II\<^sub>R\<^sup>t is R1m"
  by (pred_simp, blast)  

lemma parallel_commitment:
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "cmt\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) \<longrightarrow>\<^sub>r cmt\<^sub>R(P) \<parallel>\<^bsub>(ok\<^sup>> \<and> N\<^sub>0 M) ;; II\<^sub>R\<^sup>t\<^esub> cmt\<^sub>R(Q))"
  by (simp add: parallel_commitment_lemma_2 parallel_commitment_lemma_3 Healthy_if assms cmt\<^sub>R_def pre\<^sub>s_SRD closure rea_impl_def pred_ba.sup_commute unrest)  
  
theorem parallel_reactive_design:
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = \<^bold>R\<^sub>s(
    (\<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q)) \<and>
     \<not>\<^sub>r (cmt\<^sub>R(P) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (\<not>\<^sub>r pre\<^sub>R(Q)))) \<turnstile>
    (cmt\<^sub>R(P) \<parallel>\<^bsub>(ok\<^sup>> \<and> N\<^sub>0 M) ;; II\<^sub>R\<^sup>t\<^esub> cmt\<^sub>R(Q)))" (is "?lhs = ?rhs")
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = \<^bold>R\<^sub>s(pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) \<turnstile> cmt\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q))"
    by (metis Healthy_def NSRD_is_SRD SRD_as_reactive_design assms(1) assms(2) assms(3) par_rdes_NSRD)
  also have "... = ?rhs"
    by (simp add: parallel_assm parallel_commitment design_export_spec assms, pred_auto)
  finally show ?thesis .
qed

lemma parallel_pericondition_lemma1:
  "(ok\<^sup>> \<and> P) ;; II\<^sub>R\<lbrakk>True,True/ok\<^sup>>, wait\<^sup>>\<rbrakk> = (\<exists> st\<^sup>> \<Zspot> P)\<lbrakk>True,True/ok\<^sup>>,wait\<^sup>>\<rbrakk>"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (ok\<^sup>> \<and> P) ;; (\<exists> st\<^sup>< \<Zspot> II)\<lbrakk>True,True/ok\<^sup>>, wait\<^sup>>\<rbrakk>"
    by (pred_simp, blast)
  also have "... = ?rhs"
    by (pred_auto)
  finally show ?thesis .
qed

lemma subst_ex_out [usubst]: "\<lbrakk> mwb_lens x; $x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> (\<exists> x \<Zspot> P) = (\<exists> x \<Zspot> \<sigma> \<dagger> P)"
  by (expr_simp)

lemma parallel_pericondition_lemma2:
  assumes "M is RDM"
  shows "(\<exists> st\<^sup>> \<Zspot> N\<^sub>0(M))\<lbrakk>True,True/ok\<^sup>>, wait\<^sup>>\<rbrakk> = (($0:wait\<^sup>< \<or> $1:wait\<^sup><)\<^sub>e \<and> (\<exists> st\<^sup>> \<Zspot> M))"
proof -
  have "(\<exists> st\<^sup>> \<Zspot> N\<^sub>0(M))\<lbrakk>True,True/ok\<^sup>>, wait\<^sup>>\<rbrakk> = (\<exists> st\<^sup>> \<Zspot> (($0:wait\<^sup>< \<or> $1:wait\<^sup><) \<and> $tr\<^sup>> \<ge> $<:tr\<^sup><)\<^sub>e \<and> RDM(M))"
    by (simp add: usubst unrest nmerge_rd0_def ex_unrest Healthy_if R1m_def assms)
  also have "... = (\<exists> st\<^sup>> \<Zspot> ($0:wait\<^sup>< \<or> $1:wait\<^sup><)\<^sub>e \<and> RDM M)"
    by (pred_simp, blast)
  also have "... = (($0:wait\<^sup>< \<or> $1:wait\<^sup><)\<^sub>e \<and> (\<exists> st\<^sup>> \<Zspot> RDM M))"
    by (pred_auto)
  finally show ?thesis
    by (simp add: Healthy_if assms)
qed

lemma parallel_pericondition_lemma3:
  "(($0:wait\<^sup>< \<or> $1:wait\<^sup><)\<^sub>e \<and> (\<exists> st\<^sup>> \<Zspot> M)) = ((($0:wait\<^sup>< \<and> $1:wait\<^sup><)\<^sub>e \<and> (\<exists> st\<^sup>> \<Zspot> M)) \<or> ((\<not> $0:wait\<^sup>< \<and> $1:wait\<^sup><)\<^sub>e \<and> (\<exists> st\<^sup>> \<Zspot> M)) \<or> (($0:wait\<^sup>< \<and> \<not> $1:wait\<^sup><)\<^sub>e \<and> (\<exists> st\<^sup>> \<Zspot> M)))"
  by (pred_auto)

declare [[show_types]]

term "\<lambda> s. s \<oplus>\<^sub>L s' on x"

lemma subst_ext_lens_apply: "\<lbrakk> mwb_lens a; -$a \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> (a\<^sup>\<up> \<circ>\<^sub>s \<sigma>) \<dagger> P = ((\<sigma> \<down>\<^sub>s a) \<dagger> P) \<up> a"
  by (expr_simp, simp add: lens_override_def scene_override_commute)

lemma unrest_subst_upd_compl [unrest]: "\<lbrakk> vwb_lens x; y \<subseteq>\<^sub>L x; -$x \<sharp> (e)\<^sub>e; -$x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> -$x \<sharp>\<^sub>s \<sigma>(y \<leadsto> e)"
  by (expr_auto, simp add: lens_override_def scene_override_commute)
  
lemma varl_sub_merge_left [simp]: "vwb_lens x \<Longrightarrow> (0:x\<^sup>>)\<^sub>v \<subseteq>\<^sub>L U0\<alpha>"
  by (metis U0\<alpha>_comp_out_var comp_vwb_lens lens_comp_lb ns_alpha_def snd_vwb_lens)

lemma varr_sub_merge_right [simp]: "vwb_lens x \<Longrightarrow> (1:x\<^sup>>)\<^sub>v \<subseteq>\<^sub>L U1\<alpha>"
  by (metis U1\<alpha>_comp_out_var comp_vwb_lens ns_alpha_def snd_vwb_lens sublens_def)

lemma [usubst]: "(U0\<alpha>\<^sup>\<up> \<circ>\<^sub>s [0:wait\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright>]) \<dagger> P = ([wait\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright>] \<dagger> P) \<up> U0\<alpha>"
  by (pred_auto)

lemma [usubst]: "(U1\<alpha>\<^sup>\<up> \<circ>\<^sub>s [0:wait\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright>]) \<dagger> P = P \<up> U1\<alpha>"
  by (pred_auto)

lemma [usubst]: "(U0\<alpha>\<^sup>\<up> \<circ>\<^sub>s [1:wait\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright>]) \<dagger> P = P \<up> U0\<alpha>"
  by (pred_auto)

lemma [usubst]: "(U1\<alpha>\<^sup>\<up> \<circ>\<^sub>s [1:wait\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright>]) \<dagger> P = ([wait\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright>] \<dagger> P) \<up> U1\<alpha>"
  by (pred_auto)

lemma seqr_right_one_point_false:
  assumes "vwb_lens x"
  shows "(P ;; ((\<not>$x\<^sup><)\<^sub>e \<and> Q)) = (P\<lbrakk>False/x\<^sup>>\<rbrakk> ;; Q\<lbrakk>False/x\<^sup><\<rbrakk>)"
  using assms by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma parallel_pericondition [rdes]:
  fixes M :: "('s,'t::trace,'\<alpha>) rsp merge"
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "peri\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<longrightarrow>\<^sub>r peri\<^sub>R(P) \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> peri\<^sub>R(Q)
                                                  \<or> post\<^sub>R(P) \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> peri\<^sub>R(Q)
                                                  \<or> peri\<^sub>R(P) \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> post\<^sub>R(Q))"
proof -
  have "peri\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) =
        (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<longrightarrow>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>(ok\<^sup>> \<and> N\<^sub>0 M) ;; II\<^sub>R\<lbrakk>True,True/ok\<^sup>>, wait\<^sup>>\<rbrakk>\<^esub> cmt\<^sub>R Q)"
    by (simp add: peri_cmt_def parallel_commitment SRD_healths assms usubst unrest assms)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<longrightarrow>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>(\<exists> st\<^sup>> \<Zspot> N\<^sub>0 M)\<lbrakk>True,True/ok\<^sup>>, wait\<^sup>>\<rbrakk>\<^esub> cmt\<^sub>R Q)"
    by (simp add: parallel_pericondition_lemma1)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<longrightarrow>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>($0:wait\<^sup>< \<or> $1:wait\<^sup><)\<^sub>e \<and> (\<exists> st\<^sup>> \<Zspot> M)\<^esub> cmt\<^sub>R Q)"
    by (simp add: parallel_pericondition_lemma2 assms)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<longrightarrow>\<^sub>r ((\<lceil>cmt\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>cmt\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (($0:wait\<^sup><)\<^sub>e \<and> ($1:wait\<^sup><)\<^sub>e \<and> (\<exists> st\<^sup>> \<Zspot> M))
                                       \<or> (\<lceil>cmt\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>cmt\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; ((\<not> $0:wait\<^sup><)\<^sub>e \<and> ($1:wait\<^sup><)\<^sub>e \<and> (\<exists> st\<^sup>> \<Zspot> M))
                                       \<or> (\<lceil>cmt\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>cmt\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; ((($0:wait\<^sup><)\<^sub>e \<and> (\<not> $1:wait\<^sup><)\<^sub>e \<and> (\<exists> st\<^sup>> \<Zspot> M)))))"
    by (simp add: par_by_merge_alt_def parallel_pericondition_lemma3 seqr_or_distr, pred_simp)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<longrightarrow>\<^sub>r ((\<lceil>peri\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (\<exists> st\<^sup>> \<Zspot> M)
                                       \<or> (\<lceil>post\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (\<exists> st\<^sup>> \<Zspot> M)
                                       \<or> (\<lceil>peri\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (\<exists> st\<^sup>> \<Zspot> M)))"
    by (simp add: seqr_right_one_point_true seqr_right_one_point_false cmt\<^sub>R_def post\<^sub>R_def peri\<^sub>R_def usubst_eval usubst unrest assms)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<longrightarrow>\<^sub>r peri\<^sub>R(P) \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> peri\<^sub>R(Q)
                                       \<or> post\<^sub>R(P) \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> peri\<^sub>R(Q)
                                       \<or> peri\<^sub>R(P) \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> post\<^sub>R(Q))"
    by (simp add: par_by_merge_alt_def)
  finally show ?thesis .
qed

lemma parallel_postcondition_lemma1:
  "(ok\<^sup>> \<and> P) ;; II\<^sub>R\<lbrakk>True,False/ok\<^sup>>,wait\<^sup>>\<rbrakk> = P\<lbrakk>True,False/ok\<^sup>>,wait\<^sup>>\<rbrakk>"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (ok\<^sup>> \<and> P) ;; II\<lbrakk>True,False/ok\<^sup>>, wait\<^sup>>\<rbrakk>"
    by (pred_simp, blast)
  also have "... = ?rhs"
    by (pred_auto)
  finally show ?thesis .
qed

lemma parallel_postcondition_lemma2:
  assumes "M is RDM"
  shows "(N\<^sub>0(M))\<lbrakk>True,False/ok\<^sup>>,wait\<^sup>>\<rbrakk> = ((\<not> $0:wait\<^sup>< \<and> \<not> $1:wait\<^sup><)\<^sub>e \<and> M)"
proof -
  have "(N\<^sub>0(M))\<lbrakk>True,False/ok\<^sup>>,wait\<^sup>>\<rbrakk> = ((\<not> $0:wait\<^sup>< \<and> \<not> $1:wait\<^sup>< \<and> $tr\<^sup>> \<ge> $<:tr\<^sup><)\<^sub>e \<and> RDM M)"
    by (simp add: usubst_eval usubst unrest nmerge_rd0_def ex_unrest Healthy_if R1m_def assms)
  also have "... = ((\<not> $0:wait\<^sup>< \<and> \<not> $1:wait\<^sup><)\<^sub>e \<and> RDM M)"
    by (pred_simp, blast)    
  finally show ?thesis by (simp add: Healthy_if assms)
qed

lemma parallel_postcondition [rdes]:
  fixes M :: "('s,'t::trace,'\<alpha>) rsp merge"
  assumes "P is SRD" "Q is SRD" "M is RDM"
  shows "post\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<longrightarrow>\<^sub>r post\<^sub>R(P) \<parallel>\<^bsub>M\<^esub> post\<^sub>R(Q))"
proof -
  have "post\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) =
        (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<longrightarrow>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>(ok\<^sup>> \<and> N\<^sub>0 M) ;; II\<^sub>R\<lbrakk>True,False/ok\<^sup>>, wait\<^sup>>\<rbrakk>\<^esub> cmt\<^sub>R Q)"
    by (simp add: post_cmt_def parallel_commitment assms usubst unrest SRD_healths)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<longrightarrow>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>((\<not> $0:wait\<^sup><)\<^sub>e \<and> (\<not> $1:wait\<^sup><)\<^sub>e \<and> M)\<^esub> cmt\<^sub>R Q)"
    by (simp add: parallel_postcondition_lemma1 parallel_postcondition_lemma2 assms, pred_simp)
  also have "... = (pre\<^sub>R (P \<parallel>\<^bsub>M\<^sub>R M\<^esub> Q) \<longrightarrow>\<^sub>r post\<^sub>R P \<parallel>\<^bsub>M\<^esub> post\<^sub>R Q)"
    by (simp add: par_by_merge_alt_def seqr_right_one_point_false seqr_assoc usubst unrest cmt\<^sub>R_def post\<^sub>R_def assms)
  finally show ?thesis .
qed

lemma parallel_precondition_lemma:
  fixes M :: "('s,'t::trace,'\<alpha>) rsp merge"
  assumes "P is NSRD" "Q is NSRD" "M is RDM"
  shows "(\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q) =
         ((\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> peri\<^sub>R Q \<or> (\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> post\<^sub>R Q)"
proof -
  have "((\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q)) =
        ((\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> (peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q)))"
    by (simp add: wait'_cond_peri_post_cmt)
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R(P)\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q)\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; N\<^sub>0(M) ;; R1(true))"
    by (simp add: par_by_merge_alt_def)
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R(P)\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R(Q)\<rceil>\<^sub>1 \<triangleleft> $1:wait\<^sup>< \<triangleright> \<lceil>post\<^sub>R(Q)\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; N\<^sub>0(M) ;; R1(true))"
    by (simp add: wait'_cond_def alpha)
  also have "... = (((\<lceil>\<not>\<^sub>r pre\<^sub>R(P)\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R(Q)\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) \<triangleleft> $1:wait\<^sup>< \<triangleright> (\<lceil>\<not>\<^sub>r pre\<^sub>R(P)\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R(Q)\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e)) ;; N\<^sub>0(M) ;; R1(true))"
    (is "(?P ;; _) = (?Q ;; _)")
  proof -
    have "?P = ?Q"
      by (pred_auto)
    thus ?thesis by simp
  qed
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e)\<lbrakk>True/$1:wait\<^sup><\<rbrakk> ;; (N\<^sub>0 M ;; R1 true)\<lbrakk>True/$1:wait\<rbrakk> \<or>
                    (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e)\<lbrakk>False/$1:wait\<^sup><\<rbrakk> ;; (N\<^sub>0 M ;; R1 true)\<lbrakk>False/$1:wait\<rbrakk>)"
    by (simp add: cond_inter_var_split)
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; N\<^sub>0 M\<lbrakk>True/$1:wait\<rbrakk> ;; R1 true \<or>
                    (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; N\<^sub>0 M\<lbrakk>False/$1:wait\<rbrakk> ;; R1 true)"
    by (simp add: usubst unrest)
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (wait\<^sup>> \<and> M) ;; R1 true \<or>
                    (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (wait\<^sup>> =\<^sub>u $0:wait \<and> M) ;; R1 true)"
  proof -
    have "($tr\<acute> \<ge>\<^sub>u $<:tr \<and> M) = M"
      using RDM_R1m[OF assms(3)]
      by (simp add: Healthy_def R1m_def conj_comm)
    thus ?thesis
      by (simp add: nmerge_rd0_def unrest assms closure ex_unrest usubst)
  qed
  also have "... = ((\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; M ;; R1 true \<or>
                    (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; M ;; R1 true)"
    (is "(?P\<^sub>1 \<or>\<^sub>p ?P\<^sub>2) = (?Q\<^sub>1 \<or> ?Q\<^sub>2)")
  proof -
    have "?P\<^sub>1 = (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>peri\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (M \<and> wait\<^sup>>) ;; R1 true"
      by (simp add: conj_comm)
    hence 1: "?P\<^sub>1 = ?Q\<^sub>1"
      by (simp add: seqr_left_one_point_true seqr_left_one_point_false add: unrest usubst closure assms)
    have "?P\<^sub>2 = ((\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (M \<and> wait\<^sup>>) ;; R1 true \<or>
                 (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> \<lceil>post\<^sub>R Q\<rceil>\<^sub>1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; (M \<and> \<not> wait\<^sup>>) ;; R1 true)"
      by (subst seqr_bool_split[of "wait ;\<^sub>L mrg_left"], simp_all add: usubst unrest assms closure conj_comm)
    hence 2: "?P\<^sub>2 = ?Q\<^sub>2"
      by (simp add: seqr_left_one_point_true seqr_left_one_point_false unrest usubst closure assms)
    from 1 2 show ?thesis by simp
  qed
  also have "... = ((\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> peri\<^sub>R Q \<or> (\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> post\<^sub>R Q)"
    by (simp add: par_by_merge_alt_def)
  finally show ?thesis .
qed

lemma swap_nmerge_rd0:
  "swap\<^sub>m ;; N\<^sub>0(M) = N\<^sub>0(swap\<^sub>m ;; M)"
  by (pred_auto, meson+)

lemma SymMerge_nmerge_rd0 [closure]:
  "M is SymMerge \<Longrightarrow> N\<^sub>0(M) is SymMerge"
  by (pred_auto, meson+)
    
lemma swap_merge_rd':
  "swap\<^sub>m ;; N\<^sub>R(M) = N\<^sub>R(swap\<^sub>m ;; M)"
  by (pred_auto; blast)
    
lemma swap_merge_rd:
  "swap\<^sub>m ;; M\<^sub>R(M) = M\<^sub>R(swap\<^sub>m ;; M)"
  by (simp add: merge_rd_def seqr_assoc[THEN sym] swap_merge_rd')

lemma SymMerge_merge_rd [closure]:
  "M is SymMerge \<Longrightarrow> M\<^sub>R(M) is SymMerge"
  by (simp add: Healthy_def swap_merge_rd)
    
lemma nmerge_rd1_merge3:
  assumes "M is RDM"
  shows "\<^bold>M3(N\<^sub>1(M)) = (ok\<^sup>> =\<^sub>u ($0:ok \<and> $1:0:ok \<and> $1:1:ok) \<and> 
                      wait\<^sup>> =\<^sub>u ($0:wait \<or> $1:0:wait \<or> $1:1:wait) \<and> 
                      \<^bold>M3(M))"
proof -
  have "\<^bold>M3(N\<^sub>1(M)) = \<^bold>M3(ok\<^sup>> =\<^sub>u ($0:ok \<and> $1:ok) \<and>
                       wait\<^sup>> =\<^sub>u ($0:wait\<^sup>< \<or> $1:wait\<^sup><)\<^sub>e \<and> 
                       ($<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e \<and> 
                       (\<exists> {$0:ok, $1:ok, $<:ok, ok\<^sup>>, $0:wait, $1:wait, $<:wait, wait\<^sup>>} \<bullet> RDM(M)))"
    by (simp add: nmerge_rd1_def nmerge_rd0_def assms Healthy_if)
  also have "... = \<^bold>M3(ok\<^sup>> =\<^sub>u ($0:ok \<and> $1:ok) \<and> wait\<^sup>> =\<^sub>u ($0:wait\<^sup>< \<or> $1:wait\<^sup><)\<^sub>e \<and> RDM(M))"
    by (pred_auto; blast)
  also have "... = (ok\<^sup>> =\<^sub>u ($0:ok \<and> $1:0:ok \<and> $1:1:ok) \<and> wait\<^sup>> =\<^sub>u ($0:wait \<or> $1:0:wait \<or> $1:1:wait) \<and> \<^bold>M3(RDM(M)))"  
    by (pred_auto; blast)
  also have "... = (ok\<^sup>> =\<^sub>u ($0:ok \<and> $1:0:ok \<and> $1:1:ok) \<and> wait\<^sup>> =\<^sub>u ($0:wait \<or> $1:0:wait \<or> $1:1:wait) \<and> \<^bold>M3(M))"
    by (simp add: assms Healthy_if)
  finally show ?thesis .
qed

lemma nmerge_rd_merge3:
  "\<^bold>M3(N\<^sub>R(M)) = (\<exists> <:st\<^sup>< \<Zspot> ($\<^bold>v\<^sup>> = $<\<^sup><)\<^sub>e:\<^bold>v) \<triangleleft> $<:wait \<triangleright> \<^bold>M3(N\<^sub>1 M) \<triangleleft> $<:ok \<triangleright> (($<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e)"
  by (pred_auto; blast) (* 15 seconds *)

lemma AssocMerge_nmerge_rd:
  assumes "M is RDM" "AssocMerge M"
  shows "AssocMerge(N\<^sub>R(M))"
proof -
  have 1:"\<^bold>M3(M) = rotate\<^sub>m ;; \<^bold>M3(M)"
    using assms by (simp add: AssocMerge_def)
  have "rotate\<^sub>m ;; (\<^bold>M3(N\<^sub>R(M))) = 
        rotate\<^sub>m ;;
        ((\<exists> <:st\<^sup>< \<Zspot> ($\<^bold>v\<^sup>> = $<\<^sup><)\<^sub>e:\<^bold>v) \<triangleleft> $<:wait \<triangleright>
            (ok\<^sup>> =\<^sub>u ($0:ok \<and> $1:0:ok \<and> $1:1:ok) \<and> wait\<^sup>> =\<^sub>u ($0:wait \<or> $1:0:wait \<or> $1:1:wait) \<and> \<^bold>M3(M)) \<triangleleft> $<:ok \<triangleright>
            (($<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e))"
    by (simp add: AssocMerge_def nmerge_rd_merge3 nmerge_rd1_merge3 assms)
  also have "... = 
        ((\<exists> <:st\<^sup>< \<Zspot> ($\<^bold>v\<^sup>> = $<\<^sup><)\<^sub>e:\<^bold>v) \<triangleleft> $<:wait \<triangleright>
            (ok\<^sup>> =\<^sub>u ($0:ok \<and> $1:0:ok \<and> $1:1:ok) \<and> wait\<^sup>> =\<^sub>u ($0:wait \<or> $1:0:wait \<or> $1:1:wait) \<and> (rotate\<^sub>m ;; \<^bold>M3(M))) \<triangleleft> $<:ok \<triangleright>
            (($<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e))"
    by (pred_auto; blast)
  also have "... = 
        ((\<exists> <:st\<^sup>< \<Zspot> ($\<^bold>v\<^sup>> = $<\<^sup><)\<^sub>e:\<^bold>v) \<triangleleft> $<:wait \<triangleright>
            (ok\<^sup>> =\<^sub>u ($0:ok \<and> $1:0:ok \<and> $1:1:ok) \<and> wait\<^sup>> =\<^sub>u ($0:wait \<or> $1:0:wait \<or> $1:1:wait) \<and> \<^bold>M3(M)) \<triangleleft> $<:ok \<triangleright>
            (($<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e))"
    using "1" by auto
  also have "... = \<^bold>M3(N\<^sub>R(M))"
    by (simp add: AssocMerge_def nmerge_rd_merge3 nmerge_rd1_merge3 assms)
  finally show ?thesis
    using AssocMerge_def by blast
qed

lemma swap_merge_RDM_closed [closure]:
  assumes "M is RDM" 
  shows "swap\<^sub>m ;; M is RDM"
proof -
  have "RDM(swap\<^sub>m ;; RDM(M)) = (swap\<^sub>m ;; RDM(M))"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_def' assms)
qed
  
lemma parallel_precondition:
  fixes M :: "('s,'t::trace,'\<alpha>) rsp merge"
  assumes "P is NSRD" "Q is NSRD" "M is RDM"
  shows "pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) =
          (\<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> peri\<^sub>R Q) \<and>
           \<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> post\<^sub>R Q) \<and>
           \<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R Q) \<parallel>\<^bsub>(swap\<^sub>m ;; M) ;; R1(true)\<^esub> peri\<^sub>R P) \<and>
           \<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R Q) \<parallel>\<^bsub>(swap\<^sub>m ;; M) ;; R1(true)\<^esub> post\<^sub>R P))"
proof -
  have a: "(\<not>\<^sub>r pre\<^sub>R(P)) \<parallel>\<^bsub>N\<^sub>0(M) ;; R1(true)\<^esub> cmt\<^sub>R(Q) =
           ((\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> peri\<^sub>R Q \<or> (\<not>\<^sub>r pre\<^sub>R P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> post\<^sub>R Q)"
    by (simp add: parallel_precondition_lemma assms)

  have b: "(\<not>\<^sub>r cmt\<^sub>R P \<parallel>\<^bsub>N\<^sub>0 M ;; R1 true\<^esub> (\<not>\<^sub>r pre\<^sub>R Q)) =
           (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(Q)) \<parallel>\<^bsub>N\<^sub>0(swap\<^sub>m ;; M) ;; R1(true)\<^esub> cmt\<^sub>R(P))"
    by (simp add: swap_nmerge_rd0[THEN sym] seqr_assoc[THEN sym] par_by_merge_def par_sep_swap)
  have c: "(\<not>\<^sub>r pre\<^sub>R(Q)) \<parallel>\<^bsub>N\<^sub>0(swap\<^sub>m ;; M) ;; R1(true)\<^esub> cmt\<^sub>R(P) =
           ((\<not>\<^sub>r pre\<^sub>R Q) \<parallel>\<^bsub>(swap\<^sub>m ;; M) ;; R1(true)\<^esub> peri\<^sub>R P \<or> (\<not>\<^sub>r pre\<^sub>R Q) \<parallel>\<^bsub>(swap\<^sub>m ;; M) ;; R1(true)\<^esub> post\<^sub>R P)"
    by (simp add: parallel_precondition_lemma closure assms)

  show ?thesis
    by (simp add: parallel_assm closure assms a b c, pred_auto)
qed

text \<open> Weakest Parallel Precondition \<close>

definition wrR :: 
  "('t::trace, '\<alpha>) hrel_rp \<Rightarrow> 
   ('t :: trace, '\<alpha>) rp merge \<Rightarrow> 
   ('t, '\<alpha>) hrel_rp \<Rightarrow> 
   ('t, '\<alpha>) hrel_rp" ("_ wr\<^sub>R'(_') _" [60,0,61] 61)
where [pred]: "Q wr\<^sub>R(M) P = (\<not>\<^sub>r ((\<not>\<^sub>r P) \<parallel>\<^bsub>M ;; R1(true)\<^esub> Q))"

lemma wrR_R1 [closure]: 
  "M is R1m \<Longrightarrow> Q wr\<^sub>R(M) P is R1"
  by (simp add: wrR_def closure)
    
lemma R2_rea_not: "R2(\<not>\<^sub>r P) = (\<not>\<^sub>r R2(P))"
  by (pred_auto)
        
lemma wrR_R2_lemma:
  assumes "P is R2" "Q is R2" "M is R2m"
  shows "((\<not>\<^sub>r P) \<parallel>\<^bsub>M\<^esub> Q) ;; R1(true\<^sub>h) is R2"
proof -
  have "(\<not>\<^sub>r P) \<parallel>\<^bsub>M\<^esub> Q is R2"
    by (simp add: closure assms)
  thus ?thesis
    by (simp add: closure)
qed
    
lemma wrR_R2 [closure]: 
  assumes "P is R2" "Q is R2" "M is R2m"
  shows "Q wr\<^sub>R(M) P is R2"
proof -
  have "((\<not>\<^sub>r P) \<parallel>\<^bsub>M\<^esub> Q) ;; R1(true\<^sub>h) is R2"
    by (simp add: wrR_R2_lemma assms)
  thus ?thesis
    by (simp add: wrR_def wrR_R2_lemma par_by_merge_seq_add closure) 
qed
 
lemma wrR_RR [closure]: 
  assumes "P is RR" "Q is RR" "M is RDM"
  shows "Q wr\<^sub>R(M) P is RR"
  apply (rule RR_intro)
  apply (simp_all add: unrest assms closure wrR_def rpred)
  apply (metis (no_types, lifting) Healthy_def' R1_R2c_commute R1_R2c_is_R2 R1_rea_not RDM_R2m 
               RR_implies_R2 assms(1) assms(2) assms(3) par_by_merge_seq_add rea_not_R2_closed 
               wrR_R2_lemma)
done
             
lemma wrR_RC [closure]: 
  assumes "P is RR" "Q is RR" "M is RDM"
  shows "(Q wr\<^sub>R(M) P) is RC"
  apply (rule RC_intro)
  apply (simp add: closure assms)
  apply (simp add: wrR_def rpred closure assms )
  apply (simp add: par_by_merge_def seqr_assoc)
done
    
lemma wppR_choice [wp]: "(P \<or> Q) wr\<^sub>R(M) R = (P wr\<^sub>R(M) R \<and> Q wr\<^sub>R(M) R)"
proof -
  have "(P \<or> Q) wr\<^sub>R(M) R = 
        (\<not>\<^sub>r ((\<not>\<^sub>r R) ;; U0 \<and> (P ;; U1 \<or> Q ;; U1) \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; M ;; true\<^sub>r)"
    by (simp add: wrR_def par_by_merge_def seqr_or_distl)
  also have "... = (\<not>\<^sub>r ((\<not>\<^sub>r R) ;; U0 \<and> P ;; U1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e \<or> (\<not>\<^sub>r R) ;; U0 \<and> Q ;; U1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; M ;; true\<^sub>r)"
    by (simp add: conj_disj_distr utp_pred_laws.inf_sup_distrib2)
  also have "... = (\<not>\<^sub>r (((\<not>\<^sub>r R) ;; U0 \<and> P ;; U1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; M ;; true\<^sub>r \<or> 
                        ((\<not>\<^sub>r R) ;; U0 \<and> Q ;; U1 \<and> ($<:\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)\<^sub>e) ;; M ;; true\<^sub>r))"    
    by (simp add: seqr_or_distl)
  also have "... = (P wr\<^sub>R(M) R \<and> Q wr\<^sub>R(M) R)"
    by (simp add: wrR_def par_by_merge_def)
  finally show ?thesis .
qed

lemma wppR_impl [wp]: "(P \<longrightarrow>\<^sub>r Q) wr\<^sub>R(M) R = ((\<not>\<^sub>r P) wr\<^sub>R(M) R \<and> Q wr\<^sub>R(M) R)"
  by (simp add: rea_impl_def wp)

lemma wppR_miracle [wp]: "false wr\<^sub>R(M) P = true\<^sub>r"
  by (simp add: wrR_def)

lemma wppR_true [wp]: "P wr\<^sub>R(M) true\<^sub>r = true\<^sub>r"
  by (simp add: wrR_def)

lemma parallel_precondition_wr [rdes]:
  assumes "P is NSRD" "Q is NSRD" "M is RDM"
  shows "pre\<^sub>R(P \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> Q) = (peri\<^sub>R(Q) wr\<^sub>R(M) pre\<^sub>R(P) \<and> post\<^sub>R(Q) wr\<^sub>R(M) pre\<^sub>R(P) \<and>
                              peri\<^sub>R(P) wr\<^sub>R(swap\<^sub>m ;; M) pre\<^sub>R(Q) \<and> post\<^sub>R(P) wr\<^sub>R(swap\<^sub>m ;; M) pre\<^sub>R(Q))"
  by (simp add: assms parallel_precondition wrR_def)

lemma rea_impl_merge_left: "(P \<longrightarrow>\<^sub>r Q) \<parallel>\<^bsub>M\<^esub> R = (((\<not>\<^sub>r P) \<parallel>\<^bsub>M\<^esub> R) \<or> (Q \<parallel>\<^bsub>M\<^esub> R))"
  by (simp add: rea_impl_def par_by_merge_or_left)

lemma rea_impl_merge_right: "P \<parallel>\<^bsub>M\<^esub> (Q \<longrightarrow>\<^sub>r R) = (P \<parallel>\<^bsub>M\<^esub> (\<not>\<^sub>r Q) \<or> P \<parallel>\<^bsub>M\<^esub> R)"
  by (simp add: rea_impl_def par_by_merge_or_right)

lemma parallel_pre_lemma:
  "((Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2) wr\<^sub>R(M) P\<^sub>1 \<and> (P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>2) \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2))
       = ((Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2) wr\<^sub>R(M) P\<^sub>1 \<and> P\<^sub>2 \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2))"
  apply (simp add: par_by_merge_alt_def)
  apply (pred_auto)
  apply (meson order_refl)
  apply (meson order_refl)
  apply blast
  apply blast
  apply blast
  apply blast
  done

lemma parallel_rdes_def [rdes_def]:
  assumes "P\<^sub>1 is RC" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RC" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
          "$st\<acute> \<sharp> P\<^sub>2" "$st\<acute> \<sharp> Q\<^sub>2"
          "M is RDM"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<parallel>\<^bsub>M\<^sub>R(M)\<^esub> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = 
         \<^bold>R\<^sub>s(((Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2) wr\<^sub>R(M) P\<^sub>1 \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>3) wr\<^sub>R(M) P\<^sub>1 \<and> 
              (P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>2) wr\<^sub>R(swap\<^sub>m ;; M) Q\<^sub>1 \<and> (P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>3) wr\<^sub>R(swap\<^sub>m ;; M) Q\<^sub>1) \<turnstile>
          (P\<^sub>2 \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub>  Q\<^sub>2 \<or>
           P\<^sub>3 \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> Q\<^sub>2 \<or> P\<^sub>2 \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> Q\<^sub>3) \<diamondop>
          (P\<^sub>3 \<parallel>\<^bsub>M\<^esub> Q\<^sub>3))" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^bold>R\<^sub>s (pre\<^sub>R ?lhs \<turnstile> peri\<^sub>R ?lhs \<diamondop> post\<^sub>R ?lhs)"
    by (simp add: SRD_reactive_tri_design assms closure)
  also have "... = 
         \<^bold>R\<^sub>s(((Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2) wr\<^sub>R(M) P\<^sub>1 \<and> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>3) wr\<^sub>R(M) P\<^sub>1 \<and> 
              (P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>2) wr\<^sub>R(swap\<^sub>m ;; M) Q\<^sub>1 \<and> (P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>3) wr\<^sub>R(swap\<^sub>m ;; M) Q\<^sub>1) \<turnstile>
          ((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>2) \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2) \<or>
           (P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>3) \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>2) \<or> (P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>2) \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>3)) \<diamondop>
          ((P\<^sub>1 \<longrightarrow>\<^sub>r P\<^sub>3) \<parallel>\<^bsub>M\<^esub> (Q\<^sub>1 \<longrightarrow>\<^sub>r Q\<^sub>3)))"
    (is "_ = \<^bold>R\<^sub>s( ?X 
               \<turnstile> (?Y\<^sub>1 \<or> ?Y\<^sub>2 \<or> ?Y\<^sub>3)
               \<diamondop> ?Z)")
    by (simp add: rdes closure unrest assms, pred_auto) 
  also have "... = \<^bold>R\<^sub>s(?X \<turnstile> ((?X \<and> ?Y\<^sub>1) \<or> (?X \<and> ?Y\<^sub>2) \<or> (?X \<and> ?Y\<^sub>3)) \<diamondop> (?X \<and> ?Z))"
    by (pred_auto)
  also have "... = \<^bold>R\<^sub>s(?X \<turnstile> ((?X \<and> P\<^sub>2 \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> Q\<^sub>2) \<or> (?X \<and> P\<^sub>3 \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> Q\<^sub>2) \<or> (?X \<and> P\<^sub>2 \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> Q\<^sub>3)) \<diamondop> (?X \<and> P\<^sub>3 \<parallel>\<^bsub>M\<^esub> Q\<^sub>3))"
  proof -
    have 1:"(?X \<and> ?Y\<^sub>1) = (?X \<and> P\<^sub>2 \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> Q\<^sub>2)"
      by (pred_auto, meson order_refl, meson order_refl, meson order_refl, blast+)
    have 2:"(?X \<and> ?Y\<^sub>2) = (?X \<and> P\<^sub>3 \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> Q\<^sub>2)"
      by (pred_auto, meson order_refl, meson order_refl, meson order_refl, blast+)
    have 3:"(?X \<and> ?Y\<^sub>3) = (?X \<and> P\<^sub>2 \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> M\<^esub> Q\<^sub>3)"
      by (pred_auto, meson order_refl, meson order_refl, meson order_refl, blast+)
    have 4:"(?X \<and> ?Z) = (?X \<and> P\<^sub>3 \<parallel>\<^bsub>M\<^esub> Q\<^sub>3)"
      by (pred_auto, meson order_refl, meson order_refl, meson order_refl, blast+)
    show ?thesis
      by (simp add: 1 2 3 4)
  qed
  also have "... = ?rhs"
    by (pred_auto)
  finally show ?thesis .
qed


lemma Miracle_parallel_left_zero:
  assumes "P is SRD" "M is RDM"
  shows "Miracle \<parallel>\<^sub>R\<^bsub>M\<^esub> P = Miracle"
proof -
  have "pre\<^sub>R(Miracle \<parallel>\<^sub>R\<^bsub>M\<^esub> P) = true\<^sub>r"
    by (simp add: parallel_assm wait'_cond_idem rdes closure assms)
  moreover hence "cmt\<^sub>R(Miracle \<parallel>\<^sub>R\<^bsub>M\<^esub> P) = false"
    by (simp add: rdes closure wait'_cond_idem SRD_healths assms)
  ultimately have "Miracle \<parallel>\<^sub>R\<^bsub>M\<^esub> P = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false)"
    by (metis NSRD_iff SRD_reactive_design_alt assms par_rdes_NSRD srdes_theory.weak.top_closed)
  thus ?thesis
    by (simp add: Miracle_def R1_design_R1_pre)
qed

lemma Miracle_parallel_right_zero:
  assumes "P is SRD" "M is RDM"
  shows "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Miracle = Miracle"
proof -
  have "pre\<^sub>R(P \<parallel>\<^sub>R\<^bsub>M\<^esub> Miracle) = true\<^sub>r"
    by (simp add: wait'_cond_idem parallel_assm rdes closure assms)
  moreover hence "cmt\<^sub>R(P \<parallel>\<^sub>R\<^bsub>M\<^esub> Miracle) = false"
    by (simp add: wait'_cond_idem rdes closure SRD_healths assms)
  ultimately have "P \<parallel>\<^sub>R\<^bsub>M\<^esub> Miracle = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false)"
    by (metis NSRD_iff SRD_reactive_design_alt assms par_rdes_NSRD srdes_theory.weak.top_closed)
  thus ?thesis
    by (simp add: Miracle_def R1_design_R1_pre)
qed

subsection \<open> Example basic merge \<close>
  
definition BasicMerge :: "(('s, 't::trace, unit) rsp) merge" ("N\<^sub>B") where
[pred]: "BasicMerge = (($<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e \<and> $tr\<acute> - $<:tr =\<^sub>u $0:tr - $<:tr \<and> $tr\<acute> - $<:tr =\<^sub>u $1:tr - $<:tr \<and> $st\<acute> =\<^sub>u $<:st)"

abbreviation rbasic_par ("_ \<parallel>\<^sub>B _" [85,86] 85) where
"P \<parallel>\<^sub>B Q \<equiv> P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>B)\<^esub> Q"

lemma BasicMerge_RDM [closure]: "N\<^sub>B is RDM"
  by (rule RDM_intro, (pred_auto)+)

lemma BasicMerge_SymMerge [closure]: 
  "N\<^sub>B is SymMerge"
  by (pred_auto)
   
lemma BasicMerge'_calc:
  assumes "$ok\<^sup>> \<sharp> P" "$wait\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$wait\<^sup>> \<sharp> Q" "P is R2" "Q is R2"
  shows "P \<parallel>\<^bsub>N\<^sub>B\<^esub> Q = ((\<exists> st\<^sup>> \<Zspot> P) \<and> (\<exists> st\<^sup>> \<Zspot> Q) \<and> $st\<acute> =\<^sub>u $st)"
  using assms
proof -
  have P:"(\<exists> {ok\<^sup>>,wait\<^sup>>} \<bullet> R2(P)) = P" (is "?P' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms)
  have Q:"(\<exists> {ok\<^sup>>,wait\<^sup>>} \<bullet> R2(Q)) = Q" (is "?Q' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms)
  have "?P' \<parallel>\<^bsub>N\<^sub>B\<^esub> ?Q' = ((\<exists> st\<^sup>> \<Zspot> ?P') \<and> (\<exists> st\<^sup>> \<Zspot> ?Q') \<and> $st\<acute> =\<^sub>u $st)"
    by (simp add: par_by_merge_alt_def, pred_auto, blast+)
  thus ?thesis
    by (simp add: P Q)
qed 
  
subsection \<open> Simple parallel composition \<close>

definition rea_design_par ::
  "('s, 't::trace, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" (infixr "\<parallel>\<^sub>R" 85)
where [pred]: "P \<parallel>\<^sub>R Q = \<^bold>R\<^sub>s((pre\<^sub>R(P)  \<and> pre\<^sub>R(Q)) \<turnstile> (cmt\<^sub>R(P) \<and> cmt\<^sub>R(Q)))"

lemma RHS_design_par:
  assumes
    "$ok\<^sup>> \<sharp> P\<^sub>1" "$ok\<^sup>> \<sharp> P\<^sub>2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2))"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) =
        \<^bold>R\<^sub>s(P\<^sub>1\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<turnstile> Q\<^sub>1\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<turnstile> Q\<^sub>2\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>)"
    by (simp add: RHS_design_ok_wait)

  also from assms
  have "... =
        \<^bold>R\<^sub>s((R1 (R2c (P\<^sub>1)) \<and> R1 (R2c (P\<^sub>2)))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk> \<turnstile>
           (R1 (R2c (P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2c (P\<^sub>2 \<Rightarrow> Q\<^sub>2)))\<lbrakk>True,False/ok\<^sup><,wait\<^sup><\<rbrakk>)"
      apply (simp add: rea_design_par_def rea_pre_RHS_design rea_cmt_RHS_design usubst unrest assms)
      apply (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp)
      using assms apply (pred_auto)
  done
  also have "... =
        \<^bold>R\<^sub>s((R2c(P\<^sub>1) \<and> R2c(P\<^sub>2)) \<turnstile>
           (R1 (R2s (P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2s (P\<^sub>2 \<Rightarrow> Q\<^sub>2))))"
    by (metis (no_types, opaque_lifting) R1_R2s_R2c R1_conj R1_design_R1_pre RHS_design_ok_wait)
  also have "... =
        \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (R1 (R2s (P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2s (P\<^sub>2 \<Rightarrow> Q\<^sub>2))))"
    by (simp add: R2c_R3h_commute R2c_and R2c_design R2c_idem R2c_not RHS_def)
  also have "... = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> ((P\<^sub>1 \<Rightarrow> Q\<^sub>1) \<and> (P\<^sub>2 \<Rightarrow> Q\<^sub>2)))"
    by (metis (no_types, lifting) R1_conj R2s_conj RHS_design_export_R1 RHS_design_export_R2s)
  also have "... = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, pred_auto)
  finally show ?thesis .
qed

lemma RHS_tri_design_par:
  assumes "$ok\<^sup>> \<sharp> P\<^sub>1" "$ok\<^sup>> \<sharp> P\<^sub>2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (R\<^sub>1 \<and> R\<^sub>2))"
  by (simp add: RHS_design_par assms unrest wait'_cond_conj_exchange)

lemma RHS_tri_design_par_RR [rdes_def]:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (R\<^sub>1 \<and> R\<^sub>2))"
  by (simp add: RHS_tri_design_par unrest assms)

lemma RHS_comp_assoc: 
  assumes "P is NSRD" "Q is NSRD" "R is NSRD"
  shows "(P \<parallel>\<^sub>R Q) \<parallel>\<^sub>R R = P \<parallel>\<^sub>R Q \<parallel>\<^sub>R R"
  by (rdes_eq cls: assms)

end