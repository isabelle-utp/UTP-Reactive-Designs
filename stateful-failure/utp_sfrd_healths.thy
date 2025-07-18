section \<open> Stateful-Failure Healthiness Conditions \<close>

theory utp_sfrd_healths
  imports utp_sfrd_rel
begin

section \<open> Definitions \<close>

text \<open> We here define extra healthiness conditions for stateful-failure reactive designs. \<close>

abbreviation CSP1 :: "(('\<sigma>, '\<phi>) sfrd \<times> ('\<sigma>, '\<phi>) sfrd) health"
where "CSP1(P) \<equiv> RD1(P)"

abbreviation CSP2 :: "(('\<sigma>, '\<phi>) sfrd \<times> ('\<sigma>, '\<phi>) sfrd) health"
where "CSP2(P) \<equiv> RD2(P)"

abbreviation CSP :: "(('\<sigma>, '\<phi>) sfrd \<times> ('\<sigma>, '\<phi>) sfrd) health"
where "CSP(P) \<equiv> SRD(P)"

definition STOP :: "'\<phi> process" where
[pred]: "STOP = CSP1(ok\<^sup>> \<and> R3c(($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"

definition SKIP :: "'\<phi> process" where
[pred]: "SKIP = \<^bold>R\<^sub>s(\<exists> ref\<^sup>< \<Zspot> CSP1(II))"

definition Stop :: "('\<sigma>, '\<phi>) action" where
[pred]: "Stop = \<^bold>R\<^sub>s(true \<turnstile> (($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<and> wait\<^sup>>))"

definition Skip :: "('\<sigma>, '\<phi>) action" where
[pred]: "Skip = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<^sup>> = $tr\<^sup>< \<and> \<not> $wait\<^sup>> \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e)"

definition CSP3 :: "(('\<sigma>, '\<phi>) sfrd \<times> ('\<sigma>, '\<phi>) sfrd) health" where
[pred]: "CSP3(P) = (Skip ;; P)"

definition CSP4 :: "(('\<sigma>, '\<phi>) sfrd \<times> ('\<sigma>, '\<phi>) sfrd) health" where
[pred]: "CSP4(P) = (P ;; Skip)"

definition NCSP :: "(('\<sigma>, '\<phi>) sfrd \<times> ('\<sigma>, '\<phi>) sfrd) health" where
[pred]: "NCSP = CSP3 \<circ> CSP4 \<circ> CSP"

text \<open> Productive and normal processes \<close>

abbreviation "PCSP \<equiv> Productive \<circ> NCSP"

text \<open> Instantaneous and normal processes \<close>

abbreviation "ICSP \<equiv> ISRD1 \<circ> NCSP"

subsection \<open> Healthiness condition properties \<close>

text \<open> @{term SKIP} is the same as @{term Skip}, and @{term STOP} is the same as @{term Stop},
  when we consider stateless CSP processes. This is because any reference to the @{term st}
  variable degenerates when the alphabet type coerces its type to be empty. We therefore
  need not consider @{term SKIP} and @{term STOP} actions. \<close>

theorem SKIP_is_Skip [simp]: "SKIP = Skip"
  by (pred_auto)

theorem STOP_is_Stop [simp]: "STOP = Stop"
  by (pred_auto)

theorem Skip_UTP_form: "Skip = \<^bold>R\<^sub>s(\<exists> ref\<^sup>< \<Zspot> CSP1(II))"
  by (pred_auto)

lemma Skip_is_CSP [closure]:
  "Skip is CSP"
  by (simp add: Skip_def RHS_design_is_SRD unrest unrest_ssubst_expr usubst usubst_eval)

lemma Skip_RHS_tri_design: 
  "Skip = \<^bold>R\<^sub>s(true \<turnstile> (false \<diamondop> ($tr\<^sup>> = $tr\<^sup>< \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e))"
  by (pred_auto)

lemma Skip_RHS_tri_design' [rdes_def]: 
  "Skip = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> (false \<diamondop> \<Phi>(True,[\<leadsto>],\<guillemotleft>[]\<guillemotright>)))"
  by (pred_auto)

(*
lemma Skip_frame [frame]: "vwb_lens a \<Longrightarrow> a:[Skip]\<^sub>R\<^sup>+ = Skip"
  by (rdes_eq)
*)

lemma Stop_is_CSP [closure]:
  "Stop is CSP"
  by (simp add: Stop_def RHS_design_is_SRD unrest)

lemma Stop_RHS_tri_design: "Stop = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e \<diamondop> false)"
  by (pred_auto)

lemma Stop_RHS_rdes_def [rdes_def]: "Stop = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> \<E>(True,[],{}) \<diamondop> false)"
  by (pred_auto)

lemma preR_Skip [rdes]: "pre\<^sub>R(Skip) = true\<^sub>r"
  by (pred_auto)

lemma periR_Skip [rdes]: "peri\<^sub>R(Skip) = false"
  by (pred_auto)

lemma postR_Skip [rdes]: "post\<^sub>R(Skip) = \<Phi>(True,[\<leadsto>],[])"
  by (pred_auto)

lemma Productive_Stop [closure]:
  "Stop is Productive"
  by (simp add: Stop_RHS_tri_design Healthy_def Productive_RHS_design_form unrest closure)

find_theorems peri\<^sub>R CRR

lemma Skip_left_lemma:
  assumes "P is CSP"
  shows "Skip ;; P = \<^bold>R\<^sub>s ((\<forall> ref\<^sup>< \<Zspot> pre\<^sub>R P) \<turnstile> (\<exists> ref\<^sup>< \<Zspot> cmt\<^sub>R P))"
proof -
  have "Skip ;; P = 
        \<^bold>R\<^sub>s ((($tr\<^sup>> = $tr\<^sup>< \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e wp\<^sub>r pre\<^sub>R P) \<turnstile> 
            (($tr\<^sup>> = $tr\<^sup>< \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e ;; peri\<^sub>R P) \<diamondop> 
            (($tr\<^sup>> = $tr\<^sup>< \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e ;; post\<^sub>R P))"
    by (simp add: SRD_composition_wp alpha rdes closure wp assms rpred, pred_auto)
  also have "... = \<^bold>R\<^sub>s ((\<forall> ref\<^sup>< \<Zspot> pre\<^sub>R P) \<turnstile>
                      (($tr\<^sup>> = $tr\<^sup>< \<and> \<not> $wait\<^sup>> \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e ;; ((\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait\<^sup>< \<triangleright> cmt\<^sub>R P)))"
  proof -
    have 1:"($tr\<^sup>> = $tr\<^sup>< \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e wp\<^sub>r pre\<^sub>R P = (\<forall> ref\<^sup>< \<Zspot> pre\<^sub>R P)"
      by (pred_auto)
    thus ?thesis apply simp
      apply (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp)      
      apply pred_simp
      apply (metis (full_types))
      done
  qed
  also have "... = \<^bold>R\<^sub>s ((\<forall> ref\<^sup>< \<Zspot> pre\<^sub>R P) \<turnstile> (\<exists> ref\<^sup>< \<Zspot> cmt\<^sub>R P))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, pred_auto)
  finally show ?thesis .
qed

lemma Skip_left_unit_ref_unrest:
  assumes "P is CSP" "$ref\<^sup>< \<sharp> P\<lbrakk>False/wait\<^sup><\<rbrakk>"
  shows "Skip ;; P = P"
  using assms
  by (simp add: Skip_left_lemma)
     (metis SRD_reactive_tri_design all_unrest cmt_unrest_ref cmt_wait_false ex_unrest fst_vwb_lens ns_alpha_mwb pre_unrest_ref
      pre_wait_false ref_vwb_lens vwb_lens.axioms(2) wait'_cond_peri_post_cmt)
  
lemma CSP3_intro:
  "\<lbrakk> P is CSP; $ref\<^sup>< \<sharp> P\<lbrakk>False/wait\<^sup><\<rbrakk> \<rbrakk> \<Longrightarrow> P is CSP3"
  by (simp add: CSP3_def Healthy_def' Skip_left_unit_ref_unrest)

lemma ref_unrest_RHS_design:
  assumes "$ref\<^sup>< \<sharp> P" "$ref\<^sup>< \<sharp> Q\<^sub>1" "$ref\<^sup>< \<sharp> Q\<^sub>2"
  shows "$ref\<^sup>< \<sharp> (\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<^sub>f"
  by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def design_def unrest unrest_ssubst_expr var_alpha_combine usubst_eval usubst assms)

lemma CSP3_SRD_intro:
  assumes "P is CSP" "$ref\<^sup>< \<sharp> pre\<^sub>R(P)" "$ref\<^sup>< \<sharp> peri\<^sub>R(P)" "$ref\<^sup>< \<sharp> post\<^sub>R(P)"
  shows "P is CSP3"
proof -
  have P: "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = P"
    by (simp add: SRD_reactive_design_alt assms(1) wait'_cond_peri_post_cmt[THEN sym])
  have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) is CSP3"
    by (rule CSP3_intro, simp add: assms P, simp add: ref_unrest_RHS_design assms)
  thus ?thesis
    by (simp add: P)
qed

lemma Skip_unrest_ref [unrest]: "$ref\<^sup>< \<sharp> Skip\<lbrakk>False/wait\<^sup><\<rbrakk>"
  by (simp add: Skip_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest_ssubst_expr usubst_eval unrest)

lemma Skip_unrest_ref' [unrest]: "$ref\<^sup>> \<sharp> Skip\<lbrakk>False/wait\<^sup><\<rbrakk>"
  by (simp add: Skip_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest_ssubst_expr usubst_eval unrest)

lemma CSP3_iff:
  assumes "P is CSP"
  shows "P is CSP3 \<longleftrightarrow> ($ref\<^sup>< \<sharp> P\<lbrakk>False/wait\<^sup><\<rbrakk>)"
proof
  assume 1: "P is CSP3"
  have "$ref\<^sup>< \<sharp> (Skip ;; P)\<lbrakk>False/wait\<^sup><\<rbrakk>"
    by (simp add: usubst unrest)
  with 1 show "$ref\<^sup>< \<sharp> P\<lbrakk>False/wait\<^sup><\<rbrakk>"
    by (metis CSP3_def Healthy_def)
next
  assume 1:"$ref\<^sup>< \<sharp> P\<lbrakk>False/wait\<^sup><\<rbrakk>"
  show "P is CSP3"
    by (simp add: 1 CSP3_intro assms)
qed

lemma CSP3_unrest_ref [unrest]:
  assumes "P is CSP" "P is CSP3"
  shows "$ref\<^sup>< \<sharp> pre\<^sub>R(P)" "$ref\<^sup>< \<sharp> peri\<^sub>R(P)" "$ref\<^sup>< \<sharp> post\<^sub>R(P)"
proof -
  have a:"($ref\<^sup>< \<sharp> P\<lbrakk>False/wait\<^sup><\<rbrakk>)"
    using CSP3_iff assms by blast
  from a show "$ref\<^sup>< \<sharp> pre\<^sub>R(P)"
    by (pred_auto; blast)
  from a show "$ref\<^sup>< \<sharp> peri\<^sub>R(P)"
    by (pred_auto; blast)
  from a show "$ref\<^sup>< \<sharp> post\<^sub>R(P)"
    by (pred_auto; blast)
qed

lemma CSP3_rdes:
  assumes "P is RR" "Q is RR" "R is RR"
  shows "CSP3(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s((\<forall> ref\<^sup>< \<Zspot> P) \<turnstile> (\<exists> ref\<^sup>< \<Zspot> Q) \<diamondop> (\<exists> ref\<^sup>< \<Zspot> R))"
  apply (simp add: CSP3_def Skip_left_lemma closure assms rdes)
  apply (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp)      
  apply pred_simp
  apply (metis (full_types))
  done

lemma CSP3_form:
  assumes "P is CSP"
  shows "CSP3(P) = \<^bold>R\<^sub>s((\<forall> ref\<^sup>< \<Zspot> pre\<^sub>R(P)) \<turnstile> (\<exists> ref\<^sup>< \<Zspot> peri\<^sub>R(P)) \<diamondop> (\<exists> ref\<^sup>< \<Zspot> post\<^sub>R(P)))"
  apply (simp add: CSP3_def Skip_left_lemma closure assms rdes)
  apply (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp)      
  apply pred_simp
  apply (metis (full_types))
  done

lemma CSP3_Skip [closure]:
  "Skip is CSP3"
  by (rule CSP3_intro, simp add: Skip_is_CSP, simp add: Skip_def unrest usubst unrest_ssubst_expr usubst_eval)

lemma CSP3_Stop [closure]:
  "Stop is CSP3"
  by (rule CSP3_intro, simp add: Stop_is_CSP, simp add: Stop_def unrest usubst unrest_ssubst_expr usubst_eval)

lemma CSP3_Idempotent [closure]: "Idempotent CSP3"
  by (metis (no_types, lifting) CSP3_Skip CSP3_def Healthy_if Idempotent_def seqr_assoc)

lemma CSP3_Continuous: "Continuous CSP3"
  by (simp add: Continuous_def CSP3_def seq_Sup_distl)

lemma Skip_right_lemma:
  assumes "P is CSP"
  shows "P ;; Skip = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> cmt\<^sub>R P) \<triangleleft> $wait\<^sup>> \<triangleright> (\<exists> ref\<^sup>> \<Zspot> cmt\<^sub>R P)))"
proof -
  have "P ;; Skip = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> (\<exists> st\<^sup>> \<Zspot> peri\<^sub>R P) \<diamondop> (post\<^sub>R P ;; ($tr\<^sup>> = $tr\<^sup>< \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e))"
    by (simp add: SRD_composition_wp closure assms wp rdes rpred, pred_auto)
  also have "... = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile>
                       ((cmt\<^sub>R P ;; (\<exists> st\<^sup>< \<Zspot> \<lceil>II\<rceil>\<^sub>D)) \<triangleleft> $wait\<^sup>> \<triangleright> (cmt\<^sub>R P ;; ($tr\<^sup>> = $tr\<^sup>< \<and> \<not> $wait\<^sup>< \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, pred_auto)
  also have "... = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile>
                       ((\<exists> st\<^sup>> \<Zspot> cmt\<^sub>R P) \<triangleleft> $wait\<^sup>> \<triangleright> (cmt\<^sub>R P ;; ($tr\<^sup>> = $tr\<^sup>< \<and> \<not> $wait\<^sup>< \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, pred_auto)
  also have "... = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> cmt\<^sub>R P) \<triangleleft> $wait\<^sup>> \<triangleright> (\<exists> ref\<^sup>> \<Zspot> cmt\<^sub>R P)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, pred_auto)
  finally show ?thesis .
qed

lemma Skip_right_tri_lemma:
  assumes "P is CSP"
  shows "P ;; Skip = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> peri\<^sub>R P) \<diamondop> (\<exists> ref\<^sup>> \<Zspot> post\<^sub>R P)))"
proof -
  have "((\<exists> st\<^sup>> \<Zspot> cmt\<^sub>R P) \<triangleleft> $wait\<^sup>> \<triangleright> (\<exists> ref\<^sup>> \<Zspot> cmt\<^sub>R P)) = ((\<exists> st\<^sup>> \<Zspot> peri\<^sub>R P) \<diamondop> (\<exists> ref\<^sup>> \<Zspot> post\<^sub>R P))"
    by (pred_auto)
  thus ?thesis by (simp add: Skip_right_lemma[OF assms])
qed

lemma CSP4_intro:
  assumes "P is CSP" "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))"
          "$st\<^sup>> \<sharp> (cmt\<^sub>R P)\<lbrakk>True/wait\<^sup>>\<rbrakk>" "$ref\<^sup>> \<sharp> (cmt\<^sub>R P)\<lbrakk>False/wait\<^sup>>\<rbrakk>"
  shows "P is CSP4"
proof -
  have "CSP4(P) = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> cmt\<^sub>R P) \<triangleleft> $wait\<^sup>> \<triangleright> (\<exists> ref\<^sup>> \<Zspot> cmt\<^sub>R P)))"
    by (simp add: CSP4_def Skip_right_lemma assms(1))
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R(P) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> cmt\<^sub>R P)\<lbrakk>True/wait\<^sup>>\<rbrakk> \<triangleleft> $wait\<^sup>> \<triangleright> (\<exists> ref\<^sup>> \<Zspot> cmt\<^sub>R P)\<lbrakk>False/wait\<^sup>>\<rbrakk>))"
    
    by (simp add: wp_rea_def assms(2) rpred closure expr_if_bool_var_left expr_if_bool_var_right)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R(P) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> (cmt\<^sub>R P)\<lbrakk>True/wait\<^sup>>\<rbrakk>) \<triangleleft> $wait\<^sup>> \<triangleright> (\<exists> ref\<^sup>> \<Zspot> (cmt\<^sub>R P)\<lbrakk>False/wait\<^sup>>\<rbrakk>)))"
    by (simp add: usubst unrest)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> ((cmt\<^sub>R P)\<lbrakk>True/wait\<^sup>>\<rbrakk> \<triangleleft> $wait\<^sup>> \<triangleright> (cmt\<^sub>R P)\<lbrakk>False/wait\<^sup>>\<rbrakk>))"
    by (simp add: ex_unrest assms)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> cmt\<^sub>R P)"
    by (metis wait'_cond_def wait'_cond_split)
  also have "... = P"
    by (simp add: SRD_reactive_design_alt assms(1))
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma CSP4_RC_intro:
  assumes "P is CSP" "pre\<^sub>R(P) is RC"
          "$st\<^sup>> \<sharp> (cmt\<^sub>R P)\<lbrakk>True/wait\<^sup>>\<rbrakk>" "$ref\<^sup>> \<sharp> (cmt\<^sub>R P)\<lbrakk>False/wait\<^sup>>\<rbrakk>"
  shows "P is CSP4"
proof -
  have "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))"
    by (metis (no_types, lifting) R1_seqr_closure assms(2) rea_not_R1 rea_not_false rea_not_not wp_rea_RC_false wp_rea_def)
  thus ?thesis
    by (simp add: CSP4_intro assms)
qed

lemma CSP4_rdes:
  assumes "P is RR" "Q is RR" "R is RR"
  shows "CSP4(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s (((\<not>\<^sub>r P) wp\<^sub>r false) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> Q) \<diamondop> (\<exists> ref\<^sup>> \<Zspot> R)))"
  apply (simp add: CSP4_def Skip_right_lemma closure assms rdes)
  apply (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp)      
  apply (pred_auto; blast)
  done

lemma CSP4_form:
  assumes "P is CSP"
  shows "CSP4(P) = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> peri\<^sub>R P) \<diamondop> (\<exists> ref\<^sup>> \<Zspot> post\<^sub>R P)))"
  by (simp add: CSP4_def Skip_right_tri_lemma assms)

lemma Skip_srdes_right_unit:
  "(Skip :: ('\<sigma>,'\<phi>) action) ;; II\<^sub>R = Skip"
  by (rdes_simp)

lemma Skip_srdes_left_unit:
  "II\<^sub>R ;; (Skip :: ('\<sigma>,'\<phi>) action) = Skip"
  by (rdes_eq)

lemma CSP4_right_subsumes_RD3: "RD3(CSP4(P)) = CSP4(P)"
  by (metis (no_types, opaque_lifting) CSP4_def RD3_def Skip_srdes_right_unit seqr_assoc)

lemma CSP4_implies_RD3: "P is CSP4 \<Longrightarrow> P is RD3"
  by (metis CSP4_right_subsumes_RD3 Healthy_def)

lemma CSP4_tri_intro:
  assumes "P is CSP" "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))" "$st\<^sup>> \<sharp> peri\<^sub>R(P)" "$ref\<^sup>> \<sharp> post\<^sub>R(P)"
  shows "P is CSP4"
  using assms
  by (rule_tac CSP4_intro, simp_all add: pre\<^sub>R_def peri\<^sub>R_def post\<^sub>R_def usubst cmt\<^sub>R_def)

lemma CSP4_NSRD_intro:
  assumes "P is NSRD" "$ref\<^sup>> \<sharp> post\<^sub>R(P)"
  shows "P is CSP4"
  by (simp add: CSP4_tri_intro NSRD_is_SRD NSRD_neg_pre_unit NSRD_st'_unrest_peri assms)

lemma CSP3_commutes_CSP4: "CSP3(CSP4(P)) = CSP4(CSP3(P))"
  by (simp add: CSP3_def CSP4_def seqr_assoc)

lemma NCSP_implies_CSP [closure]: "P is NCSP \<Longrightarrow> P is CSP"
  by (metis (no_types, opaque_lifting) CSP3_def CSP4_def Healthy_def NCSP_def SRD_idem SRD_seqr_closure Skip_is_CSP comp_apply)

lemma NCSP_elim [RD_elim]: 
  "\<lbrakk> X is NCSP; P(\<^bold>R\<^sub>s(pre\<^sub>R(X) \<turnstile> peri\<^sub>R(X) \<diamondop> post\<^sub>R(X))) \<rbrakk> \<Longrightarrow> P(X)"
  by (simp add: SRD_reactive_tri_design closure)
    
lemma NCSP_implies_CSP3 [closure]:
  "P is NCSP \<Longrightarrow> P is CSP3"
  by (metis (no_types, lifting) CSP3_def Healthy_def' NCSP_def Skip_is_CSP Skip_left_unit_ref_unrest Skip_unrest_ref comp_apply seqr_assoc)

lemma NCSP_implies_CSP4 [closure]:
  "P is NCSP \<Longrightarrow> P is CSP4"
  by (metis (no_types, opaque_lifting) CSP3_commutes_CSP4 Healthy_def NCSP_def NCSP_implies_CSP NCSP_implies_CSP3 comp_apply)

lemma NCSP_implies_RD3 [closure]: "P is NCSP \<Longrightarrow> P is RD3"
  by (metis CSP3_commutes_CSP4 CSP4_right_subsumes_RD3 Healthy_def NCSP_def comp_apply)

lemma NCSP_implies_NSRD [closure]: "P is NCSP \<Longrightarrow> P is NSRD"
  by (simp add: NCSP_implies_CSP NCSP_implies_RD3 SRD_RD3_implies_NSRD)

lemma NCSP_subset_implies_CSP [closure]:
  "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<Longrightarrow> A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  using NCSP_implies_CSP by blast

lemma NCSP_subset_implies_NSRD [closure]:
  "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<Longrightarrow> A \<subseteq> \<lbrakk>NSRD\<rbrakk>\<^sub>H"
  using NCSP_implies_NSRD by blast

lemma CSP_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP"
  by (simp add: is_Healthy_subset_member)

lemma CSP3_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP3\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP3"
  by (simp add: is_Healthy_subset_member)

lemma CSP4_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP4"
  by (simp add: is_Healthy_subset_member)

lemma NCSP_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is NCSP"
  by (simp add: is_Healthy_subset_member)

lemma NCSP_intro:
  assumes "P is CSP" "P is CSP3" "P is CSP4"
  shows "P is NCSP"
  by (metis Healthy_def NCSP_def assms comp_eq_dest_lhs)

lemma Skip_left_unit: "P is NCSP \<Longrightarrow> Skip ;; P = P"
  by (metis (full_types) CSP3_def Healthy_if NCSP_implies_CSP3)

lemma Skip_right_unit: "P is NCSP \<Longrightarrow> P ;; Skip = P"
  by (metis (full_types) CSP4_def Healthy_if NCSP_implies_CSP4)

lemma NCSP_NSRD_intro:
  assumes "P is NSRD" "$ref\<^sup>< \<sharp> pre\<^sub>R(P)" "$ref\<^sup>< \<sharp> peri\<^sub>R(P)" "$ref\<^sup>> \<sharp> post\<^sub>R(P)" "$ref\<^sup>< \<sharp> post\<^sub>R(P)"
  shows "P is NCSP"
  by (simp add: CSP3_SRD_intro CSP4_NSRD_intro NCSP_intro NSRD_is_SRD assms)

lemma CSP4_neg_pre_unit:
  assumes "P is CSP" "P is CSP4"
  shows "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))"
  by (simp add: CSP4_implies_RD3 NSRD_neg_pre_unit SRD_RD3_implies_NSRD assms(1) assms(2))

lemma NSRD_CSP4_intro:
  assumes "P is CSP" "P is CSP4"
  shows "P is NSRD"
  by (simp add: CSP4_implies_RD3 SRD_RD3_implies_NSRD assms(1) assms(2))

lemma NCSP_form: 
  "NCSP P = \<^bold>R\<^sub>s ((\<forall> ref\<^sup>< \<Zspot> (\<not>\<^sub>r pre\<^sub>R(P)) wp\<^sub>r false) \<turnstile> ((\<exists> ref\<^sup>< \<Zspot> \<exists> st\<^sup>> \<Zspot> peri\<^sub>R(P)) \<diamondop> (\<exists> ref\<^sup>< \<Zspot> \<exists> ref\<^sup>> \<Zspot> post\<^sub>R(P))))"
proof -
  obtain Q where Q_def: "Q = NSRD P" and Q_NSRD: "Q is NSRD"
    by (simp add: Healthy_def' NSRD_idem)
  
  have "NCSP P = CSP3 (CSP4 Q)"
    by (metis (no_types, opaque_lifting) CSP4_def NCSP_def NSRD_alt_def RD3_def Skip_srdes_left_unit comp_eq_dest_lhs rel_RA1 Q_def)

  also have "... =  \<^bold>R\<^sub>s ((\<forall> ref\<^sup>< \<Zspot> (\<not>\<^sub>r pre\<^sub>R Q) wp\<^sub>r false) \<turnstile>
                   (\<exists> ref\<^sup>< \<Zspot> \<exists> st\<^sup>> \<Zspot> peri\<^sub>R Q) \<diamondop>
                   (\<exists> ref\<^sup>< \<Zspot> \<exists> ref\<^sup>> \<Zspot> post\<^sub>R Q))"
    by (simp add: CSP3_form CSP4_form closure Q_NSRD unrest wp unrest_ssubst_expr usubst usubst_eval rdes, pred_auto)
  also have "... = \<^bold>R\<^sub>s ((\<forall> ref\<^sup>< \<Zspot> (\<not>\<^sub>r pre\<^sub>R(P)) wp\<^sub>r false) \<turnstile> ((\<exists> ref\<^sup>< \<Zspot> \<exists> st\<^sup>> \<Zspot> peri\<^sub>R(P)) \<diamondop> (\<exists> ref\<^sup>< \<Zspot> \<exists> ref\<^sup>> \<Zspot> post\<^sub>R(P))))"
    apply (simp add: Q_def NSRD_form rdes closure wp rea_pre_RHS_design rea_peri_RHS_design rea_post_RHS_design)
    apply (rule srdes_tri_eq_R1_R2c_intro)
    apply (pred_auto; blast)+
    done

    finally show ?thesis .
qed

lemma CSP4_st'_unrest_peri [unrest]:
  assumes "P is CSP" "P is CSP4"
  shows "$st\<^sup>> \<sharp> peri\<^sub>R(P)"
  by (simp add: NSRD_CSP4_intro NSRD_st'_unrest_peri assms)

lemma CSP4_healthy_form:
  assumes "P is CSP" "P is CSP4"
  shows "P = \<^bold>R\<^sub>s(((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> peri\<^sub>R(P)) \<diamondop> (\<exists> ref\<^sup>> \<Zspot> post\<^sub>R(P))))"
proof -
  have "P = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> cmt\<^sub>R P) \<triangleleft> $wait\<^sup>> \<triangleright> (\<exists> ref\<^sup>> \<Zspot> cmt\<^sub>R P)))"
    by (metis CSP4_def Healthy_def Skip_right_lemma assms(1) assms(2))
  also have "... = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> cmt\<^sub>R P)\<lbrakk>True/wait\<^sup>>\<rbrakk> \<triangleleft> $wait\<^sup>> \<triangleright> (\<exists> ref\<^sup>> \<Zspot> cmt\<^sub>R P)\<lbrakk>False/wait\<^sup>>\<rbrakk>))"
    by (simp add: expr_if_bool_var_left expr_if_bool_var_right)
  also have "... = \<^bold>R\<^sub>s(((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> peri\<^sub>R(P)) \<diamondop> (\<exists> ref\<^sup>> \<Zspot> post\<^sub>R(P))))"
    by (simp add: wait'_cond_def usubst peri\<^sub>R_def post\<^sub>R_def cmt\<^sub>R_def unrest)
  finally show ?thesis .
qed

lemma CSP4_ref'_unrest_pre [unrest]:
  assumes "P is CSP" "P is CSP4"
  shows "$ref\<^sup>> \<sharp> pre\<^sub>R(P)"
  by (simp add: NSRD_CSP4_intro NSRD_neg_pre_RC RC_implies_RR assms(1,2) unrest_ref'_neg_RC)

lemma NCSP_set_unrest_pre_wait':
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  shows "\<And> P. P \<in> A \<Longrightarrow> $wait\<^sup>> \<sharp> pre\<^sub>R(P)"
proof -
  fix P
  assume "P \<in> A"
  hence "P is NSRD"
    using NCSP_implies_NSRD assms by auto
  thus "$wait\<^sup>> \<sharp> pre\<^sub>R(P)"
    using NSRD_wait'_unrest_pre by blast
qed

lemma CSP4_set_unrest_pre_st':
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H"
  shows "\<And> P. P \<in> A \<Longrightarrow> $st\<^sup>> \<sharp> pre\<^sub>R(P)"
proof -
  fix P
  assume "P \<in> A"
  hence "P is NSRD"
    using NSRD_CSP4_intro assms(1) assms(2) by blast
  thus "$st\<^sup>> \<sharp> pre\<^sub>R(P)"
    using NSRD_st'_unrest_pre by blast
qed

find_theorems R2s unrest

thm R2s_unrest

lemma CSP4_ref'_unrest_post [unrest]:
  assumes "P is CSP" "P is CSP4"
  shows "$ref\<^sup>> \<sharp> post\<^sub>R(P)"
proof -
  have "post\<^sub>R(P) = post\<^sub>R(\<^bold>R\<^sub>s(((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false) \<turnstile> ((\<exists> st\<^sup>> \<Zspot> peri\<^sub>R(P)) \<diamondop> (\<exists> ref\<^sup>> \<Zspot> post\<^sub>R(P)))))"
    using CSP4_healthy_form assms(1) assms(2) by fastforce
  also have "... = R1 (R2c ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<longrightarrow>\<^sub>r (\<exists> ref\<^sup>> \<Zspot> post\<^sub>R P)))"
    by (simp add: rea_post_RHS_design usubst unrest wp_rea_def)
  also have "$ref\<^sup>> \<sharp> ..."
    by (simp add: R1_def R2c_def wp_rea_def unrest unrest_ssubst_expr usubst usubst_eval)
  thus ?thesis
    using calculation by auto
qed

lemma CSP3_Chaos [closure]: "Chaos is CSP3"
  by (simp add: Chaos_def, rule CSP3_intro, simp_all add: RHS_design_is_SRD unrest)

lemma CSP4_Chaos [closure]: "Chaos is CSP4"
  by (rule CSP4_tri_intro, simp_all add: closure rdes unrest)

lemma NCSP_Chaos [closure]: "Chaos is NCSP"
  by (simp add: NCSP_intro closure) 
    
lemma CSP3_Miracle [closure]: "Miracle is CSP3"
  by (simp add: Miracle_def, rule CSP3_intro, simp_all add: RHS_design_is_SRD unrest)

lemma CSP4_Miracle [closure]: "Miracle is CSP4"
  by (rule CSP4_tri_intro, simp_all add: closure rdes unrest)

lemma NCSP_Miracle [closure]: "Miracle is NCSP"
  by (simp add: NCSP_intro closure) 
    
lemma NCSP_seqr_closure [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P ;; Q is NCSP"
  by (metis (no_types, lifting) CSP3_def CSP4_def Healthy_def' NCSP_implies_CSP NCSP_implies_CSP3
      NCSP_implies_CSP4 NCSP_intro SRD_seqr_closure assms(1) assms(2) seqr_assoc)

lemma CSP4_Skip [closure]: "Skip is CSP4"
  apply (rule CSP4_intro, simp_all add: Skip_is_CSP)
  apply (simp_all add: Skip_def rea_pre_RHS_design rea_cmt_RHS_design usubst unrest unrest_ssubst_expr usubst_eval R2c_true)
done

lemma NCSP_Skip [closure]: "Skip is NCSP"
  by (metis CSP3_Skip CSP4_Skip Healthy_def NCSP_def Skip_is_CSP comp_apply)

lemma CSP4_Stop [closure]: "Stop is CSP4"
  apply (rule CSP4_intro, simp_all add: Stop_is_CSP)
  apply (simp_all add: Stop_def rea_pre_RHS_design rea_cmt_RHS_design usubst unrest unrest_ssubst_expr usubst_eval R2c_true)
done

lemma NCSP_Stop [closure]: "Stop is NCSP"
  by (metis CSP3_Stop CSP4_Stop Healthy_def NCSP_def Stop_is_CSP comp_apply)

lemma CSP4_Idempotent: "Idempotent CSP4"
  by (metis (no_types, lifting) CSP3_Skip CSP3_def CSP4_def Healthy_if Idempotent_def seqr_assoc)

lemma CSP4_Continuous: "Continuous CSP4"
  by (simp add: Continuous_def CSP4_def seq_Sup_distr)

(*
lemma rdes_frame_ext_NCSP_closed [closure]:
  assumes "vwb_lens a" "P is NCSP"
  shows "a:[P]\<^sub>R\<^sup>+ is NCSP"
  by (metis (no_types, lifting) CSP3_def CSP4_def Healthy_intro NCSP_Skip NCSP_implies_NSRD NCSP_intro NSRD_is_SRD Skip_frame Skip_left_unit Skip_right_unit assms(1) assms(2) rdes_frame_ext_NSRD_closed seq_srea_frame)
*)

lemma preR_Stop [rdes]: "pre\<^sub>R(Stop) = true\<^sub>r"
  by (simp add: Stop_def Stop_is_CSP rea_pre_RHS_design unrest usubst R2c_true)

lemma periR_Stop [rdes]: "peri\<^sub>R(Stop) = \<E>(True,[],{})"
  by (pred_auto)

lemma postR_Stop [rdes]: "post\<^sub>R(Stop) = false"
  by (pred_auto)

lemma cmtR_Stop [rdes]: "cmt\<^sub>R(Stop) = ($tr\<^sup>> = $tr\<^sup>< \<and> $wait\<^sup>>)\<^sub>e"
  by (pred_auto)

lemma NCSP_Idempotent [closure]: "Idempotent NCSP"
  by (clarsimp simp add: NCSP_def Idempotent_def)
     (metis (no_types, opaque_lifting) CSP3_Idempotent CSP3_def CSP4_Idempotent CSP4_def Healthy_def Idempotent_def SRD_idem SRD_seqr_closure Skip_is_CSP seqr_assoc)

lemma NCSP_Continuous [closure]: "Continuous NCSP"
  by (simp add: CSP3_Continuous CSP4_Continuous Continuous_comp NCSP_def SRD_Continuous)

lemma preR_CRR [closure]: "P is NCSP \<Longrightarrow> pre\<^sub>R(P) is CRR"
  by (rule CRR_intro, simp_all add: closure unrest)
  
lemma periR_CRR [closure]: "P is NCSP \<Longrightarrow> peri\<^sub>R(P) is CRR"
  by (rule CRR_intro, simp_all add: closure unrest)

lemma postR_CRR [closure]: "P is NCSP \<Longrightarrow> post\<^sub>R(P) is CRR"
  by (rule CRR_intro, simp_all add: closure unrest)
    
lemma NCSP_rdes_intro [closure]:
  assumes "P is CRC" "Q is CRR" "R is CRR"
          "$st\<^sup>> \<sharp> Q" "$ref\<^sup>> \<sharp> R"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) is NCSP"
  apply (rule NCSP_intro)
    apply (simp_all add: closure assms)
   apply (rule CSP3_SRD_intro)
      apply (simp_all add: rdes closure assms unrest)
  apply (rule CSP4_tri_intro)
     apply (simp_all add: rdes closure assms unrest unrest_ssubst_expr usubst usubst_eval)
  apply (metis (no_types, lifting) CRC_implies_RC R1_seqr_closure assms(1) rea_not_R1 rea_not_false rea_not_not wp_rea_RC_false wp_rea_def)
  done
    
lemma NCSP_preR_CRC [closure]:
  assumes "P is NCSP"
  shows "pre\<^sub>R(P) is CRC"
  by (rule CRC_intro, simp_all add: closure assms unrest)

lemma NCSP_postR_CRF [closure]: "P is NCSP \<Longrightarrow> post\<^sub>R P is CRF"
  by (rule CRF_intro, simp_all add: unrest closure)

lemma CSP3_Sup_closure [closure]:
  "A \<subseteq> \<lbrakk>CSP3\<rbrakk>\<^sub>H \<Longrightarrow> (\<Sqinter> A) is CSP3"
  apply (auto simp add: CSP3_def Healthy_def seq_Sup_distl)
  apply (rule cong[of Sup])
   apply (rule refl)
  using image_iff apply force
  done

lemma CSP4_Sup_closure [closure]:
  "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H \<Longrightarrow> (\<Sqinter> A) is CSP4"
  apply (auto simp add: CSP4_def Healthy_def seq_Sup_distr)
  apply (rule cong[of Sup])
   apply (rule refl)
  using image_iff apply force
  done
  
lemma NCSP_Sup_closure [closure]: "\<lbrakk> A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H; A \<noteq> {} \<rbrakk> \<Longrightarrow> (\<Sqinter> A) is NCSP"
  apply (rule NCSP_intro, simp_all add: closure)
   apply (metis (no_types, lifting) Ball_Collect CSP3_Sup_closure NCSP_implies_CSP3)
  apply (metis (no_types, lifting) Ball_Collect CSP4_Sup_closure NCSP_implies_CSP4)
  done

lemma NCSP_SUP_closure [closure]: "\<lbrakk> \<And> i. P(i) is NCSP; A \<noteq> {} \<rbrakk> \<Longrightarrow> (\<Sqinter> i\<in>A. P(i)) is NCSP"
  by (metis (mono_tags, lifting) Ball_Collect NCSP_Sup_closure image_iff image_is_empty)

lemma PCSP_implies_NCSP [closure]:
  assumes "P is PCSP"
  shows "P is NCSP"
proof -
  have "P = Productive(NCSP(NCSP P))"
    by (metis (no_types, opaque_lifting) Healthy_def' Idempotent_def NCSP_Idempotent assms comp_apply)
    
  also have "... = \<^bold>R\<^sub>s ((\<forall> ref\<^sup>< \<Zspot> (\<not>\<^sub>r pre\<^sub>R(NCSP P)) wp\<^sub>r false) \<turnstile> 
                       (\<exists> ref\<^sup>< \<Zspot> \<exists> st\<^sup>> \<Zspot> peri\<^sub>R(NCSP P)) \<diamondop> 
                       ((\<exists> ref\<^sup>< \<Zspot> \<exists> ref\<^sup>> \<Zspot> post\<^sub>R (NCSP P)) \<and> ($tr\<^sup>< < $tr\<^sup>>)\<^sub>e))"
    by (simp add: NCSP_form Productive_RHS_design_form unrest unrest_ssubst_expr usubst usubst_eval closure)
  also have "... is NCSP"
    apply (rule NCSP_rdes_intro)
        apply (rule CRC_intro)
         apply (simp_all add: unrest unrest_ssubst_expr usubst usubst_eval ex_unrest all_unrest closure)
    done
  thus ?thesis
    using calculation by force
qed

lemma PCSP_elim [RD_elim]: 
  assumes "X is PCSP" "P (\<^bold>R\<^sub>s ((pre\<^sub>R X) \<turnstile> peri\<^sub>R X \<diamondop> (R4(post\<^sub>R X))))"
  shows "P X"
proof -
  from assms(1) have X_NSRD: "X is NSRD" by (simp add: PCSP_implies_NCSP NCSP_implies_NSRD)
  have X_form: "X = \<^bold>R\<^sub>s (pre\<^sub>R X \<turnstile> peri\<^sub>R X \<diamondop> post\<^sub>R X)"
    by (simp add: NSRD_is_SRD SRD_reactive_tri_design X_NSRD)
  show ?thesis
  proof -
    have f1: "X is NCSP"
      using PCSP_implies_NCSP assms(1) by blast
    then have f2: "Productive X = X"
      by (metis Healthy_def assms(1) comp_apply)
    have "(peri\<^sub>R X is RR) \<and> (pre\<^sub>R X is RR)"
      using f1 by (simp add: CRR_implies_RR X_NSRD periR_CRR preR_RR)
    then show ?thesis
      using f2 f1 by (metis (no_types) CRR_implies_RR Productive_RHS_R4_design_form X_form assms(2) postR_CRR)
  qed
qed

lemma R5_alt_def: "R5(P) = (P \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e)"
  by pred_auto

lemma ICSP_implies_NCSP [closure]:
  assumes "P is ICSP"
  shows "P is NCSP"
proof -
  have "P = ISRD1(NCSP(NCSP P))"
    by (metis (no_types, opaque_lifting) Healthy_def' Idempotent_def NCSP_Idempotent assms comp_apply)
  also have "... = ISRD1 (\<^bold>R\<^sub>s ((\<forall> ref\<^sup>< \<Zspot> (\<not>\<^sub>r pre\<^sub>R (NCSP P)) wp\<^sub>r false) \<turnstile>
                              (\<exists> ref\<^sup>< \<Zspot> \<exists> st\<^sup>> \<Zspot> peri\<^sub>R (NCSP P)) \<diamondop> 
                              (\<exists> ref\<^sup>< \<Zspot> \<exists> ref\<^sup>> \<Zspot> post\<^sub>R (NCSP P))))"
    by (simp add: NCSP_form)
  also have "... = \<^bold>R\<^sub>s ((\<forall> ref\<^sup>< \<Zspot> (\<not>\<^sub>r pre\<^sub>R(NCSP P)) wp\<^sub>r false) \<turnstile> 
                       false \<diamondop> 
                       ((\<exists> ref\<^sup>< \<Zspot> \<exists> ref\<^sup>> \<Zspot> post\<^sub>R (NCSP P)) \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e))"
    by (simp_all add: ISRD1_RHS_design_form R5_alt_def closure rdes unrest)
  also have "... is NCSP"
    apply (rule NCSP_rdes_intro)
        apply (rule CRC_intro)
         apply (simp_all add: unrest unrest_ssubst_expr usubst usubst_eval ex_unrest all_unrest closure)
    done
  thus ?thesis using calculation by auto
qed

lemma ICSP_implies_ISRD [closure]:
  assumes "P is ICSP"
  shows "P is ISRD"
  by (metis (no_types, opaque_lifting) Healthy_def ICSP_implies_NCSP ISRD_def NCSP_implies_NSRD assms comp_apply)

lemma ICSP_elim [RD_elim]: 
  assumes "X is ICSP" "P (\<^bold>R\<^sub>s ((pre\<^sub>R X) \<turnstile> false \<diamondop> R5(post\<^sub>R X)))"
  shows "P X"
  by (metis Healthy_if NCSP_implies_CSP ICSP_implies_NCSP ISRD1_form assms comp_apply)

lemma ICSP_Stop_right_zero_lemma:
  "(P \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) ;; true\<^sub>r = true\<^sub>r \<Longrightarrow> (P \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) ;; ($tr\<^sup>> = $tr\<^sup><)\<^sub>e = ($tr\<^sup>> = $tr\<^sup><)\<^sub>e"
  by (pred_auto, blast)

lemma ICSP_Stop_right_zero:
  assumes "P is ICSP" "pre\<^sub>R(P) = true\<^sub>r" "post\<^sub>R(P) ;; true\<^sub>r = true\<^sub>r"
  shows "P ;; Stop = Stop"
proof -
  from assms(3) have 1:"(post\<^sub>R P \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) ;; true\<^sub>r = true\<^sub>r"
    by (pred_auto, metis (no_types, opaque_lifting) dual_order.eq_iff)
  show ?thesis
    by (rdes_simp cls: assms(1), simp add: R5_alt_def csp_enable_nothing assms(2) ICSP_Stop_right_zero_lemma[OF 1])
qed

lemma ICSP_intro: "\<lbrakk> P is NCSP; P is ISRD1 \<rbrakk> \<Longrightarrow> P is ICSP"
  using Healthy_comp by blast

lemma seq_ICSP_closed [closure]:
  assumes "P is ICSP" "Q is ICSP"
  shows "P ;; Q is ICSP"
  by (meson ICSP_implies_ISRD ICSP_implies_NCSP ICSP_intro ISRD_implies_ISRD1 NCSP_seqr_closure assms seq_ISRD_closed)

lemma Miracle_ICSP [closure]: "Miracle is ICSP"
  by (rule ICSP_intro, simp add: closure, simp add: ISRD1_rdes_intro rdes_def closure)

subsection \<open> CSP theories \<close>

lemma NCSP_false: "NCSP false = Miracle"
  by (simp add: NCSP_def srdes_theory.healthy_top[THEN sym], simp add: closure Healthy_if)

lemma NCSP_true: "NCSP true = Chaos"
  by (simp add: NCSP_def srdes_theory.healthy_bottom[THEN sym], simp add: closure Healthy_if)
 
interpretation csp_theory: utp_theory_kleene NCSP Skip
  rewrites "P \<in> carrier csp_theory.thy_order \<longleftrightarrow> P is NCSP"
  and "carrier csp_theory.thy_order \<rightarrow> carrier csp_theory.thy_order \<equiv> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  and "le csp_theory.thy_order = (\<sqsubseteq>)"
  and "eq csp_theory.thy_order = (=)"
  and csp_top: "csp_theory.utp_top = Miracle" 
  and csp_bottom: "csp_theory.utp_bottom = Chaos"
proof -
  have "utp_theory_continuous NCSP"
    by (unfold_locales, simp_all add: Healthy_Idempotent Healthy_if NCSP_Idempotent NCSP_Continuous)
  then interpret utp_theory_continuous NCSP
    by simp
  show t: "utp_top = Miracle" and b:"utp_bottom = Chaos"
    by (simp_all add: healthy_top healthy_bottom NCSP_false NCSP_true)
  show "utp_theory_kleene NCSP Skip"
    by (unfold_locales, simp_all add: closure Skip_left_unit Skip_right_unit Miracle_left_zero t)
qed (simp_all)

abbreviation TestC ("test\<^sub>C") where
"test\<^sub>C P \<equiv> csp_theory.utp_test P"

definition StarC :: "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" ("_\<^sup>\<star>\<^sup>C" [999] 999) where
"StarC P \<equiv> csp_theory.utp_star P"

lemma StarC_unfold: "P is NCSP \<Longrightarrow> P\<^sup>\<star>\<^sup>C = Skip \<sqinter> (P ;; P\<^sup>\<star>\<^sup>C)"
  by (simp add: StarC_def csp_theory.Star_unfoldl_eq)

lemma sfrd_star_as_rdes_star:
  "P is NCSP \<Longrightarrow> P\<^sup>\<star>\<^sup>R ;; Skip = P\<^sup>\<star>\<^sup>C"
  by (simp add: upred_semiring.distrib_right csp_theory.Star_alt_def nsrdes_theory.Star_alt_def StarC_def StarR_def closure unrest unrest_ssubst_expr usubst usubst_eval Skip_srdes_left_unit csp_theory.Unit_Right)

lemma sfrd_star_as_rdes_star':
  "P is NCSP \<Longrightarrow> Skip ;; P\<^sup>\<star>\<^sup>R = P\<^sup>\<star>\<^sup>C"
  by (simp add: csp_theory.Star_alt_def nsrdes_theory.Star_alt_def StarC_def StarR_def closure unrest Skip_srdes_right_unit csp_theory.Unit_Left upred_semiring.distrib_left)

theorem csp_star_rdes_def [rdes_def]:
  assumes "P is CRC" "Q is CRR" "R is CRF" "$st\<^sup>> \<sharp> Q"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R))\<^sup>\<star>\<^sup>C = \<^bold>R\<^sub>s((R\<^sup>\<star>\<^sup>c wp\<^sub>r P) \<turnstile> (R\<^sup>\<star>\<^sup>c ;; Q) \<diamondop> R\<^sup>\<star>\<^sup>c)"
  apply (simp add: wp_rea_def sfrd_star_as_rdes_star[THEN sym] crf_star_as_rea_star assms seqr_assoc rpred closure unrest StarR_rdes_def)
  apply (simp add: rdes_def assms closure unrest wp_rea_def[THEN sym])
  apply (simp add: wp rpred assms closure)
  apply (simp add: csp_do_nothing) 
  done

subsection \<open> Algebraic laws \<close>

lemma Stop_left_zero:
  assumes "P is CSP"
  shows "Stop ;; P = Stop"
  by (simp add: NSRD_seq_post_false assms NCSP_implies_NSRD NCSP_Stop postR_Stop)

end