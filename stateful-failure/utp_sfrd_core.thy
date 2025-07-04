section \<open> Stateful-Failure Core Types \<close>

theory utp_sfrd_core
  imports "HOL-Library.Function_Algebras" "UTP-Reactive-Designs.utp_rea_designs"
begin

unbundle UTP_Syntax 

subsection \<open> SFRD Alphabet \<close>

alphabet ('\<sigma>, '\<phi>) sfrd_vars = "('\<phi> list, '\<sigma>) srea_vars" +
  ref :: "'\<phi> set"                               

text \<open>
  The following two locale interpretations are a technicality to improve the
  behaviour of the automatic tactics. They enable (re)interpretation of state
  spaces in order to remove any occurrences of lens types, replacing them by
  tuple types after the tactics @{method pred_simp} and @{method rel_simp}
  are applied. Eventually, it would be desirable to automate preform these
  interpretations automatically as part of the @{command alphabet} command.
\<close>

(*
interpretation alphabet_csp_prd:
  lens_interp "\<lambda>(ok, wait, tr, m). (ok, wait, tr, ref\<^sub>v m, more m)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation alphabet_csp_rel:
  lens_interp "\<lambda>(ok, ok', wait, wait', tr, tr', m, m').
    (ok, ok', wait, wait', tr, tr', ref\<^sub>v m, ref\<^sub>v m', more m, more m')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done
*)

type_synonym ('\<sigma>,'\<phi>) sfrd = "('\<sigma>, '\<phi>) sfrd_vars"
type_synonym ('\<sigma>,'\<phi>) action  = "('\<sigma>, '\<phi>) sfrd hrel"
type_synonym '\<phi> csp = "(unit,'\<phi>) sfrd"
type_synonym '\<phi> process  = "'\<phi> csp hrel"
  
text \<open> There is some slight imprecision with the translations, in that we don't bother to check
  if the trace event type and refusal set event types are the same. Essentially this is because
  its very difficult to construct processes where this would be the case. However, it may
  be better to add a proper ML print translation in the future. \<close>
  
translations
  (type) "('\<sigma>,'\<phi>) sfrd" <= (type) "('\<sigma>, '\<phi>) sfrd_vars"
  (type) "('\<sigma>,'\<phi>) action" <= (type) "('\<sigma>, '\<phi>) sfrd hrel"
  (type) "'\<phi> process" <= (type) "(unit,'\<phi>) action"

notation sfrd_vars.more\<^sub>L ("\<Sigma>\<^sub>C")

(* FIXME: Nasty hack below *)

declare des_vars.splits [alpha_splits del]
declare rea_vars.splits [alpha_splits del]
declare des_vars.splits [alpha_splits del]
declare srea_vars.splits [alpha_splits del]
declare srea_vars.splits [alpha_splits]
declare rea_vars.splits [alpha_splits]
declare des_vars.splits [alpha_splits]

subsection \<open> Basic laws \<close>
                             
lemma R2c_tr_ext: "R2c ($tr\<^sup>> = $tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><])\<^sub>e = ($tr\<^sup>> = $tr\<^sup>< @ [\<lceil>a\<rceil>\<^sub>S\<^sub><])\<^sub>e"
  by (pred_auto)

lemma circus_alpha_bij_lens:
  "bij_lens (((ok\<^sup><,ok\<^sup>>,wait\<^sup><,wait\<^sup>>,tr\<^sup><,tr\<^sup>>,st\<^sup><,st\<^sup>>,ref\<^sup><,ref\<^sup>>))\<^sub>v :: _ \<Longrightarrow> ('s,'e) sfrd \<times> ('s,'e) sfrd)"
  by (unfold_locales, simp add: alpha_splits lens_defs alpha_defs prod.case_eq_if)+

subsection \<open> Unrestriction laws \<close>

lemma pre_unrest_ref [unrest]: "$ref\<^sup>< \<sharp> P \<Longrightarrow> $ref\<^sup>< \<sharp> pre\<^sub>R(P)"
  by (simp add: pre\<^sub>R_def unrest)

lemma peri_unrest_ref [unrest]: "$ref\<^sup>< \<sharp> P \<Longrightarrow> $ref\<^sup>< \<sharp> peri\<^sub>R(P)"
  by (simp add: peri\<^sub>R_def R1_def, unrest)

lemma post_unrest_ref [unrest]: "$ref\<^sup>< \<sharp> P \<Longrightarrow> $ref\<^sup>< \<sharp> post\<^sub>R(P)"
  by (simp add: post\<^sub>R_def R1_def, unrest)

lemma cmt_unrest_ref [unrest]: "$ref\<^sup>< \<sharp> P \<Longrightarrow> $ref\<^sup>< \<sharp> cmt\<^sub>R(P)"
  by (simp add: cmt\<^sub>R_def R1_def, unrest)

lemma st_lift_unrest_ref' [unrest]: "$ref\<^sup>> \<sharp> \<lceil>b\<rceil>\<^sub>S\<^sub><"
  by (pred_auto)

lemma RHS_design_ref_unrest [unrest]:
  "\<lbrakk>$ref\<^sup>< \<sharp> P; $ref\<^sup>< \<sharp> Q \<rbrakk> \<Longrightarrow> $ref\<^sup>< \<sharp> (\<^bold>R\<^sub>s(P \<turnstile> Q))\<lbrakk>False/wait\<^sup><\<rbrakk>"
  by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def design_def, unrest)

lemma R1_ref_unrest [unrest]: "$ref\<^sup>< \<sharp> P \<Longrightarrow> $ref\<^sup>< \<sharp> R1(P)"
  unfolding R1_def by unrest

lemma R2c_ref_unrest [unrest]: "$ref\<^sup>< \<sharp> P \<Longrightarrow> $ref\<^sup>< \<sharp> R2c(P)"
  unfolding R2c_def R2s_def by pred_auto

lemma R1_ref'_unrest [unrest]: "$ref\<^sup>> \<sharp> P \<Longrightarrow> $ref\<^sup>> \<sharp> R1(P)"
  by (simp add: R1_def, unrest)

lemma R2c_ref'_unrest [unrest]: "$ref\<^sup>> \<sharp> P \<Longrightarrow> $ref\<^sup>> \<sharp> R2c(P)"
  by pred_auto

lemma R2s_notin_ref': "R2s(\<lceil>e\<rceil>\<^sub>S\<^sub>< \<notin> $ref\<^sup>>)\<^sub>e = (\<lceil>e\<rceil>\<^sub>S\<^sub>< \<notin> $ref\<^sup>>)\<^sub>e"
  by pred_auto

lemma unrest_circus_alpha:
  fixes P :: "('e, 't) action"
  assumes 
    "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$wait\<^sup>< \<sharp> P" "$wait\<^sup>> \<sharp> P" "$tr\<^sup>< \<sharp> P" 
    "$tr\<^sup>> \<sharp> P" "$st\<^sup>< \<sharp> P" "$st\<^sup>> \<sharp> P" "$ref\<^sup>< \<sharp> P" "$ref\<^sup>> \<sharp> P"
  shows "\<Sigma> \<sharp> P"
  by (rule bij_lens_unrest_all[OF circus_alpha_bij_lens], simp add: unrest assms)

lemma unrest_subst_upd_same [unrest]: "\<lbrakk> vwb_lens x; $x \<sharp> (e)\<^sub>e; $x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> $x \<sharp> \<sigma>(x \<leadsto> e) \<dagger> f"
  by (expr_simp)

lemma unrest_subst_upd_diff: "\<lbrakk> vwb_lens x; vwb_lens y; x \<bowtie> y; $x \<sharp> (e)\<^sub>e; $x \<sharp> \<sigma> \<dagger> f; $y \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> $x \<sharp> \<sigma>(y \<leadsto> e) \<dagger> f"
  by (expr_simp, metis lens_indep.lens_put_comm)

lemma unrest_all_circus_vars:
  fixes P :: "('s, 'e) action"
  assumes "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$wait\<^sup>< \<sharp> P" "$wait\<^sup>> \<sharp> P" "$ref\<^sup>< \<sharp> P"
  shows "\<Sigma> \<sharp> [ref\<^sup>> \<leadsto> \<guillemotleft>r'\<guillemotright>, st\<^sup>< \<leadsto> \<guillemotleft>s\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>s'\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>t\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>t'\<guillemotright>] \<dagger> P"
  using assms
  by (simp add: bij_lens_unrest_all_eq[OF circus_alpha_bij_lens] unrest_pair_split unrest unrest_subst_upd_diff)

(*

lemma unrest_all_circus_vars_st_st':
  fixes P :: "('s, 'e) action"
  assumes "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$wait\<^sup>< \<sharp> P" "$wait\<^sup>> \<sharp> P" "$ref\<^sup>< \<sharp> P" "$ref\<^sup>> \<sharp> P" "\<Sigma> \<sharp> s" "\<Sigma> \<sharp> s'" "\<Sigma> \<sharp> t" "\<Sigma> \<sharp> t'"
  shows "\<Sigma> \<sharp> [$st \<leadsto> s, $st\<^sup>> \<leadsto> s', $tr \<leadsto> t, $tr\<^sup>> \<leadsto> t'] \<dagger> P"
  using assms
  by (simp add: bij_lens_unrest_all_eq[OF circus_alpha_bij_lens] unrest_plus_split plus_vwb_lens)
     (simp add: unrest usubst closure)

lemma unrest_all_circus_vars_st:
  fixes P :: "('s, 'e) action"
  assumes "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$wait\<^sup>< \<sharp> P" "$wait\<^sup>> \<sharp> P" "$ref\<^sup>< \<sharp> P" "$ref\<^sup>> \<sharp> P" "$st\<^sup>> \<sharp> P" "\<Sigma> \<sharp> s" "\<Sigma> \<sharp> t" "\<Sigma> \<sharp> t'"
  shows "\<Sigma> \<sharp> [$st \<leadsto> s, $tr \<leadsto> t, $tr\<^sup>> \<leadsto> t'] \<dagger> P"
  using assms
  by (simp add: bij_lens_unrest_all_eq[OF circus_alpha_bij_lens] unrest_plus_split plus_vwb_lens)
      (simp add: unrest usubst closure)

lemma unrest_any_circus_var:
  fixes P :: "('s, 'e) action"
  assumes "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$wait\<^sup>< \<sharp> P" "$wait\<^sup>> \<sharp> P" "$ref\<^sup>< \<sharp> P" "$ref\<^sup>> \<sharp> P" "\<Sigma> \<sharp> s" "\<Sigma> \<sharp> s'" "\<Sigma> \<sharp> t" "\<Sigma> \<sharp> t'"
  shows "x \<sharp> [$st \<leadsto> s, $st\<^sup>> \<leadsto> s', $tr \<leadsto> t, $tr\<^sup>> \<leadsto> t'] \<dagger> P" 
  by (simp add: unrest_all_var unrest_all_circus_vars_st_st' assms)

lemma unrest_any_circus_var_st:
  fixes P :: "('s, 'e) action"
  assumes "$ok\<^sup>< \<sharp> P" "$ok\<^sup>> \<sharp> P" "$wait\<^sup>< \<sharp> P" "$wait\<^sup>> \<sharp> P" "$ref\<^sup>< \<sharp> P" "$ref\<^sup>> \<sharp> P" "$st\<^sup>> \<sharp> P" "\<Sigma> \<sharp> s" "\<Sigma> \<sharp> t" "\<Sigma> \<sharp> t'"
  shows "x \<sharp> [$st \<leadsto> s, $tr \<leadsto> t, $tr\<^sup>> \<leadsto> t'] \<dagger> P"
  by (simp add: unrest_all_var unrest_all_circus_vars_st assms)
*)

end