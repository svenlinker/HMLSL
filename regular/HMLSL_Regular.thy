(*  Title:      regular/HMLSL_Regular.thy
    Author:     Sven Linker

Defines HMLSL with regular sensors for cars.
*)
section\<open>HMLSL for Regular Sensors\<close>
text \<open>
Within this section, we instantiate HMLSL for cars with 
regular sensors.
\<close>


theory HMLSL_Regular
  imports "../HMLSL" Regular_Sensors
begin
  
locale hmlsl_regular = regular_sensors + restriction
begin
interpretation hmlsl : hmlsl "regular :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
proof unfold_locales   
  fix e ts c
  show " 0 < regular e ts c"  
    by (metis less_add_same_cancel2 less_trans regular_def
        traffic.psGeZero traffic.sdGeZero) 
qed
  
notation hmlsl.re ("re'(_')")
notation hmlsl.cl("cl'(_')")
notation hmlsl.len ("len")

text \<open>
The spatial atoms are dependent of the perspective of the view,
hence we cannot prove similar lemmas as for perfect sensors.

However, we can still prove 
lemmas corresponding to the activity and stability rules of the
proof system for MLSL \cite{Linker2015a}.

Similar to the situation with perfect sensors, needed to instantiate the 
sensor function, to ensure that the perceived length does not change
during spatial transitions.
\<close>
  
lemma backwards_res_act:
  "(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c) \<^bold>\<or> cl(c))"
proof
  assume assm:"(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c))"
  from assm have len_eq:"len v ts c = len v ts' c"
    using create_reservation_length_stable by blast
  have "res ts c \<sqsubseteq> res ts' c" using assm traffic.create_res_subseteq1
    by auto
  hence restr_subs_res:"restrict v (res ts) c \<sqsubseteq> restrict v (res ts') c"    
    using assm restriction.restrict_view 
    using create_reservation_restrict_union by auto
  have "clm ts c \<sqsubseteq> res ts' c" using assm traffic.create_res_subseteq2     
    using assm restriction.restrict_view  by auto 
  hence restr_subs_clm:"restrict v (clm ts) c \<sqsubseteq> restrict v (res ts') c"     
    using assm restriction.restrict_view 
    using restriction.create_reservation_restrict_union by auto
  have "restrict v (res ts) c = \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>" by simp
  then show " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))" 
  proof
    assume restr_res_nonempty:"restrict v (res ts) c \<noteq> \<emptyset>"
    hence restrict_one:"|restrict v (res ts) c | = 1" 
      using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym
        restr_subs_res assm 
      using local.hmlsl.re_def local.hmlsl.satisfies_def by fastforce
    have "restrict v (res ts ) c \<sqsubseteq> lan v" using restr_subs_res assm 
      by (simp add: restriction.restrict_view)
    hence "restrict v (res ts)c = lan v" using restriction.restrict_eq_lan_subs
        restrict_one assm  
      using local.hmlsl.re_def local.hmlsl.satisfies_def by auto
    then show ?thesis using assm len_eq 
      by (simp add: local.hmlsl.re_def local.hmlsl.satisfies_def)
  next
    assume restr_res_empty:"restrict v (res ts) c = \<emptyset>"
    then have  clm_non_empty: "restrict v (clm ts) c \<noteq> \<emptyset>" 
      using HMLSL.hmlsl.re_def assm local.hmlsl.re_def local.hmlsl.satisfies_def nat_int.card_empty_zero restriction.create_reservation_restrict_union by auto
    then  have restrict_one:"|restrict v (clm ts) c | = 1" 
      using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym
        restr_subs_clm assm 
      using restriction.restriction_clm_leq_one by fastforce
    have "restrict v (clm ts ) c \<sqsubseteq> lan v" using restr_subs_clm assm 
      using restriction.restrict_view by auto
    hence "restrict v (clm ts)c = lan v" using restriction.restrict_eq_lan_subs
        restrict_one assm   
      using local.hmlsl.re_def local.hmlsl.satisfies_def by auto
    then show ?thesis using assm len_eq 
      by (simp add: local.hmlsl.cl_def local.hmlsl.re_def local.hmlsl.satisfies_def)
  qed
qed

lemma backwards_res_act_somewhere:
  "(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle>) \<longrightarrow> (ts,v \<Turnstile>\<^bold>\<langle> re(c) \<^bold>\<or> cl(c)\<^bold>\<rangle> )"
proof
  assume a:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle>)"
  then obtain v' where "(ts',v' \<Turnstile> re(c)) \<and> v' \<le> v" 
    using local.hmlsl.hchop_def local.hmlsl.satisfies_def local.hmlsl.vchop_def hmlsl.somewhere_leq  
    by (metis (no_types, lifting))
  then have "ts,v' \<Turnstile> re(c) \<^bold>\<or> cl(c)" using backwards_res_act a by blast
  then show "ts,v \<Turnstile>\<^bold>\<langle> re(c) \<^bold>\<or> cl(c)\<^bold>\<rangle>" 
  using backwards_res_act hmlsl.satisfies_def hmlsl.somewhere_leq 
  using \<open>(ts' , v' \<Turnstile> re(c)) \<and> v' \<le> v\<close> by auto
qed

lemma backwards_res_stab:
  "(ts \<^bold>\<midarrow>r(d) \<^bold>\<rightarrow> ts') \<and>  (d \<noteq>c) \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))" 
  using regular_sensors.create_reservation_length_stable restrict_def'
    traffic.create_res_subseteq1_neq 
  using local.hmlsl.re_def local.hmlsl.satisfies_def by auto
  
lemma backwards_c_res_stab:
  "(ts \<^bold>\<midarrow>c(d,n) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
  using create_claim_length_stable traffic.create_clm_eq_res  
  by (metis local.hmlsl.re_def local.hmlsl.satisfies_def traffic.create_claim_def)
    
lemma backwards_wdc_res_stab:
  "(ts \<^bold>\<midarrow>wdc(d) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
  using withdraw_claim_length_stable traffic.withdraw_clm_eq_res
  by (metis local.hmlsl.re_def local.hmlsl.satisfies_def traffic.withdraw_claim_def)
    
lemma backwards_wdr_res_stab:
  "(ts \<^bold>\<midarrow>wdr(d,n) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))" 
  by (metis inf.absorb1 local.hmlsl.re_def local.hmlsl.satisfies_def order.trans regular_sensors.withdraw_reservation_length_stable restriction.restrict_def' restriction.restrict_res withdraw_res_subseteq)

text\<open>
We now proceed to prove the \emph{reservation lemma}, which was 
crucial in the manual safety proof \cite {Hilscher2011}. 
\<close>
lemma reservation1: "\<Turnstile>(re(c) \<^bold>\<or> cl(c)) \<^bold>\<rightarrow> \<^bold>\<box>r(c) re(c)" 
proof -
  { fix ts v ts'
  assume assm:"ts,v \<Turnstile>re(c) \<^bold>\<or> cl(c)" and ts'_def:"ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts'"
  from assm have  "re(c) ts' v" unfolding hmlsl.satisfies_def
  proof
    assume re:  "re(c) ts v" 
    then show ?thesis  
      using local.hmlsl.re_def regular_sensors.create_reservation_length_stable restrict_view restriction.create_reservation_restrict_union sup.absorb_iff1 ts'_def by fastforce
  next
    assume cl:"cl(c) ts v"
    then show ?thesis  
      by (metis (no_types, lifting) dual_order.antisym local.hmlsl.cl_def local.hmlsl.re_def regular_sensors.create_reservation_length_stable restrict_view restriction.create_reservation_restrict_union sup_ge2 ts'_def)
  qed
  }
  then show ?thesis using hmlsl.satisfies_def hmlsl.valid_def  sorry
qed

lemma reservation2: "\<Turnstile>(\<^bold>\<box>r(c) re(c)) \<^bold>\<rightarrow> (re(c) \<^bold>\<or> cl(c))" 
  using backwards_res_act traffic.always_create_res   
  by (metis (no_types, lifting) local.hmlsl.satisfies_def local.hmlsl.valid_def)
  
    
lemma reservation:"\<Turnstile>(\<^bold>\<box>r(c) re(c)) \<^bold>\<leftrightarrow> (re(c) \<^bold>\<or> cl(c))"
  using reservation1 reservation2 local.hmlsl.valid_def hmlsl.satisfies_def sorry      
end
end
  
