(*  Title:     Sensors.thy
    Author:     Sven Linker

Defines perfect sensors for cars. Cars can perceive both
the physical size and braking distance of all other cars.
*)

section\<open> HMLSL for perfect sensors\<close>
  
theory HMLSL_p
  imports "Perfect_Sensors"
begin
  
  
class hmlsl_perfect = perfect_sensors + restriction
begin
  
interpretation hmlsl : hmlsl "perfect :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
proof unfold_locales 
  
  fix e ts c
  show " 0 < perfect e ts c" 
    by (metis less_add_same_cancel2 less_trans perfect_def traffic.psGeZero traffic.sdGeZero) 
qed
  
  
notation hmlsl.re ("re'(_')")
notation hmlsl.cl("cl'(_')")
notation hmlsl.len ("len")
  
  
lemma at_res1:"\<Turnstile>(re(c)) \<^bold>\<rightarrow> (\<^bold>\<forall>d. @d re(c))" 
  by (metis (no_types, lifting) perfect_sensors.arbitrary_switch_length_stable restriction.switch_restrict_stable view.switch_def)
    
lemma at_res2:"\<Turnstile>(\<^bold>\<forall>d. @d re(c)) \<^bold>\<rightarrow> re(c)" 
  using view.switch_refl by blast
    
lemma at_res:"\<Turnstile>re(c) \<^bold>\<leftrightarrow> (\<^bold>\<forall>d. @d re(c))"
  using at_res1 at_res2 by blast
    
lemma at_res_inst:"\<Turnstile> (@d re(c)) \<^bold>\<rightarrow>re(c)"
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>( @d re(c))"
  obtain v' where v'_def:"(v=(d)> v') " using view.switch_always_exists by blast
  with assm have v':"ts,v' \<Turnstile> re(c)" by blast
  with v' show "ts,v \<Turnstile>re(c)" using restriction.switch_restrict_stable perfect_sensors.switch_length_stable v'_def view.switch_def 
    by (metis (no_types, lifting) all_own_ext_eq_len_eq)
qed
  
  
lemma at_clm1:"\<Turnstile>cl(c) \<^bold>\<rightarrow> (\<^bold>\<forall>d. @d cl(c))"
  by (metis (no_types, lifting)  all_own_ext_eq_len_eq view.switch_def restriction.switch_restrict_stable)
    
lemma at_clm2:"\<Turnstile>(\<^bold>\<forall>d. @d cl(c)) \<^bold>\<rightarrow> cl(c)"
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>(\<^bold>\<forall>d. @d cl(c))"
  obtain v' where v'_def:"(v=(own v)> v') " using view.switch_refl by auto
  with assm have v':"ts,v' \<Turnstile> cl(c)" by blast
  have "v = v'" using v'_def view.switch_refl view.switch_unique by blast
  with v' show "ts,v \<Turnstile>cl(c)" by blast
qed
  
lemma at_clm:"\<Turnstile>cl(c) \<^bold>\<leftrightarrow> (\<^bold>\<forall>d. @d cl(c))"
  using at_clm1 at_clm2 by blast
    
lemma at_clm_inst:"\<Turnstile> (@d cl(c)) \<^bold>\<rightarrow>cl(c)"
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>( @d cl(c))"
  obtain v' where v'_def:"(v=(d)> v') " using view.switch_always_exists by blast
  with assm have v':"ts,v' \<Turnstile> cl(c)" by blast
  with v' show "ts,v \<Turnstile>cl(c)" using restriction.switch_restrict_stable switch_length_stable v'_def view.switch_def 
    by (metis (no_types, lifting) all_own_ext_eq_len_eq)
qed
  
  
lemma backwards_res_act:"(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c) \<^bold>\<or> cl(c))"
proof
  assume assm:"(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c))"
  from assm have len_eq:"len v ts c = len v ts' c" using create_reservation_length_stable by blast
  have "res ts c \<sqsubseteq> res ts' c" using assm traffic.create_res_subseteq1 by blast
  hence restr_subs_res:"restrict v (res ts) c \<sqsubseteq> restrict v (res ts') c" by (simp add: restriction.restrict_view assm)
  have "clm ts c \<sqsubseteq> res ts' c" using assm traffic.create_res_subseteq2 by blast
  hence restr_subs_clm:"restrict v (clm ts) c \<sqsubseteq> restrict v (res ts') c" by (simp add: restriction.restrict_view assm)
  have "restrict v (res ts) c = \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>" by simp
  then show " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))"
  proof
    assume restr_res_nonempty:"restrict v (res ts) c \<noteq> \<emptyset>"
    hence restrict_one:"|restrict v (res ts) c | = 1" 
      using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym restr_subs_res assm 
      using card'_dict by fastforce
    have "restrict v (res ts ) c \<sqsubseteq> lan v" using restr_subs_res assm by auto
    hence "restrict v (res ts)c = lan v" using restriction.restrict_eq_lan_subs using restrict_one assm by auto
    thus " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))" using assm len_eq by auto
  next
    assume restr_res_empty:"restrict v (res ts) c = \<emptyset>"
    have "restrict v (clm ts) c = \<emptyset> \<or> restrict v (clm ts) c \<noteq> \<emptyset>" by simp
    thus " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))"
    proof
      assume clm_non_empty:"restrict v (clm ts) c \<noteq> \<emptyset>"
      hence restrict_one:"|restrict v (clm ts) c | = 1" 
        using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym restr_subs_clm assm using card'_dict by fastforce
      have "restrict v (clm ts ) c \<sqsubseteq> lan v" using restr_subs_clm assm by auto
      hence "restrict v (clm ts)c = lan v" using restriction.restrict_eq_lan_subs using restrict_one assm by auto
      thus " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))" using assm len_eq by auto
    next
      assume clm_empty:"restrict v (clm ts) c = \<emptyset>"
      hence "restrict v (clm ts) c \<squnion> restrict v (res ts) c = \<emptyset>" using nat_int.chop_empty nat_int.nchop_def restr_res_empty union_dict by auto                  
      hence "restrict v (res ts') c \<noteq> restrict v (clm ts) c \<squnion> restrict v (res ts) c"  using assm traffic.create_reservation_def 
        using nat_int.card_empty_zero assm card'_dict by auto
      hence False using restriction.create_reservation_restrict_union assm clm_empty restr_res_empty 
        by metis
      thus ?thesis by simp
    qed
  qed
qed
  
lemma backwards_res_stab:"(ts \<^bold>\<midarrow>r(d) \<^bold>\<rightarrow> ts') \<and>  (d \<noteq>c) \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
proof
  assume assm:"(ts \<^bold>\<midarrow>r(d) \<^bold>\<rightarrow> ts') \<and>  (d \<noteq>c) \<and> (ts',v \<Turnstile> re(c))"
  from assm have len_eq:"len v ts c = len v ts' c" using create_reservation_length_stable by blast
  have "res ts c = res ts' c" using assm traffic.create_res_subseteq1_neq by blast
  thus " ts,v \<Turnstile> (re(c))" using assm len_eq restriction.restrict_def by auto
qed
  
lemma backwards_c_res_stab:"(ts \<^bold>\<midarrow>c(d,n) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
  using create_claim_length_stable traffic.create_clm_eq_res 
  by (metis (mono_tags, lifting) traffic.create_claim_def) 
    
lemma backwards_wdc_res_stab:"(ts \<^bold>\<midarrow>wdc(d) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
  using withdraw_claim_length_stable traffic.withdraw_clm_eq_res 
  by (metis (mono_tags, lifting) traffic.withdraw_claim_def) 
    
lemma backwards_wdr_res_stab:"(ts \<^bold>\<midarrow>wdr(d,n) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
  using withdraw_reservation_length_stable traffic.withdraw_res_subseteq
  by (smt inf_absorb2 order_trans restriction.restrict_def restriction.restrict_res) 
    
lemma reservation1: "\<Turnstile>(re(c) \<^bold>\<or> cl(c)) \<^bold>\<rightarrow> \<^bold>\<box>r(c) re(c)"
proof (rule allI| rule impI)+ 
  fix ts v ts'
  assume assm:"ts,v \<Turnstile>re(c) \<^bold>\<or> cl(c)" and ts'_def:"ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts'"
  from assm show "ts',v \<Turnstile>  re(c)"
  proof
    assume re:"ts,v \<Turnstile>re(c)"
    have len_eq:"len v ts c = len v ts' c" using ts'_def create_reservation_length_stable by blast
    have restrict:"restrict v (res ts ) c = restrict v (res ts' ) c" 
      by (metis (no_types, lifting) inf_absorb2 order_trans re restriction.restrict_def restriction.restrict_res traffic.create_res_subseteq1 ts'_def) 
    show  re':"ts',v \<Turnstile> re(c)" using len_eq ts'_def restrict 
      using re by auto
  next
    assume cl:"ts,v \<Turnstile>cl(c)"
    have len_eq:"len v ts c = len v ts' c" using ts'_def create_reservation_length_stable by blast
    have "(clm ts) c \<sqsubseteq> res ts' c"     
      by (simp add: traffic.create_res_subseteq2 ts'_def)
    then have restrict:"restrict v (clm ts ) c \<sqsubseteq> restrict v (res ts' ) c" using traffic.create_res_subseteq2 ts'_def  less_eq_nat_int.rep_eq 
      using eq_iff by (metis (no_types) cl inf.orderE inf_commute order_trans restriction.restrict_clm restriction.restrict_def)
    show  re':"ts',v \<Turnstile> re(c)" using len_eq cl restrict 
      using  restriction.restrict_def by (simp add: inf_absorb1 inf_commute)
  qed
qed
  
lemma reservation2: "(\<Turnstile>(\<^bold>\<box>r(c) re(c)) \<^bold>\<rightarrow> (re(c) \<^bold>\<or> cl(c)))" 
  using backwards_res_act traffic.always_create_res by blast
    
lemma reservation:"\<Turnstile>(\<^bold>\<box>r(c) re(c)) \<^bold>\<leftrightarrow> (re(c) \<^bold>\<or> cl(c))"
  using reservation1 reservation2 by blast
    
lemma backwards_res_act_somewhere:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle>) \<longrightarrow> (ts,v \<Turnstile>\<^bold>\<langle> re(c) \<^bold>\<or> cl(c)\<^bold>\<rangle> )"
  using backwards_res_act by blast 
    
end
  
end
  