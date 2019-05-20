(*  Title:      perfect/HMLSL_Perfect.thy
    Author:     Sven Linker

Defines HMLSL with perfect sensors for cars. Cars can perceive both
the physical size and braking distance of all other cars.
*)

section\<open>HMLSL for Perfect Sensors\<close>
text \<open>
Within this section, we instantiate HMLSL for cars with 
perfect sensors.
\<close>


theory HMLSL_Perfect
  imports "../HMLSL" "Perfect_Sensors"
begin
  
  
locale hmlsl_perfect = perfect_sensors + restriction
begin
  
interpretation hmlsl : hmlsl "perfect :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
proof unfold_locales 
  
  fix e ts c
  show " 0 < perfect e ts c" 
    by (metis less_add_same_cancel2 less_trans perfect_def traffic.psGeZero
        traffic.sdGeZero) 
qed
  
notation hmlsl.re ("re'(_')")
notation hmlsl.cl("cl'(_')")
notation hmlsl.len ("len")

text \<open>
 The spatial atoms are independent of the perspective of the view. 
Hence we can prove several lemmas on the relation between the hybrid modality
and the spatial atoms.
\<close>
print_induct_rules
print_claset
print_rules

lemma at_res1:
  includes hmlsl.spatial_rules 
  shows "ts, v \<Turnstile>(re(c)) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<forall>d. \<^bold>@d re(c))"  
proof
  fix d
  assume 1:"ts,v \<Turnstile> re(c)"
  obtain u where "v=d>u" 
    using view.switch_exists by blast
  then have "ts,u \<Turnstile>re(c)" using 1  
    by (metis local.hmlsl.re_def local.hmlsl.satisfies_def switch_length_stable switch_restrict_stable view.switch_def)
  then show "ts,v \<Turnstile> \<^bold>@d re(c)" 
    using \<open>v = d > u\<close>  using hmlsl.atI' by (metis)
qed
    
lemma at_res2:"ts,v \<Turnstile>(\<^bold>\<forall>d. \<^bold>@d re(c)) \<Longrightarrow> ts,v \<Turnstile> re(c)" 
 using view.switch_refl local.hmlsl.atE' by blast
    
lemma at_res:"(ts,v \<Turnstile>re(c)) = (ts,v \<Turnstile> \<^bold>\<forall>d. \<^bold>@d re(c))" 
  using at_res1 at_res2 by blast
    
lemma at_res_inst:"ts,v \<Turnstile> (\<^bold>@d re(c)) \<Longrightarrow> ts,v \<Turnstile> re(c)" 
  using at_res1 switch_length_stable switch_restrict_stable  
  by (meson local.hmlsl.atE' local.hmlsl.mallE view.switch_exists view.switch_symm) 
(*proof -
  {
  fix ts v
  assume assm:"ts,v \<Turnstile>( \<^bold>@d re(c))" 
  obtain v' where v'_def:"(v=(d)> v') "
    using view.switch_always_exists by blast
  with assm have v':"ts,v' \<Turnstile> re(c)" unfolding hmlsl.satisfies_def hmlsl.at_def by blast
  with v' have "ts,v \<Turnstile>re(c)" 
    using restriction.switch_restrict_stable perfect_sensors.switch_length_stable v'_def
      view.switch_def unfolding hmlsl.satisfies_def hmlsl.re_def
    by (metis (no_types, lifting) all_own_ext_eq_len_eq)
}
  from this show ?thesis unfolding hmlsl.valid_def hmlsl.satisfies_def by blast
qed
*)

lemma at_clm1:"ts,v \<Turnstile>cl(c) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<forall>d. \<^bold>@d cl(c))"
proof
  fix d
  assume 1:"ts,v \<Turnstile> cl(c)"
  obtain u where "v=d>u" 
    using view.switch_exists by blast
  then have "ts,u \<Turnstile>cl(c)" using 1 
    by (metis local.hmlsl.cl_def local.hmlsl.satisfies_def switch_length_stable switch_restrict_stable view.switch_def)
  then show "ts,v \<Turnstile> \<^bold>@d cl(c)" 
    using \<open>v = d > u\<close> view.switch_unique 
    by (metis local.hmlsl.atI)
qed
    
lemma at_clm2:"ts,v \<Turnstile>(\<^bold>\<forall>d. \<^bold>@d cl(c)) \<Longrightarrow> ts,v \<Turnstile> cl(c)" 
 using view.switch_refl local.hmlsl.atE' by blast
  
lemma at_clm:"(ts,v \<Turnstile>cl(c)) = (ts,v \<Turnstile> \<^bold>\<forall>d. \<^bold>@d cl(c))" 
  using at_clm1 at_clm2 by blast
    
lemma at_clm_inst:"ts,v \<Turnstile> (\<^bold>@d cl(c)) \<Longrightarrow> ts,v \<Turnstile>cl(c)" 
using at_clm1 switch_length_stable switch_restrict_stable  
  by (meson local.hmlsl.atE' local.hmlsl.mallE view.switch_exists view.switch_symm) 
(*proof - 
  {
  fix ts v
  assume assm:"ts,v \<Turnstile>( \<^bold>@d cl(c))"
  obtain v' where v'_def:"(v=(d)> v') "
    using view.switch_always_exists by blast
  with assm have v':"ts,v' \<Turnstile> cl(c)" unfolding hmlsl.satisfies_def hmlsl.at_def by blast 
  with v' have "ts,v \<Turnstile>cl(c)"
    using restriction.switch_restrict_stable switch_length_stable v'_def view.switch_def 
    unfolding hmlsl.satisfies_def hmlsl.cl_def
    by (metis (no_types, lifting) all_own_ext_eq_len_eq)
} 
  from this show ?thesis unfolding hmlsl.valid_def hmlsl.satisfies_def by blast
qed
*)

text\<open>
With the definition of sensors, we can also express how the spatial situation
changes after the different transitions. In particular, we can prove 
lemmas corresponding to the activity and stability rules of the
proof system for MLSL \cite{Linker2015a}.

Observe that we were not able to prove these rules for basic HMLSL, since 
its generic sensor function allows for instantiations where the perceived length changes
during spatial transitions.
\<close>

lemma forwards_res_act:
 "(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts,v \<Turnstile> cl(c)) \<longrightarrow> (ts',v \<Turnstile> re(c))" 
  unfolding hmlsl.satisfies_def hmlsl.re_def hmlsl.cl_def 
  by (metis create_reservation_restrict_union inf_sup_aci(5) perfect_sensors.create_reservation_length_stable restriction.restrict_view sup.absorb_iff1)

lemma forwards_res_stab:
 "(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts,v \<Turnstile> re(c)) \<longrightarrow> (ts',v \<Turnstile> re(c))"
  unfolding hmlsl.satisfies_def hmlsl.re_def 
  by (metis inf.absorb1 order_trans perfect_sensors.create_reservation_length_stable restrict_def' restriction.restrict_subseteq traffic.create_res_subseteq1) 

lemma backwards_res_act:
  "(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c) \<^bold>\<or> cl(c))" 
proof
  assume assm:"(ts \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c))"
  from assm have len_eq:"len v ts c = len v ts' c"
    using create_reservation_length_stable by blast
  have "res ts c \<sqsubseteq> res ts' c" using assm traffic.create_res_subseteq1 by blast
  hence restr_subs_res:"restrict v (res ts) c \<sqsubseteq> restrict v (res ts') c"  
    using restriction.restrict_view assm unfolding hmlsl.satisfies_def hmlsl.re_def 
    by auto
  have "clm ts c \<sqsubseteq> res ts' c" using assm traffic.create_res_subseteq2 by blast
  hence restr_subs_clm:"restrict v (clm ts) c \<sqsubseteq> restrict v (res ts') c"
    using restriction.restrict_view assm unfolding hmlsl.satisfies_def hmlsl.re_def
    by auto
  have "restrict v (res ts) c = \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>" by simp
  then show " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))" 
  proof
    assume restr_res_nonempty:"restrict v (res ts) c \<noteq> \<emptyset>"
    hence restrict_one:"|restrict v (res ts) c | = 1" 
      using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym
        restr_subs_res assm unfolding hmlsl.satisfies_def hmlsl.re_def by fastforce
    have "restrict v (res ts ) c \<sqsubseteq> lan v" 
      using restr_subs_res assm unfolding hmlsl.satisfies_def hmlsl.re_def by auto
    hence "restrict v (res ts)c = lan v" 
      using restriction.restrict_eq_lan_subs restrict_one assm unfolding hmlsl.satisfies_def hmlsl.re_def by auto
    thus " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))" 
      using assm len_eq  
      using local.hmlsl.mdisjI1 local.hmlsl.re_def local.hmlsl.satisfies_def by auto
  next
    assume restr_res_empty:"restrict v (res ts) c = \<emptyset>"
    then have clm_non_empty:" restrict v (clm ts) c \<noteq> \<emptyset>" 
      using assm card_empty_zero restriction.create_reservation_restrict_union 
      unfolding hmlsl.satisfies_def hmlsl.re_def by auto
    hence restrict_one:"|restrict v (clm ts) c | = 1" 
      using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym
        restr_subs_clm assm unfolding hmlsl.satisfies_def  hmlsl.re_def by fastforce
    have "restrict v (clm ts ) c \<sqsubseteq> lan v" 
      using restr_subs_clm assm unfolding hmlsl.satisfies_def  hmlsl.re_def by auto
    hence "restrict v (clm ts)c = lan v"
      using restriction.restrict_eq_lan_subs restrict_one assm unfolding hmlsl.satisfies_def hmlsl.re_def  by auto
    thus " ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))" 
      using assm len_eq 
      using local.hmlsl.cl_def local.hmlsl.mdisjI2 local.hmlsl.re_def local.hmlsl.satisfies_def by auto
  qed
qed
  
lemma backwards_res_act_somewhere:
  "(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle>) \<longrightarrow> (ts,v \<Turnstile>\<^bold>\<langle> re(c) \<^bold>\<or> cl(c)\<^bold>\<rangle> )"
  using backwards_res_act 
  using local.hmlsl.someI local.hmlsl.somewhere_leq by auto

lemma backwards_res_stab:
  "(ts \<^bold>\<midarrow>r(d)\<^bold>\<rightarrow> ts') \<and>  (d \<noteq>c) \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
  using perfect_sensors.create_reservation_length_stable restriction.restrict_def'
    traffic.create_res_subseteq1_neq  unfolding hmlsl.satisfies_def hmlsl.re_def
  by auto
  
lemma backwards_c_res_stab:
  "(ts \<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
  using create_claim_length_stable traffic.create_clm_eq_res unfolding hmlsl.satisfies_def hmlsl.re_def 
  by (metis (mono_tags, lifting) traffic.create_claim_def) 
    
lemma backwards_wdc_res_stab:
  "(ts \<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))"
  using withdraw_claim_length_stable traffic.withdraw_clm_eq_res unfolding hmlsl.satisfies_def hmlsl.re_def 
  by (metis (mono_tags, lifting) traffic.withdraw_claim_def) 
    
lemma backwards_wdr_res_stab:
  "(ts \<^bold>\<midarrow>wdr(d,n) \<^bold>\<rightarrow> ts') \<and> (ts',v \<Turnstile> re(c)) \<longrightarrow> (ts,v \<Turnstile> re(c))" unfolding hmlsl.satisfies_def hmlsl.re_def
  by (metis inf.absorb1 order_trans perfect_sensors.withdraw_reservation_length_stable
      restriction.restrict_def' restriction.restrict_res traffic.withdraw_res_subseteq)

text\<open>
We now proceed to prove the \emph{reservation lemma}, which was 
crucial in the manual safety proof \cite {Hilscher2011}. 
\<close>


lemma reservation1: 
  includes hmlsl.dynamic_rules
  shows "ts,v \<Turnstile>(re(c) \<^bold>\<or> cl(c)) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<box>r(c) re(c)"  
  using hmlsl_perfect.forwards_res_act hmlsl_perfect.forwards_res_stab by blast
(*  using hmlsl_perfect.forwards_res_act hmlsl_perfect.forwards_res_stab local.hmlsl.satisfies_def local.hmlsl.valid_def by auto*)
(*proof -
  {
  fix ts v ts'
  assume assm:"ts,v \<Turnstile>re(c) \<^bold>\<or> cl(c)" and ts'_def:"ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts'"
  consider (re) "ts,v \<Turnstile>re(c)" | (cl) "ts,v \<Turnstile>cl(c)" 
    using assm local.hmlsl.satisfies_def by auto
  then  have "ts',v \<Turnstile>  re(c)"  
  proof (cases)
    case re
    then show ?thesis unfolding hmlsl.satisfies_def     (* hmlsl.re_def *)
      by (metis inf.absorb1 order_trans perfect_sensors.create_reservation_length_stable
           restriction.restrict_def' restriction.restrict_subseteq 
          traffic.create_res_subseteq1 ts'_def)
  next
    case cl
    then show ?thesis unfolding hmlsl.satisfies_def hmlsl.cl_def hmlsl.re_def
      by (metis inf.absorb1 order_trans perfect_sensors.create_reservation_length_stable
          restriction.restrict_def' restriction.restrict_subseteq
          traffic.create_res_subseteq2 ts'_def)
  qed
}
  from this show ?thesis unfolding hmlsl.satisfies_def hmlsl.valid_def by blast
qed
*)

lemma reservation2: 
  includes hmlsl.dynamic_rules 
  shows "ts,v \<Turnstile>(\<^bold>\<box>r(c) re(c)) \<Longrightarrow> ts,v \<Turnstile> (re(c) \<^bold>\<or> cl(c))"
  using backwards_res_act backwards_res_stab always_create_res 
  by (meson local.hmlsl.crResE)
(*  by (metis always_create_res hmlsl_perfect.backwards_res_act local.hmlsl.res_box_def local.hmlsl.satisfies_def)*)
(*  using backwards_res_act traffic.always_create_res unfolding hmlsl.valid_def hmlsl.satisfies_def by blast*)

lemma reservation:"(ts,v \<Turnstile>\<^bold>\<box>r(c) re(c)) = (ts,v \<Turnstile> re(c) \<^bold>\<or> cl(c))" 
  using reservation1 reservation2  by iprover
  (*unfolding hmlsl.valid_def unfolding hmlsl.valid_def hmlsl.satisfies_def by blast*)
end
end
  
