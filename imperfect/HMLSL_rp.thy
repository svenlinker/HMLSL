theory HMLSL_rp
  imports Regular_Sensors
begin
  
  locale hmlsl_regular = regular_sensors + restriction
  begin
  interpretation hmlsl : hmlsl "regular :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
  proof unfold_locales 
  
  fix e ts c
  show " 0 < regular e ts c"  
    by (metis less_add_same_cancel2 less_trans regular_def traffic.psGeZero traffic.sdGeZero) 
qed
print_facts
  print_locale!hmlsl_regular

  notation hmlsl.re ("re'(_')")
  notation hmlsl.cl("cl'(_')")
  notation hmlsl.len ("len")

(*context regular_sensors 
begin
  
abbreviation mtrue  :: "\<sigma>" ("\<^bold>\<top>")
  where "\<^bold>\<top> \<equiv> \<lambda> ts w. True" 
abbreviation mfalse :: "\<sigma>" ("\<^bold>\<bottom>") 
  where "\<^bold>\<bottom> \<equiv> \<lambda> ts w. False"   
abbreviation mnot   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda> ts w. \<not>\<phi>(ts)(w)" 
abbreviation mnegpred :: "(cars\<Rightarrow>\<sigma>)\<Rightarrow>(cars\<Rightarrow>\<sigma>)" ("\<^sup>\<not>_"[52]53) 
  where "\<^sup>\<not>\<Phi> \<equiv> \<lambda>x.\<lambda> ts w. \<not>\<Phi>(x)(ts)(w)"   
abbreviation mand   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51)
  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<and>\<psi>(ts)(w)"   
abbreviation mor    :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50)
  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<or>\<psi>(ts)(w)"   
abbreviation mimp   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) 
  where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<longrightarrow>\<psi>(ts)(w)"  
abbreviation mequ   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48)
  where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<longleftrightarrow>\<psi>(ts)(w)"  
abbreviation mforall   :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>")      
  where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda> ts w.\<forall>x. \<Phi>(x)(ts)(w)"
abbreviation mforallB  :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9)
  where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"   
abbreviation mexists   :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") 
  where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda> ts w.\<exists>x. \<Phi>(x)(ts)(w)"
abbreviation mexistsB  :: "(('a)\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9)
  where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"   
abbreviation meq    :: "'a\<Rightarrow>'a\<Rightarrow>\<sigma>" (infixr"\<^bold>="60) -- "Equality"  
  where "x\<^bold>=y \<equiv> \<lambda> ts w. x = y"
abbreviation mgeq :: "('a::ord) \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infix "\<^bold>\<ge>" 60)
  where "x \<^bold>\<ge> y \<equiv> \<lambda> ts w. x \<ge> y" 
abbreviation mge ::"('a::ord) \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infix "\<^bold>>" 60)
  where "x \<^bold>> y \<equiv> \<lambda> ts w. x > y" 
abbreviation hchop   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<frown>" 53)
  where "\<phi> \<^bold>\<frown> \<psi> \<equiv> \<lambda> ts w.\<exists>v u. (w=v\<parallel>u) \<and> \<phi>(ts)(v)\<and>\<psi>(ts)(u)"
abbreviation vchop   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<smile>" 53)
  where "\<phi> \<^bold>\<smile> \<psi> \<equiv> \<lambda> ts w.\<exists>v u. (w=v--u) \<and> \<phi>(ts)(v) \<and> \<psi>(ts)(u)"
abbreviation somewhere ::"\<sigma>\<Rightarrow>\<sigma>" ( "\<^bold>\<langle>_\<^bold>\<rangle> " 55)
  where "\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<equiv> \<^bold>\<top> \<^bold>\<frown> (\<^bold>\<top>\<^bold>\<smile>\<phi> \<^bold>\<smile>\<^bold>\<top>)\<^bold>\<frown>\<^bold>\<top>"
abbreviation everywhere::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>[_\<^bold>]" 55)
  where "\<^bold>[\<phi>\<^bold>] \<equiv> \<^bold>\<not>\<^bold>\<langle>\<^bold>\<not>\<phi>\<^bold>\<rangle>"
abbreviation res_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>r'(_') _" 55)
  where "\<^bold>\<box>r(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts'. (ts\<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)" 
abbreviation clm_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>c'(_') _" 55)
  where "\<^bold>\<box>c(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts' n. (ts\<^bold>\<midarrow>c(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)"
abbreviation wdres_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>wdr'(_') _" 55)
  where "\<^bold>\<box>wdr(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts' n. (ts\<^bold>\<midarrow>wdr(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)"
abbreviation wdclm_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>wdc'(_') _" 55)
  where "\<^bold>\<box>wdc(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts'. (ts\<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)"
abbreviation time_box::"\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>\<^bold>\<tau> _" 55) 
  where "\<^bold>\<box>\<^bold>\<tau> \<phi> \<equiv> \<lambda>ts w. \<forall>ts'. (ts\<^bold>\<leadsto>ts') \<longrightarrow> \<phi>(ts')(move ts ts' w)" 
abbreviation globally::"\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>G _" 55)
  where "\<^bold>G \<phi> \<equiv> \<lambda>ts w. \<forall>ts'. (ts \<^bold>\<Rightarrow> ts') \<longrightarrow> \<phi>(ts')(move ts ts' w)"
abbreviation at :: "cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma> " ("@ _ _" 50)
  where "@c \<phi> \<equiv> \<lambda>ts w .  \<forall>v'. (w=c>v') \<longrightarrow> \<phi>(ts)(v')"
    
abbreviation re:: "cars \<Rightarrow> \<sigma>" ("re'(_')" 70)
  where "re(c) \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel>> 0 \<and> len v ts c = ext v \<and>  restrict v (res ts) c = lan v \<and>  |lan v|=1" 
    
abbreviation cl:: "cars \<Rightarrow> \<sigma>" ("cl'(_')" 70)
  where "cl(c) \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel>> 0 \<and> len v ts c = ext v \<and> restrict v (clm ts) c = lan v \<and> |lan v| = 1" 
    
abbreviation free:: "\<sigma>" ("free")
  where "free ==  \<lambda> ts v. \<parallel>ext v\<parallel> > 0 \<and> |lan v| = 1 \<and>
                  (\<forall>c.  \<parallel>len v ts c\<parallel> = 0 \<or> ((restrict v (clm ts) c = \<emptyset>) \<and> (restrict v (res ts) c = \<emptyset>)))"  
    
abbreviation width_eq::"nat \<Rightarrow> \<sigma>" ("\<^bold>\<omega> = _ " 60)
  where "\<^bold>\<omega> = n == \<lambda>  ts v. |lan v| = n"  
    
abbreviation width_geq::"nat \<Rightarrow> \<sigma>" ("\<^bold>\<omega> \<ge> _" 60)
  where "\<^bold>\<omega> \<ge> n == \<lambda>  ts v. |lan v| \<ge> n" 
    
abbreviation width_ge::"nat \<Rightarrow> \<sigma>" ("\<^bold>\<omega> > _" 60)
  where "\<^bold>\<omega> > n == (\<^bold>\<omega> = n+1) \<^bold>\<smile> \<^bold>\<top>"
    
abbreviation length_eq::"real \<Rightarrow> \<sigma>" ("\<^bold>\<l> = _ " 60)
  where "\<^bold>\<l> = r == \<lambda> ts v. \<parallel>ext v\<parallel> = r"
    
abbreviation length_ge:: "real \<Rightarrow> \<sigma>" ("\<^bold>\<l> > _" 60)
  where "\<^bold>\<l> > r == \<lambda> ts v. \<parallel>ext v\<parallel> > r"
    
abbreviation length_geq::"real \<Rightarrow> \<sigma>" ("\<^bold>\<l> \<ge> _" 60)
  where "\<^bold>\<l> \<ge> r == (\<^bold>\<l> = r) \<^bold>\<or> (\<^bold>\<l> > r)"
    
abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("\<Turnstile> _" 10 )
  where "\<Turnstile> \<phi> \<equiv>  \<forall>ts. \<forall>V. \<phi>(ts)(V)"
    
abbreviation satisfies::" traffic \<Rightarrow> view \<Rightarrow> \<sigma> \<Rightarrow> bool" ("_ , _ \<Turnstile> _" 10)
  where "ts, v \<Turnstile> \<phi> == \<phi>(ts)(v)" *)
    declare[[show_consts]]
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
      using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym restr_subs_res assm card'_dict by fastforce
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
        using nat_int.card_non_empty_geq_one nat_int.card_subset_le dual_order.antisym restr_subs_clm assm card'_dict by fastforce
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
  