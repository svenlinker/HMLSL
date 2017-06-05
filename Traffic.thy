(*  Title:      Traffic.thy
    Author:     Sven Linker

Defines a type for traffic snapshots. Consists of six elements:
pos: positions of cars
res: reservations of cars
clm: claims of cars
dyn: current dynamic behaviour of cars
physical_size: the real sizes of cars
braking_distance: braking distance each car needs in emergency

Definitions for transitions between traffic snapshots.
*)

section\<open>Traffic Snapshots\<close>

theory Traffic
imports Cars
begin

text {* Definition of the traffic snapshot. The constraints on res and clm are the sanity conditions
of traffic snapshots.  *}
(*
  The definition of the type traffic snapshot already includes the sanity conditions
*)

typedef traffic = "{ts :: ((cars\<Rightarrow>real) * (cars \<Rightarrow> lanes) * (cars\<Rightarrow>lanes) *((cars\<Rightarrow> (real\<Rightarrow> real)))*(cars \<Rightarrow> real) *(cars \<Rightarrow> real)) . 
                    
                      (\<forall>c. ((fst (snd ts))) c \<sqinter> ((fst (snd (snd ts)))) c = \<emptyset> )  \<and>
                      (\<forall>c. |(fst (snd ts)) c| \<ge> 1) \<and>
                      (\<forall>c. |(fst (snd ts)) c| \<le> 2) \<and>
                      (\<forall>c. |(fst (snd (snd ts)) c)| \<le> 1) \<and>
                      (\<forall>c. |(fst (snd ts)) c| + |(fst (snd (snd ts))) c| \<le> 2) \<and>
(*                      (\<forall>c. |(fst (snd ts)) c| =2 \<longrightarrow> (\<exists>n . Rep_nat_int ((fst (snd ts)) c) = {n,n+1})) \<and>*)
                      (\<forall>c. ( (fst(snd(snd (ts)))) c \<noteq> \<emptyset> \<longrightarrow> 
                        (\<exists> n. Rep_nat_int ((fst (snd ts)) c) \<union> Rep_nat_int ((fst (snd (snd ts))) c) = {n, n+1}))) \<and>
(*                      (\<forall>c t. fst (snd (snd (snd (ts)))) c t \<ge> 0) \<and> *)
                      (\<forall>c . fst (snd (snd (snd (snd (ts))))) c > 0) \<and>
                      (\<forall>c.  snd (snd (snd (snd (snd (ts))))) c > 0)
 } "
proof -
  obtain pos where sp_def:"\<forall>c::cars. pos c = (1::real)" by force
  obtain re where re_def:"\<forall>c::cars. re c = Abs_nat_int {1}" by force
  obtain cl where cl_def:"\<forall>c::cars. cl c = \<emptyset>" by force
  obtain dyn where dyn_def:"\<forall>c::cars. \<forall>x::real . (dyn c) x  = (0::real)"  by force
  obtain ps where ps_def :"\<forall>c::cars . ps c = (1::real)" by force
  obtain sd where sd_def:"\<forall>c::cars . sd c = (1::real)" by force
  obtain ts where ts_def:"ts =  (pos,re,cl, dyn, ps, sd)" by simp

  have disj:"\<forall>c .((re c) \<sqinter> (cl c) = \<emptyset>)" by (simp add: cl_def nat_int.inter_empty1)
  have re_geq_one:"\<forall>c. |re c| \<ge> 1" by (simp add: Abs_nat_int_inverse card'_dict re_def)
  have re_leq_two:"\<forall>c. |re c| \<le> 2" using  re_def nat_int.rep_single card'_dict by auto
  have cl_leq_one:"\<forall>c. |cl c| \<le> 1" using nat_int.card_empty_zero cl_def card'_dict by auto  
  have add_leq_two:"\<forall>c . |re c| + |cl c| \<le> 2"  using nat_int.card_empty_zero cl_def re_leq_two card'_dict by (simp )
  have consec_re:" \<forall>c. |(re c)| =2 \<longrightarrow> (\<exists>n . Rep_nat_int (re c) = {n,n+1})" 
    by (simp add: Abs_nat_int_inverse  re_def card'_dict)
  have  clNextRe : "\<forall>c. ((cl c) \<noteq> \<emptyset> \<longrightarrow> (\<exists> n. Rep_nat_int (re c) \<union> Rep_nat_int (cl c) = {n, n+1}))"
    by (simp add: cl_def)
  from dyn_def have dyn_geq_zero:"\<forall>c. \<forall>x. dyn(c) x \<ge> 0" by auto
  from ps_def have ps_ge_zero:"\<forall>c. ps c > 0" by auto
  from sd_def have sd_ge_zero:"\<forall>c. sd c > 0" by auto
  
  have " ts \<in> {ts :: ((cars\<Rightarrow>real) * (cars \<Rightarrow> lanes) * (cars\<Rightarrow>lanes) *((cars\<Rightarrow> (real\<Rightarrow> real)))* (cars \<Rightarrow> real) *(cars \<Rightarrow> real)) . 
                     
                      (\<forall>c. ((fst (snd ts))) c \<sqinter> ((fst (snd (snd ts)))) c = \<emptyset> )  \<and>
                      (\<forall>c. |(fst (snd ts)) c| \<ge> 1) \<and>
                      (\<forall>c. |(fst (snd ts)) c| \<le> 2) \<and>
                      (\<forall>c. |(fst (snd (snd ts)) c)| \<le> 1) \<and>
                      (\<forall>c. |(fst (snd ts)) c| + |(fst (snd (snd ts))) c| \<le> 2) \<and>
(*                      (\<forall>c. |(fst (snd ts)) c| =2 \<longrightarrow> (\<exists>n . Rep_nat_int ((fst (snd ts)) c) = {n,n+1})) \<and>*)
                      (\<forall>c. ( (fst(snd(snd (ts)))) c \<noteq> \<emptyset> \<longrightarrow> 
                        (\<exists> n. Rep_nat_int ((fst (snd ts)) c) \<union> Rep_nat_int ((fst (snd (snd ts))) c) = {n, n+1}))) \<and>
(*                      (\<forall>c t. fst (snd (snd (snd (ts)))) c t \<ge> 0) \<and> *)
                      (\<forall>c . fst (snd (snd (snd (snd (ts))))) c > 0) \<and>
                      (\<forall>c.  snd (snd (snd (snd (snd (ts))))) c > 0)  
 } " 
    using sp_def re_def cl_def disj  re_geq_one re_leq_two cl_leq_one add_leq_two consec_re  (*dyn_geq_zero *)
      ps_def sd_def ts_def by auto
  thus ?thesis by blast
qed 

locale traffic   
begin   


definition pos::"traffic \<Rightarrow> (cars \<Rightarrow> real)"
where "pos ts \<equiv> fst (Rep_traffic ts)"


definition res::"traffic \<Rightarrow> (cars \<Rightarrow> lanes)"
where "res ts \<equiv> fst (snd (Rep_traffic ts))"

definition clm ::"traffic \<Rightarrow> (cars \<Rightarrow> lanes)"
where "clm ts \<equiv> fst (snd (snd (Rep_traffic ts)))"

definition dyn::"traffic \<Rightarrow> (cars \<Rightarrow> (real\<Rightarrow> real))"
where "dyn ts \<equiv> fst (snd (snd (snd (Rep_traffic ts))))"

definition physical_size::"traffic \<Rightarrow> (cars \<Rightarrow> real)"
where "physical_size ts \<equiv> fst (snd (snd (snd (snd (Rep_traffic ts)))))"

definition braking_distance::"traffic \<Rightarrow> (cars \<Rightarrow> real)"
where "braking_distance ts \<equiv> snd (snd (snd (snd (snd (Rep_traffic ts)))))"



lemma disjoint: "((res ts) c) \<sqinter> ((clm ts) c) = \<emptyset>"
using Rep_traffic res_def clm_def   by auto 

lemma atLeastOneRes: "1 \<le> |((res ts) c)|" 
using Rep_traffic  res_def by auto 

lemma atMostTwoRes:" |((res ts) c)| \<le> 2"
using Rep_traffic  res_def  by auto 

lemma  atMostOneClm: "|((clm ts) c)| \<le> 1" 
using Rep_traffic  clm_def  by auto 

lemma atMostTwoLanes: "|((res ts) c)| +|((clm ts) c)| \<le> 2"
using Rep_traffic  res_def clm_def  by auto 

lemma  consecutiveRes:" |((res ts)  c)| =2 \<longrightarrow> (\<exists>n . Rep_nat_int ((res ts) c) = {n,n+1})"
proof
  assume assump:"|((res ts)  c)| =2" 
  then have not_empty:"(res ts c) \<noteq> \<emptyset>" 
    by (simp add: card_non_empty_geq_one)
  from assump and card_seq have "Rep_nat_int (res ts  c) = {} \<or> (\<exists>n . Rep_nat_int (res ts c) = {n,n+1})" 
    by (metis add_diff_cancel_left' atLeastAtMost_singleton insert_is_Un nat_int.un_consec_seq one_add_one order_refl)  
  with assump show "(\<exists>n . Rep_nat_int (res ts c) = {n,n+1})" 
    using Rep_nat_int_inject bot_nat_int.rep_eq card_non_empty_geq_one 
    by (metis not_empty)
qed
  
lemma clmNextRes : "((clm ts) c) \<noteq> \<emptyset> \<longrightarrow> (\<exists> n. Rep_nat_int ((res ts) c) \<union> Rep_nat_int ((clm ts) c) = {n, n+1})"
using Rep_traffic res_def clm_def by auto 

(*lemma dynGeqZero:"\<forall>x. (dyn ts c x \<ge> 0)" 
using Rep_traffic  dyn_def by auto 
*)
lemma psGeZero:"\<forall>c. (physical_size ts c > 0)"
using Rep_traffic physical_size_def by auto 

lemma sdGeZero:"\<forall>c. (braking_distance ts c > 0)"
using Rep_traffic braking_distance_def by auto 

lemma clm_consec_res: "(clm ts) c \<noteq> \<emptyset> \<longrightarrow> nat_int.consec (clm ts c) (res ts c) \<or> nat_int.consec (res ts c) (clm ts c)"
proof
  assume assm:"clm ts c \<noteq>\<emptyset>"
  hence adj:"(\<exists> n. Rep_nat_int ((res ts) c) \<union> Rep_nat_int ((clm ts) c) = {n, n+1})" using clmNextRes by blast
  obtain n where n_def: " Rep_nat_int ((res ts) c) \<union> Rep_nat_int ((clm ts) c) = {n, n+1}" using adj
    by blast
  have disj:"res ts c \<sqinter> clm ts c = \<emptyset>" using disjoint by blast
  from n_def and disj have "n \<^bold>\<in> res ts c \<or> n \<^bold>\<in> clm ts c" 
    using UnE insertI1 nat_int.el.rep_eq el_dict by auto
  thus "nat_int.consec (clm ts c) (res ts c) \<or> nat_int.consec (res ts c) (clm ts c)"
  proof
    assume n_in_res: "n \<^bold>\<in> res ts c"
    hence suc_n_in_clm:"n+1 \<^bold>\<in> clm ts c" using el_dict
      by (metis (no_types) UnE assm disj inf.absorb_iff2 inf_sup_absorb insert_subset less_eq_nat_int.rep_eq n_def n_in_res nat_int.el.rep_eq sup.cobounded2 sup_bot.right_neutral)
    have "Rep_nat_int (res ts c) \<noteq> {n, n + 1}" 
      by (metis assm disj n_def inf_absorb1 inf_commute less_eq_nat_int.rep_eq sup.cobounded2)
    then have suc_n_not_in_res:"n+1 \<^bold>\<notin> res ts c" 
      using n_def n_in_res nat_int.el.rep_eq nat_int.not_in.rep_eq not_in_dict el_dict by auto
    have n_not_in_clm:"n \<^bold>\<notin> clm ts c" 
    proof (rule ccontr)
      assume "\<not>n \<^bold>\<notin> clm ts c" 
      then have n_in_clm:"n \<in> Rep_nat_int (clm ts c)" using nat_int.el.rep_eq nat_int.not_in.rep_eq not_in_dict el_dict by auto
      have "n \<in> Rep_nat_int (res ts c)" using n_in_res by (simp add: nat_int.el_def el_dict)
      then have "n \<in> Rep_nat_int (res ts c) \<inter> Rep_nat_int (clm ts c)" using n_in_clm by blast
      then have "n \<^bold>\<in> (res ts c \<sqinter> clm ts c)" 
        using Abs_nat_int_inverse Rep_nat_int nat_int.el_def  nat_int.inter_result inf_nat_int.rep_eq nat_int.el.rep_eq el_dict by auto
      then show False using disj using nat_int.non_empty_elem_in el_dict not_in_dict by auto
    qed 
    have max:"nat_int.maximum (res ts c) = n" using n_in_res suc_n_not_in_res nat_int.el.rep_eq nat_int.not_in.rep_eq 
      using n_def nat_int.maximum_in nat_int.non_empty_elem_in el_dict not_in_dict 
      using inf_sup_aci(4) by fastforce 
    have min:"nat_int.minimum (clm ts c) = n+1" using suc_n_in_clm n_not_in_clm nat_int.el.rep_eq nat_int.not_in.rep_eq
      using n_def nat_int.minimum_in nat_int.non_empty_elem_in  using inf_sup_aci(4)  
      using el_dict not_in.rep_eq by fastforce
    have "nat_int.consec (res ts c) (clm ts c)" using n_in_res suc_n_in_clm disj nat_int.consec_def max min el_dict not_in_dict 
      using nat_int.non_empty_elem_in by auto
    thus ?thesis by blast
  next
    assume n_in_clm: "n \<^bold>\<in> clm ts c"
    have suc_n_not_in_clm:"n+1 \<^bold>\<notin> clm ts c" 
    proof (rule ccontr)
      assume "\<not> n+1 \<^bold>\<notin> (clm ts c)"      
      then have "n+1 \<in> Rep_nat_int (clm ts c)" using nat_int.el.rep_eq nat_int.not_in.rep_eq el_dict not_in_dict by auto
      then have "|clm ts c| > 1" 
        using assm card_non_empty_geq_one el_dict n_in_clm singleton by fastforce
      then show False using atMostOneClm not_less by blast
    qed
    have n_not_in_res:"n \<^bold>\<notin> res ts c" 
    proof (rule ccontr)
      assume "\<not>n \<^bold>\<notin> res ts c" 
      then have n_in_res:"n \<in> Rep_nat_int (res ts c)"  using el_dict not_in_dict
        by (simp )
      have "n \<in> Rep_nat_int (clm ts c)" using n_in_clm el_dict by (simp )
      then have "n \<in> Rep_nat_int (res ts c) \<inter> Rep_nat_int (clm ts c)" using n_in_res by blast
      then have "n \<^bold>\<in> (res ts c \<sqinter> clm ts c)" 
        using Abs_nat_int_inverse Rep_nat_int nat_int.el_def  nat_int.inter_result 
        by (simp add: inf_nat_int.rep_eq el_dict)
      then show False using disj using nat_int.non_empty_elem_in el_dict  by auto
    qed
    have suc_n_in_res:"n+1 \<^bold>\<in> res ts c" 
    proof (rule ccontr)
      assume "\<not>n+1 \<^bold>\<in> res ts c"
      then have "n \<^bold>\<in> res ts c " 
        using n_def nat_int.el.rep_eq suc_n_not_in_clm nat_int.not_in.rep_eq el_dict not_in_dict by auto 
      then show False using n_not_in_res 
        using nat_int.el.rep_eq nat_int.not_in.rep_eq el_dict not_in_dict by auto
    qed          

    have max:"nat_int.maximum (clm ts c) = n" using n_in_clm suc_n_not_in_clm el_dict not_in_dict  
      by (smt Int_insert_right Max_singleton Un_commute assm inf_sup_absorb insert_absorb2 insert_commute nat_int.maximum_def n_def nat_int.el.rep_eq nat_int.not_in.rep_eq singleton_insert_inj_eq' subset_insert sup.cobounded2)
    have min:"nat_int.minimum (res ts c) = n+1" using suc_n_in_res n_not_in_res el_dict not_in_dict card'_dict
      by (metis (no_types, lifting) Int_insert_right Min_singleton atLeastOneRes nat_int.card_empty_zero inf_bot_right inf_sup_absorb nat_int.minimum_def n_def nat_int.el.rep_eq nat_int.not_in.rep_eq not_one_le_zero)
    have "nat_int.consec (clm ts c) (res ts c)" using n_in_clm suc_n_in_res disj nat_int.consec_def max min card'_dict
      by (metis (no_types, lifting) assm atLeastOneRes nat_int.card_empty_zero not_one_le_zero)
    thus ?thesis by blast
  qed
qed

  
definition create_claim ::" traffic\<Rightarrow>  cars \<Rightarrow>  nat \<Rightarrow> traffic \<Rightarrow> bool" ("_ \<^bold>\<midarrow>c'( _, _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>c(c,n)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)
                                \<and> |clm ts c| = 0
                                \<and> |res ts c| = 1
                                \<and> ((n+1) \<^bold>\<in> res ts c \<or> (n-1 \<^bold>\<in> res ts c))
                                \<and> (clm ts') = (clm ts)(c:=Abs_nat_int {n})"

definition withdraw_claim ::" traffic\<Rightarrow>  cars \<Rightarrow>   traffic \<Rightarrow> bool" ("_ \<^bold>\<midarrow>wdc'( _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)
                                \<and> (clm ts') = (clm ts)(c:=\<emptyset>)"


definition create_reservation ::" traffic\<Rightarrow>  cars \<Rightarrow> traffic \<Rightarrow> bool" ("_ \<^bold>\<midarrow>r'( _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)(c:=( (res ts c)\<squnion> (clm ts c) ))
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (clm ts') = (clm ts)(c:=\<emptyset>)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)"

definition withdraw_reservation ::" traffic\<Rightarrow>  cars \<Rightarrow>  nat \<Rightarrow> traffic \<Rightarrow> bool" ("_ \<^bold>\<midarrow>wdr'( _, _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>wdr(c,n)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)(c:= Abs_nat_int{n} )
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (clm ts') = (clm ts)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)
                                \<and> n \<^bold>\<in> (res ts c)
                                \<and> |res ts c| = 2"

definition drive::"traffic \<Rightarrow> real \<Rightarrow> traffic \<Rightarrow> bool" (" _ \<^bold>\<midarrow> _ \<^bold>\<rightarrow> _" 27)
  where "(ts \<^bold>\<midarrow> x \<^bold>\<rightarrow> ts') == (\<forall>c. (pos ts' c = (pos ts c) + (dyn ts c x))) 
                              \<and> (\<forall> c y. 0 \<le> y \<and> y \<le> x \<longrightarrow> dyn ts c y \<ge> 0)  
                              \<and> (res ts' = res ts)
                              \<and> (clm ts' = clm ts)
                              \<and> (dyn ts' = dyn ts)
                              \<and> (physical_size ts') = (physical_size ts)
                              \<and> (braking_distance ts') = (braking_distance ts)"

definition change_dyn::"traffic \<Rightarrow> cars \<Rightarrow> ( real \<Rightarrow> real) \<Rightarrow> traffic \<Rightarrow> bool" (" _ \<^bold>\<midarrow> dyn'(_,_') \<^bold>\<rightarrow> _" 27)
where "(ts \<^bold>\<midarrow>dyn(c, f )\<^bold>\<rightarrow> ts') == (pos ts' = pos ts) 
                              \<and> (res ts' = res ts)
                              \<and> (clm ts' = clm ts)
                              \<and> (dyn ts' = (dyn ts)(c:= f))
(*                              \<and> (\<forall>t. f t \<ge> 0) *)
                              \<and> (physical_size ts') = (physical_size ts)"

inductive evolve::"traffic \<Rightarrow> traffic \<Rightarrow> bool" ("_ \<^bold>\<leadsto> _")
where refl : "ts \<^bold>\<leadsto> ts" |
 drive:  "\<exists>x. x \<ge> 0 \<and>  ( ts \<^bold>\<midarrow>x\<^bold>\<rightarrow> ts') \<Longrightarrow> ts' \<^bold>\<leadsto> ts''    \<Longrightarrow> ts \<^bold>\<leadsto> ts''" |
 change: "\<exists>c. \<exists>f. (ts \<^bold>\<midarrow>dyn(c,f)\<^bold>\<rightarrow>ts') \<Longrightarrow> ts' \<^bold>\<leadsto> ts'' \<Longrightarrow> ts \<^bold>\<leadsto> ts''"

lemma evolve_trans:"(ts0 \<^bold>\<leadsto> ts1) \<Longrightarrow> (ts1 \<^bold>\<leadsto> ts2) \<Longrightarrow> (ts0 \<^bold>\<leadsto> ts2)"  
proof (induction rule:evolve.induct)
  case (refl ts)
  then show ?case by simp
next
  case (drive ts ts' ts'')
  then show ?case by (metis evolve.drive)
next
  case (change ts ts' ts'')
  then show ?case by (metis evolve.change)
qed
 
 
inductive abstract::"traffic \<Rightarrow> traffic \<Rightarrow> bool"  ("_ \<^bold>\<Rightarrow> _") for ts
where refl: "(ts \<^bold>\<Rightarrow> ts)" |
  evolve:"  ts \<^bold>\<Rightarrow> ts' \<Longrightarrow> ts' \<^bold>\<leadsto> ts''   \<Longrightarrow> ts \<^bold>\<Rightarrow> ts''" |
  cr_clm:" ts \<^bold>\<Rightarrow> ts' \<Longrightarrow>\<exists>c. \<exists> n.  (ts' \<^bold>\<midarrow>c(c,n)\<^bold>\<rightarrow> ts'')     \<Longrightarrow> ts \<^bold>\<Rightarrow> ts''" |
  wd_clm:"ts \<^bold>\<Rightarrow> ts'  \<Longrightarrow> \<exists>c.  (ts' \<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow> ts'') \<Longrightarrow>  ts \<^bold>\<Rightarrow> ts''" |
  cr_res:"ts \<^bold>\<Rightarrow> ts' \<Longrightarrow> \<exists>c.  (ts' \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts'') \<Longrightarrow>  ts \<^bold>\<Rightarrow> ts''" |
  wd_res:"ts \<^bold>\<Rightarrow> ts' \<Longrightarrow> \<exists>c. \<exists> n.  (ts' \<^bold>\<midarrow>wdr(c,n)\<^bold>\<rightarrow> ts'') \<Longrightarrow>  ts \<^bold>\<Rightarrow> ts''" 
  
  
lemma abs_trans:" (ts1 \<^bold>\<Rightarrow> ts2) \<Longrightarrow>(ts0 \<^bold>\<Rightarrow> ts1) \<Longrightarrow> (ts0 \<^bold>\<Rightarrow> ts2)"  
proof (induction  rule:abstract.induct    )
  case refl
  then show ?case by simp
next
  case (evolve ts' ts'')
  then show ?case 
    using traffic.evolve by blast  
next
  case (cr_clm ts' ts'')
  then show ?case 
    using traffic.cr_clm by blast 
next
  case (wd_clm ts' ts'')
  then show ?case 
    using traffic.wd_clm by blast 
next
  case (cr_res ts' ts'')
  then show ?case
    using traffic.cr_res by blast 
next
  case (wd_res ts' ts'')
  then show ?case 
    using traffic.wd_res by blast 
qed


  
    
lemma create_res_subseteq1:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<longrightarrow> res ts c \<sqsubseteq> res ts' c "
proof
  assume assm:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"
  hence "res ts' c = res ts c \<squnion> clm ts c" using create_reservation_def
    using fun_upd_apply by auto
  thus "res ts c \<sqsubseteq> res ts' c" using union_dict
    by (metis (no_types, lifting) Un_commute clm_consec_res  nat_int.un_subset2 nat_int.union_def nat_int.chop_subset1 nat_int.nchop_def)
qed
lemma create_res_subseteq2:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<longrightarrow> clm ts c \<sqsubseteq> res ts' c "
proof
  assume assm:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"
  hence "res ts' c = res ts c \<squnion> clm ts c" using create_reservation_def
    using fun_upd_apply by auto
  thus "clm ts c \<sqsubseteq> res ts' c" using union_dict
    by (metis Un_commute clm_consec_res disjoint inf_le1 nat_int.un_subset1 nat_int.un_subset2 nat_int.union_def)
qed

lemma create_res_subseteq1_neq:"(ts \<^bold>\<midarrow>r(d)\<^bold>\<rightarrow> ts') \<and> d \<noteq>c \<longrightarrow> res ts c = res ts' c "
proof
  assume assm:"(ts \<^bold>\<midarrow>r(d)\<^bold>\<rightarrow> ts') \<and> d \<noteq>c"
  thus "res ts c = res ts' c" using create_reservation_def
  using fun_upd_apply by auto
qed

lemma create_res_subseteq2_neq:"(ts \<^bold>\<midarrow>r(d)\<^bold>\<rightarrow> ts') \<and> d \<noteq>c \<longrightarrow> clm ts c= clm ts' c "
proof
  assume assm:"(ts \<^bold>\<midarrow>r(d)\<^bold>\<rightarrow> ts') \<and> d \<noteq>c"
  thus "clm ts c =  clm ts' c" using create_reservation_def
    using fun_upd_apply by auto
qed


lemma always_create_res:"\<forall>ts. \<exists>ts'. (ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"
proof
  fix ts
  show " \<exists>ts'. (ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"
  proof (cases "clm ts c = \<emptyset>")
    case True
    obtain ts' where ts'_def:"ts' = ts" by simp
    hence "ts  \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts'" 
      using create_reservation_def True fun_upd_triv nat_int.un_empty_absorb1 union_dict by auto
    thus ?thesis ..
  next
    case False
    obtain ts' where ts'_def: "ts'=  (pos ts, 
                                (res ts)(c:=( (res ts c)\<squnion> (clm ts c) )),
                                 (clm ts)(c:=\<emptyset>),
                                (dyn ts), (physical_size ts), (braking_distance ts))" 
      by blast
    have disj:"\<forall>c .(((fst (snd ts'))) c \<sqinter> ((fst (snd (snd ts')))) c = \<emptyset>)" by (simp add: disjoint nat_int.inter_empty1 ts'_def)
    have re_geq_one:"\<forall>c. |fst (snd ts') c| \<ge> 1" using card'_dict union_dict 
      by (smt One_nat_def Suc_leI Un_commute add_is_0 atLeastOneRes nat_int.card_un_add clm_consec_res fst_conv fun_upd_apply nat_int.union_def neq0_conv False snd_conv ts'_def)
    have re_leq_two:"\<forall>c. |(fst (snd ts')) c| \<le> 2" using card'_dict union_dict
      by (metis (no_types, lifting) Un_commute add.commute atMostTwoLanes atMostTwoRes nat_int.card_un_add clm_consec_res fun_upd_apply nat_int.union_def False prod.sel(1) prod.sel(2) ts'_def)
    have cl_leq_one:"\<forall>c. |(fst (snd (snd ts'))) c| \<le> 1" using atMostOneClm nat_int.card_empty_zero ts'_def card'_dict union_dict by auto
    have add_leq_two:"\<forall>c . |(fst (snd ts')) c| + |(fst (snd (snd ts'))) c| \<le> 2" using card'_dict union_dict 
      by (metis (no_types, lifting) add.right_neutral atMostTwoLanes nat_int.card_empty_zero fun_upd_apply prod.sel(1) prod.sel(2) re_leq_two ts'_def)
    have  clNextRe : "\<forall>c. (((fst (snd (snd ts'))) c) \<noteq> \<emptyset> \<longrightarrow> (\<exists> n. Rep_nat_int ((fst (snd ts')) c) \<union> Rep_nat_int (fst (snd (snd ts')) c) = {n, n+1}))"
      using clmNextRes ts'_def by auto
    have consec_re:" \<forall>c. |((fst (snd ts')) c)| =2 \<longrightarrow> (\<exists>n . Rep_nat_int ((fst (snd ts')) c) = {n,n+1})" 
    proof (rule allI|rule impI)+
      fix d
      assume assm:"|((fst (snd ts')) d)| =2"
      have "c=d \<or> c \<noteq>d" by simp
      then show "(\<exists>n . Rep_nat_int ((fst (snd ts')) d) = {n,n+1})"
      proof
        assume "c \<noteq> d"
        hence "(fst (snd ts')) d = res ts d" by (simp add: ts'_def)
        thus ?thesis using assm consecutiveRes by auto
      next
        assume eq:"c=d"
        hence def_ts'_res:"(fst (snd ts')) d = (res ts c)\<squnion> (clm ts c) " by (simp add:ts'_def)
        from False have at_least_one_clm:"|clm ts c| \<ge> 1" using nat_int.card_non_empty_geq_one card'_dict union_dict by auto
        from False have n1:"\<exists>n1. n1 \<^bold>\<in> clm ts c" by (simp add: nat_int.non_empty_elem_in el_dict )
        have n2:"\<exists>n2. n2 \<^bold>\<in> res ts c" using el_dict
          by (metis (no_types, lifting) clm_consec_res disjoint nat_int.consec_def nat_int.el.rep_eq inf_absorb1 less_eq_nat_int.rep_eq False subsetI)
        obtain n1 and n2 where n1_def:"n1 \<^bold>\<in> clm ts c" and n2_def:"n2 \<^bold>\<in> res ts c" using n1 n2 by blast
        have rep_clm:"Rep_nat_int (clm ts c) = {n1}" using n1_def atMostOneClm at_least_one_clm el_dict 
          using antisym singleton by fastforce 
        have rep_res:"Rep_nat_int (res ts c) = {n2}" using n2_def atMostTwoLanes atLeastOneRes  
          by (metis Rep_nat_int_inverse add.right_neutral add_diff_cancel_left' add_le_imp_le_right atLeastAtMost_singleton card_seq el.rep_eq el_dict empty_iff le_antisym nat_int.in_singleton one_add_one rep_clm singleton2)
        have consec:"\<exists> n. Rep_nat_int ((res ts) c) \<union> Rep_nat_int ((clm ts) c) = {n, n+1}" 
          using clmNextRes False by auto
        have n1_n2_un:"Rep_nat_int ((res ts) c) \<union> Rep_nat_int ((clm ts) c) = {n1, n2}" using
            rep_clm rep_res by simp
        have "n1 = n2+1 \<or> n2 = n1+1" using consec n1_n2_un 
          by (metis doubleton_eq_iff)
        thus ?thesis using Abs_nat_int_inverse union_dict
          by (smt Abs_nat_int_inverse Un_commute atLeastAtMost_singleton_iff def_ts'_res insert_commute mem_Collect_eq n1_n2_un nat_int.un_consec_seq nat_int.union_def order_refl rep_clm rep_res)
      qed
    qed
(*    have dyn_geq_zero: "(\<forall>c t. fst (snd (snd (snd (ts')))) c t \<ge> 0)" using ts'_def dynGeqZero by (simp ) *)
    have ps_ge_zero: "(\<forall>c . fst (snd (snd (snd (snd (ts'))))) c > 0)" using ts'_def psGeZero by (simp )
    have sd_ge_zero: "(\<forall>c . snd (snd (snd (snd (snd (ts'))))) c > 0)" using ts'_def sdGeZero by (simp )
        
    have ts'_type:"ts'\<in> {ts :: ((cars\<Rightarrow>real) * (cars \<Rightarrow> lanes) * (cars\<Rightarrow>lanes) *((cars\<Rightarrow> (real\<Rightarrow> real)))* (cars \<Rightarrow> real) *(cars \<Rightarrow> real)) . 
                      (\<forall>c. ((fst (snd ts))) c \<sqinter> ((fst (snd (snd ts)))) c = \<emptyset> )  \<and>
                      (\<forall>c. |(fst (snd ts)) c| \<ge> 1) \<and>
                      (\<forall>c. |(fst (snd ts)) c| \<le> 2) \<and>
                      (\<forall>c. |(fst (snd (snd ts)) c)| \<le> 1) \<and>
                      (\<forall>c. |(fst (snd ts)) c| + |(fst (snd (snd ts))) c| \<le> 2) \<and>
(*                      (\<forall>c. |(fst (snd ts)) c| =2 \<longrightarrow> (\<exists>n . Rep_nat_int ((fst (snd ts)) c) = {n,n+1})) \<and> *)
                      (\<forall>c. ( (fst(snd(snd (ts)))) c \<noteq> \<emptyset> \<longrightarrow> 
                        (\<exists> n. Rep_nat_int ((fst (snd ts)) c) \<union> Rep_nat_int ((fst (snd (snd ts))) c) = {n, n+1}))) \<and>
(*                      (\<forall>c t. fst (snd (snd (snd (ts)))) c t \<ge> 0) \<and> *)
                      (\<forall>c . fst (snd (snd (snd (snd (ts))))) c > 0) \<and>
                      (\<forall>c.  snd (snd (snd (snd (snd (ts))))) c > 0) 
     }"
      using  ts'_def disj  re_geq_one re_leq_two cl_leq_one add_leq_two consec_re   
        clNextRe mem_Collect_eq (*dyn_geq_zero*) ps_ge_zero  sd_ge_zero by blast
    have rep_eq:"Rep_traffic (Abs_traffic ts') = ts'" using ts'_def ts'_type Abs_traffic_inverse by blast 
    have sp_eq:"(pos (Abs_traffic ts')) = (pos ts) "  using rep_eq ts'_def
      using Rep_traffic pos_def by auto 
    have res_eq:"(res  (Abs_traffic ts')) = (res ts)(c:=( (res ts c)\<squnion> (clm ts c) ))" 
      using Rep_traffic 
        ts'_def ts'_type Abs_traffic_inverse rep_eq using res_def clm_def fstI sndI by auto
    have dyn_eq:"(dyn  (Abs_traffic ts')) = (dyn ts)" using
        Rep_traffic   
        ts'_def ts'_type Abs_traffic_inverse rep_eq using dyn_def fstI sndI by auto
    have clm_eq:"(clm  (Abs_traffic ts')) = (clm ts)(c:=\<emptyset>)" using
        ts'_def ts'_type Abs_traffic_inverse rep_eq using clm_def fstI sndI 
      using Rep_traffic 
      by fastforce 
        
        
    hence "ts  \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> Abs_traffic ts'" using ts'_def ts'_type  create_reservation_def 
        ts'_def disj  re_geq_one re_leq_two cl_leq_one add_leq_two consec_re  
        fst_conv snd_conv rep_eq sp_eq res_eq dyn_eq clm_eq 
        Rep_traffic clm_def res_def clm_def dyn_def physical_size_def braking_distance_def by auto 
        
    thus ?thesis ..
  qed
qed


lemma create_clm_eq_res:"(ts \<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow> ts')  \<longrightarrow> res ts c = res ts' c "
  using create_claim_def by auto

lemma withdraw_clm_eq_res:"(ts \<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow> ts') \<longrightarrow> res ts c= res ts' c "
  using withdraw_claim_def by auto

lemma withdraw_res_subseteq:"(ts \<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow> ts') \<longrightarrow> res ts' c \<sqsubseteq> res ts c "
  using withdraw_reservation_def order_refl less_eq_nat_int.rep_eq nat_int.el.rep_eq 
    nat_int.in_refl nat_int.in_singleton  fun_upd_apply subset_eq el_dict by fastforce

end
end