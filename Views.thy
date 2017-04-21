(*  Title:      Views.thy
    Author:     Sven Linker, University of Liverpool

Defines a type for views on traffic. Consists of closed real valued interval
denoting "extension" (length on the road visible", the visible interval of lanes,
and the owner of the view.

Contains chopping relations on extension and lanes and switching to
different owners.
*)

section\<open>Views on Traffic\<close>
theory Views
  imports Cars
begin
  
  
record view = 
  ext::extension 
  lan ::lanes  
  own ::cars
  
instantiation  view_ext:: (order) order
begin  
definition "less_eq_view_ext (V:: 'a view_ext)  (V':: 'a view_ext)  \<equiv> 
     ((ext V) \<le> (ext V')) \<and> (lan V \<sqsubseteq>  lan V') \<and> own V = own V' \<and> more V \<le> more V'"  
definition "less_view_ext (V :: 'a view_ext) (V':: 'a view_ext)  \<equiv> 
     ((ext V) \<le> (ext V')) \<and> (lan V \<sqsubseteq>  lan V') \<and> own V' = own V \<and>  more V \<le> more V' \<and> 
     \<not>(((ext V') \<le> (ext V)) \<and> (lan V' \<sqsubseteq>  lan V) \<and> own V' = own V  \<and> more V' \<le> more V)" 
instance   
proof
  fix v v' v''::  "'a view_ext" 
  show "v \<le> v"  using less_eq_view_ext_def less_eq_nat_int.rep_eq by auto
  show " (v < v') = (v \<le> v' \<and> \<not> v' \<le> v)" using less_eq_view_ext_def less_view_ext_def by auto
  show "v \<le> v' \<Longrightarrow> v' \<le> v'' \<Longrightarrow> v \<le> v''" using less_eq_view_ext_def less_eq_nat_int.rep_eq order_trans by auto
  show "v \<le> v' \<Longrightarrow> v' \<le> v \<Longrightarrow> v = v'"  using less_eq_view_ext_def by auto  
qed  
end 
  
  
locale view
begin

lemmas[simp] = R_Chop_dict   
  
definition       hchop :: "view \<Rightarrow> view \<Rightarrow>  view \<Rightarrow> bool" ("_=_\<parallel>_")
  where "(v=u\<parallel>w) == real_int.R_Chop(ext v)(ext u)(ext w) \<and> lan v=lan u \<and> lan v=lan w \<and> own v = own u \<and> own v = own w \<and> more v = more w  "
definition   vchop :: "view \<Rightarrow> view \<Rightarrow>  view \<Rightarrow> bool" ("_=_--_")
  where   "  (v=u--w) == (nat_int.N_Chop(lan v)(lan u)( lan w) \<and> 
                  ext v = ext u \<and> ext v = ext w 
                  \<and> own v = own u \<and> own  v = own w \<and> more v = more w) "
    
definition switch :: "view \<Rightarrow> cars \<Rightarrow> view \<Rightarrow> bool" ("_ = _ > _")
  where   "  (v=c>w) == ext v = ext w \<and> lan v = lan w \<and>  own w = c \<and> more v = more w"


lemma h_chop_middle1:"(v=u\<parallel>w) \<longrightarrow> left (ext v) \<le> right (ext u)" 
  by (metis hchop_def real_int.rchop_def real_int.left_leq_right)
    
lemma h_chop_middle2:"(v=u\<parallel>w) \<longrightarrow> right (ext v) \<ge> left (ext w)" 
  using real_int.left_leq_right real_int.rchop_def view.hchop_def by auto
    
    
lemma horizontal_chop1: " \<exists> u w. (v=u\<parallel>w)" 
proof -
  have real_chop:"\<exists>x1 x2.  R_Chop(ext v, x1,x2)" using real_int.chop_singleton_left  by force
  obtain x1 and x2 where x1_x2_def:" R_Chop(ext v, x1,x2)" using real_chop by force
  obtain V1 and V2 where v1:"V1 = \<lparr> ext = x1, lan = lan v, own = own v\<rparr>" and v2:"V2 = \<lparr> ext = x2,lan= lan v, own = own v\<rparr> "  by blast 
  from v1 and v2 have "v=V1\<parallel>V2" using hchop_def x1_x2_def by (simp)
  thus ?thesis by blast
qed
  
lemma horizontal_chop_empty_right :"\<forall>v. \<exists> u. (v=v\<parallel>u)" 
  using hchop_def real_int.chop_singleton_right 
  by (metis (no_types, hide_lams) select_convs) 
    
lemma horizontal_chop_empty_left :"\<forall>v. \<exists>u. (v=u\<parallel>v)" 
  using hchop_def real_int.chop_singleton_left 
  by (metis (no_types, hide_lams) select_convs(1) select_convs(2) select_convs(3)) 
    
lemma horizontal_chop_non_empty:"\<parallel>ext v\<parallel> > 0 \<longrightarrow> (\<exists>u w. (v=u\<parallel>w) \<and> \<parallel>ext u\<parallel> > 0 \<and> \<parallel>ext w\<parallel>>0)"
proof
  assume "\<parallel>ext v\<parallel> > 0" 
  then obtain l1 and l2 where chop:" R_Chop(ext v, l1,l2) \<and> \<parallel>l1\<parallel> > 0 \<and> \<parallel>l2\<parallel> > 0" 
    using real_int.chop_dense by force
  obtain V1 where v1_def:"V1 = \<lparr> ext = l1, lan = lan v, own = own v \<rparr>" by simp
  obtain V2 where v2_def:"V2 = \<lparr> ext = l2,lan = lan v, own = own v \<rparr>" by simp
  then have  " (v=V1\<parallel>V2) \<and> \<parallel>ext V1\<parallel> > 0 \<and> \<parallel>ext V2\<parallel>>0" 
   using  chop hchop_def v1_def by (simp)
  then show " (\<exists>V1 V2. (v=V1\<parallel>V2) \<and> \<parallel>ext V1\<parallel> > 0 \<and> \<parallel>ext V2\<parallel>>0)" by blast
qed
  
  
lemma horizontal_chop_split_add:"x \<ge> 0 \<and> y \<ge> 0 \<longrightarrow> \<parallel>ext v\<parallel> = x+y \<longrightarrow> (\<exists>u w. (v=u\<parallel>w) \<and> \<parallel>ext u\<parallel> = x \<and> \<parallel>ext w\<parallel> = y)"
proof (rule impI)+
  assume geq_0:"x \<ge> 0 \<and> y \<ge> 0" and len_v:"\<parallel>ext v\<parallel> = x+y"
  obtain V1 where v1_def: "V1 = \<lparr> ext = Abs_real_int (left (ext v), left (ext v) + x), lan = lan v, own = (own v) \<rparr>" by simp
  have v1_in_type:"(left (ext v), left (ext v) + x) \<in> {r::(real*real) . fst r \<le> snd r}" 
    by (simp add: geq_0)
  obtain V2 where v2_def: "V2 = \<lparr> ext = Abs_real_int (left (ext v)+x, left (ext v) + (x+y)), lan =  (lan v), own =  (own v) \<rparr>" by simp
  have v2_in_type:"(left (ext v)+x, left (ext v) + (x+y)) \<in> {r::(real*real) . fst r \<le> snd r}" 
    by (simp add: geq_0)
  from v1_def and geq_0 have len_v1:"\<parallel>ext V1\<parallel> = x" using v1_in_type 
    by (simp add: Abs_real_int_inverse  real_int.length_def) 
  from v2_def and geq_0 have len_v2:"\<parallel>ext V2\<parallel>= y" using v2_in_type 
    by (simp add: Abs_real_int_inverse  real_int.length_def) 
  from v1_def and v2_def have "(v=V1\<parallel>V2)" 
    using Abs_real_int_inverse fst_conv hchop_def len_v prod.collapse real_int.rchop_def real_int.length_def snd_conv v1_in_type v2_in_type by auto
  with len_v1 and len_v2 have "(v=V1\<parallel>V2) \<and> \<parallel>ext V1\<parallel> = x \<and> \<parallel>ext V2\<parallel> = y" by simp
  thus "(\<exists>V1 V2. (v=V1\<parallel>V2) \<and> \<parallel>ext V1\<parallel> = x \<and> \<parallel>ext V2\<parallel> = y)" by blast
qed
  
lemma horizontal_chop_assoc1:"(v=v1\<parallel>v2) \<and> (v2=v3\<parallel>v4) \<longrightarrow> (\<exists>v'. (v=v'\<parallel>v4) \<and> (v'=v1\<parallel>v3))"
proof
  assume assm:"(v=v1\<parallel>v2) \<and> (v2=v3\<parallel>v4)"
  obtain v' where v'_def:"v' =\<lparr> ext = Abs_real_int(left (ext v1), right (ext v3)), lan = (lan v), own = (own v) \<rparr>"
    by simp
  hence 1:"v=v'\<parallel>v4" 
    using assm real_int.chop_assoc1 hchop_def by auto
  have 2:"v'=v1\<parallel>v3" using v'_def assm real_int.chop_assoc1 hchop_def by auto
  from 1 and 2 have "(v=v'\<parallel>v4) \<and>  (v'=v1\<parallel>v3)" by best
  thus "(\<exists>v'. (v=v'\<parallel>v4)  \<and> (v'=v1\<parallel>v3))" ..
qed
  
lemma horizontal_chop_assoc2:"(v=v1\<parallel>v2) \<and> (v1=v3\<parallel>v4) \<longrightarrow> (\<exists>v'. (v=v3\<parallel>v') \<and> (v'=v4\<parallel>v2))"
proof
  assume assm:"(v=v1\<parallel>v2) \<and> (v1=v3\<parallel>v4)"
  obtain v' where v'_def:"v'=\<lparr> ext = Abs_real_int(left (ext v4),right (ext v2)), lan = (lan v), own = (own v) \<rparr>"  
    by simp
  hence 1:"v=v3\<parallel>v'" 
    using assm fst_conv real_int.chop_assoc2 snd_conv hchop_def by auto
  have 2: "v'=v4\<parallel>v2" 
    using assm real_int.chop_assoc2 v'_def hchop_def by auto
  from 1 and 2 have "(v=v3\<parallel>v') \<and> (v'=v4\<parallel>v2)" by best
  thus "(\<exists>v'. (v=v3\<parallel>v') \<and> (v'=v4\<parallel>v2))" ..
qed
  
  
  
  
lemma horizontal_chop_width_stable:"(v=u\<parallel>w) \<longrightarrow> |lan v| = |lan u| \<and> |lan v|=|lan w|"
  using hchop_def by auto
    
lemma horizontal_chop_own_trans:"(v=u\<parallel>w) \<longrightarrow> own u = own w" 
  using hchop_def by auto    
    
lemma vertical_chop1:"\<forall>v. \<exists> u w. (v=u--w)"
  using vchop_def  nat_int.chop_always_possible
  by (metis (no_types, hide_lams) select_convs)
    
lemma vertical_chop_empty_down:"\<forall>v.\<exists> u.(v=v--u)"
  using vchop_def nat_int.chop_empty_right 
  by (metis (no_types, hide_lams) select_convs)
    
    
lemma vertical_chop_empty_up:"\<forall>v.\<exists>u.(v=u--v)"
  using vchop_def nat_int.chop_empty_left 
  by (metis (no_types, hide_lams) select_convs(1) select_convs(2) select_convs(3))
    
    
lemma vertical_chop_assoc1:"(v=v1--v2) \<and> (v2=v3--v4) \<longrightarrow> (\<exists>v'. (v=v'--v4) \<and> (v'=v1--v3))"
proof
  assume assm:"(v=v1--v2) \<and> (v2=v3--v4)"
  obtain v' where v'_def:"v' =\<lparr> ext = ext v, lan= (lan v1) \<squnion>  (lan v3), own = (own v) \<rparr>"
    by simp
  then have 1:"v=v'--v4" 
    using assm nat_int.chop_assoc1 vchop_def 
    using union_dict by auto
  have 2:"v'=v1--v3" using v'_def assm nat_int.chop_assoc1 vchop_def union_dict by auto
  from 1 and 2 have "(v=v'--v4) \<and>  (v'=v1--v3)" by best
  then show "(\<exists>v'. (v=v'--v4)  \<and> (v'=v1--v3))" ..
qed
  
lemma vertical_chop_assoc2:"(v=v1--v2) \<and> (v1=v3--v4) \<longrightarrow> (\<exists>v'. (v=v3--v') \<and> (v'=v4--v2))" 
proof
  assume assm:"(v=v1--v2) \<and> (v1=v3--v4)"
  obtain v' where v'_def:"v'=\<lparr> ext = ext v, lan = (lan v4) \<squnion> (lan v2), own = (own v) \<rparr>"  
    by simp
  then have 1:"v=v3--v'" 
    using assm fst_conv nat_int.chop_assoc2 snd_conv vchop_def union_dict by auto
  have 2: "v'=v4--v2" 
    using assm nat_int.chop_assoc2 v'_def vchop_def union_dict by auto
  from 1 and 2 have "(v=v3--v') \<and> (v'=v4--v2)" by best
  then show "(\<exists>v'. (v=v3--v') \<and> (v'=v4--v2))" ..
qed

lemma vertical_chop_singleton:"(v=u--w) \<and> |lan v| = 1 \<longrightarrow> ( |lan u| = 0 \<or> |lan w| = 0)" 
  using nat_int.chop_single vchop_def Rep_nat_int_inverse 
  using card'_dict by fastforce
    
lemma vertical_chop_add1:"(v=u--w) \<longrightarrow> |lan v| = |lan u| + |lan w|"
  using nat_int.chop_add1 vchop_def 
      using card'_dict by fastforce

    
lemma vertical_chop_add2:"|lan v| = x+y \<longrightarrow> (\<exists> u w.  (v=u--w) \<and> |lan u| = x \<and> |lan w| = y)" 
proof
  assume assm:"|lan v| = x+y"
  hence add:"\<exists>i j. N_Chop(lan v, i,j) \<and> |i| = x \<and> |j| = y"
    using  card'_dict  chop_add2 by blast
  obtain i and j where l1_l2_def:"N_Chop(lan v, i,j) \<and> |i| = x \<and> |j| = y"
    using add by blast
  obtain u and w where "u=\<lparr>ext =  ext v, lan = i, own = (own v) \<rparr>"
    and "w = \<lparr> ext = ext v, lan = j, own = (own v) \<rparr> " by blast
  hence "(v=u--w) \<and> |lan u|=x \<and> |lan w|=y" 
    using l1_l2_def view.vchop_def card'_dict 
    by (simp add: N_Chop_dict)
  thus "(\<exists> u w.  (v=u--w) \<and> |lan u| = x \<and> |lan w| = y)" by blast
qed
  
lemma vertical_chop_length_stable:"(v=u--w) \<longrightarrow> \<parallel>ext v\<parallel> = \<parallel>ext u\<parallel> \<and> \<parallel>ext v\<parallel> = \<parallel>ext w\<parallel>"
  using vchop_def by auto
    
lemma vertical_chop_own_trans:"(v=u--w) \<longrightarrow> own u = own w" using vchop_def by auto    
    
lemma vertical_chop_width_mon:"(v=v1--v2) \<and> (v2=v3--v4) \<and> |lan v3| = x \<longrightarrow> |lan v| \<ge> x"
  by (metis le_add1 trans_le_add2 vertical_chop_add1)
    
lemma horizontal_chop_leq1:"(v=u\<parallel>w) \<longrightarrow> u \<le> v"
  using real_int.chop_leq1 hchop_def less_eq_view_ext_def order_refl by fastforce
    
lemma horizontal_chop_leq2:"(v=u\<parallel>w) \<longrightarrow> w \<le> v"
  using real_int.chop_leq2 hchop_def less_eq_view_ext_def order_refl by fastforce
    
lemma vertical_chop_leq1:"(v=u--w) \<longrightarrow> u \<le> v"
  using nat_int.chop_subset1 vchop_def less_eq_view_ext_def order_refl by fastforce
    
lemma vertical_chop_leq2:"(v=u--w) \<longrightarrow> w \<le> v"
  using nat_int.chop_subset2 vchop_def less_eq_view_ext_def order_refl by fastforce
    
    
lemma somewhere_leq:"v \<le> v' \<longleftrightarrow> (\<exists>v1 v2 v3 vl vr vu vd. (v'=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu))" 
proof
  assume assm:"v \<le> v'"
  hence assm_exp:"(ext v \<le> ext v') \<and> (lan v \<sqsubseteq> lan v') \<and> (own v = own v')" using less_eq_view_ext_def by auto
  obtain vl v1 v2 vr where vl:"vl = \<lparr> ext = Abs_real_int (left (ext v'), left (ext v)), lan = lan v', own =own v' \<rparr>"
    and v1:"v1= \<lparr> ext = Abs_real_int (left (ext v), right (ext v')), lan = lan v', own =own v' \<rparr>"
    and v2:"v2 = \<lparr> ext = Abs_real_int (left (ext v), right (ext v)), lan = lan v', own =own v' \<rparr>"
    and vr:"vr = \<lparr> ext = Abs_real_int (right (ext v), right (ext v')), lan = lan v', own =own v' \<rparr>" by blast
  have vl_in_type:"(left (ext v'), left (ext v)) \<in> {r::(real*real) . fst r \<le> snd r}" using less_eq_real_int_def assm_exp 
      real_int.left_leq_right snd_conv fst_conv mem_Collect_eq by simp
  have v1_in_type:"(left (ext v), right (ext v')) \<in> {r::(real*real) . fst r \<le> snd r}" using less_eq_real_int_def assm_exp 
      real_int.left_leq_right snd_conv fst_conv mem_Collect_eq 
    using order_trans by fastforce
  have v2_in_type:"(left (ext v), right (ext v)) \<in> {r::(real*real) . fst r \<le> snd r}" using less_eq_real_int_def assm_exp 
      real_int.left_leq_right snd_conv fst_conv mem_Collect_eq 
    using order_trans by fastforce
  have vr_in_type:"(right (ext v), right (ext v')) \<in> {r::(real*real) . fst r \<le> snd r}" using less_eq_real_int_def assm_exp 
      real_int.left_leq_right snd_conv fst_conv mem_Collect_eq 
    using order_trans by fastforce
  hence hchops:"(v'=vl\<parallel>v1)\<and> (v1=v2\<parallel>vr)"  using vl v1 v2 vr less_eq_real_int_def hchop_def real_int.rchop_def 
      vl_in_type  v1_in_type  v2_in_type vr_in_type Abs_real_int_inverse by auto
      
  have lanes_v2:"lan v2 = lan v'" using v2 by auto
  have own_v2:"own v2 = own v'" using v2 by auto
  have ext_v2:"ext v2 =ext v" using v2 v2_in_type Abs_real_int_inverse  by (simp add: Rep_real_int_inverse )
      
  show "(\<exists>v1 v2 v3 vl vr vu vd. (v'=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu))"
  proof (cases "lan v' = lan v")
    assume eq:"lan v' = lan v"
    obtain vd v3 vu where vd:"vd = \<lparr> ext = ext v2, lan = \<emptyset>, own = own v'\<rparr>" 
      and v3:"v3 = \<lparr> ext = ext v2, lan = lan v', own = own v' \<rparr>"
      and vu:"vu = \<lparr> ext = ext v2, lan = \<emptyset>, own = own v' \<rparr>" by blast
    hence "(v2=vd--v3) \<and> (v3=v--vu)" using vd v3 vu eq vchop_def nat_int.nchop_def nat_int.un_empty_absorb1 nat_int.un_empty_absorb2
        nat_int.inter_empty1 nat_int.inter_empty2 lanes_v2 own_v2 ext_v2 assm_exp by auto
    hence "(v'=vl\<parallel>v1)\<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu)" using hchops by auto
    thus ?thesis by blast
  next
    assume neq:"lan v' \<noteq> lan v"
    hence v'_neq_empty:"lan v' \<noteq> \<emptyset>" 
      by (metis assm_exp nat_int.card_empty_zero nat_int.card_non_empty_geq_one nat_int.card_subset_le le_0_eq)
    have "lan v = \<emptyset> \<or> lan v \<noteq> \<emptyset>" by simp
    thus ?thesis  
    proof
      assume eq:"lan v = \<emptyset>"
      obtain vd v3 vu where vd:"vd = \<lparr> ext = ext v2, lan = \<emptyset>, own = own v'\<rparr>" 
        and v3:"v3 = \<lparr> ext = ext v2, lan = lan v', own = own v' \<rparr>"
        and vu:"vu = \<lparr> ext = ext v2, lan = lan v', own = own v' \<rparr>" by blast
      hence "(v2=vd--v3) \<and> (v3=v--vu)" using vd v3 vu eq vchop_def nat_int.nchop_def nat_int.un_empty_absorb1 nat_int.un_empty_absorb2
          nat_int.inter_empty1 nat_int.inter_empty2 lanes_v2 own_v2 ext_v2 assm_exp by auto
      hence "(v'=vl\<parallel>v1)\<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu)" using hchops by auto
      thus ?thesis by blast
    next
      assume neq2:"lan v \<noteq> \<emptyset>"
      have "nat_int.minimum ( lan v) = nat_int.minimum (lan v') \<or> (nat_int.minimum ( lan v) > nat_int.minimum (lan v')) " 
        by (metis  bot_nat_int.rep_eq Min_le Rep_nat_int_inverse assm_exp finite_atLeastAtMost le_neq_implies_less nat_int.minimum_def nat_int.minimum_in nat_int.card_seq nat_int.el.rep_eq less_eq_nat_int.rep_eq neq2 subsetCE v'_neq_empty)
      show ?thesis
      proof (cases "(nat_int.minimum (lan v)) = nat_int.minimum(lan v')")
        assume  min:"nat_int.minimum ( lan v) = nat_int.minimum (lan v')"
        hence max:"nat_int.maximum (lan v) < nat_int.maximum (lan v')" 
          by (metis Rep_nat_int_inverse assm_exp atLeastatMost_subset_iff leI le_antisym nat_int.leq_max_sup nat_int.leq_min_inf nat_int.maximum_def nat_int.minimum_def nat_int.rep_non_empty_means_seq less_eq_nat_int.rep_eq neq neq2 v'_neq_empty)
        obtain vd v3 vu where vd:"vd = \<lparr> ext = ext v2, lan = \<emptyset>, own = own v'\<rparr>" 
          and v3:"v3 = \<lparr> ext = ext v2, lan = lan v', own = own v' \<rparr>"
          and vu:"vu = \<lparr> ext = ext v2, lan =  Abs_nat_int ({nat_int.maximum(lan v)+1..nat_int.maximum(lan v')}), own = own v' \<rparr>" by blast
        have vu_in_type:"{nat_int.maximum(lan v) +1 ..nat_int.maximum(lan v')} \<in> {S . (\<exists> (m::nat) n . {m..n }=S) }" using max by auto
        have consec:"nat_int.consec (lan v) (lan vu)" using max 
          by (simp add:  Suc_leI   nat_int.consec_def nat_int.leq_min_inf' nat_int.leq_nat_non_empty neq2  vu)
        have disjoint:" lan v \<sqinter>  lan vu = \<emptyset>" using consec nat_int.consec_def vu vu_in_type 
          using nat_int.consec_inter_empty by blast
        have union:"lan v' = lan v \<squnion> lan vu" using min max consec union_dict
          by (metis (no_types, lifting) Abs_nat_int_inverse One_nat_def Rep_nat_int_inverse Suc_leI add.right_neutral add_Suc_right nat_int.leq_max_sup nat_int.leq_min_inf nat_int.maximum_def nat_int.minimum_def nat_int.rep_non_empty_means_seq nat_int.union_def neq2 select_convs(2) nat_int.un_consec_seq v'_neq_empty vu vu_in_type)
        then have "(v2=vd--v3) \<and> (v3=v--vu)" using vd v3 vu vchop_def nat_int.nchop_def nat_int.un_empty_absorb1 nat_int.un_empty_absorb2
            nat_int.inter_empty1 nat_int.inter_empty2 lanes_v2 own_v2 ext_v2 assm_exp vu_in_type  Abs_nat_int_inverse  consec union disjoint
          using select_convs(1) select_convs(2) select_convs(3) N_Chop_dict union_dict by force
        hence "(v'=vl\<parallel>v1)\<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu)" using hchops by auto
        thus ?thesis by blast
      next
        assume "(nat_int.minimum (lan v)) \<noteq> nat_int.minimum (lan v')"         
        then have  min:"nat_int.minimum ( lan v) > nat_int.minimum (lan v')" using minimum_dict
        by (metis  bot_nat_int.rep_eq Min_le Rep_nat_int_inverse assm_exp finite_atLeastAtMost le_neq_implies_less nat_int.minimum_def nat_int.minimum_in nat_int.card_seq nat_int.el.rep_eq less_eq_nat_int.rep_eq neq2 subsetCE v'_neq_empty)
        show ?thesis
        proof (cases "(nat_int.maximum (lan v)) = nat_int.maximum (lan v')")
          assume max:"nat_int.maximum(lan v) = nat_int.maximum (lan v')"
          obtain vd v3 vu where vd:"vd = \<lparr> ext = ext v2, lan = Abs_nat_int ({nat_int.minimum(lan v')..nat_int.minimum(lan v)-1}), own = own v'\<rparr>" 
            and v3:"v3 = \<lparr> ext = ext v2, lan = lan v, own = own v' \<rparr>"
            and vu:"vu = \<lparr> ext = ext v2, lan = \<emptyset> , own = own v' \<rparr>" by blast
          have vd_in_type:"{nat_int.minimum(lan v') ..nat_int.minimum(lan v)-1} \<in> {S . (\<exists> (m::nat) n .  {m..n }= S) }"  by auto
              
          have consec:"nat_int.consec (lan vd) (lan v)" using min 
            by (simp add:  Suc_leI   nat_int.consec_def nat_int.leq_max_sup' nat_int.leq_nat_non_empty neq2  vd)
          have disjoint:"lan vd \<sqinter> lan v = \<emptyset>" using min consec nat_int.consec_inter_empty by auto
          have union:" lan v' = lan vd \<squnion> lan v" using min max consec neq2 union_dict
            by (smt Rep_nat_int_inverse   bot_nat_int.rep_eq atLeastatMost_empty_iff nat_int.leq_max_sup nat_int.maximum_def nat_int.consec_def nat_int.leq_min_inf' nat_int.rep_non_empty_means_seq nat_int.union_def select_convs(2) nat_int.un_consec_seq v'_neq_empty vd)
          then have "(v2=vd--v3) \<and> (v3=v--vu)" using vd v3 vu vchop_def nat_int.nchop_def nat_int.un_empty_absorb1 nat_int.un_empty_absorb2
              nat_int.inter_empty1 nat_int.inter_empty2 lanes_v2 own_v2 ext_v2 assm_exp vd_in_type  Abs_nat_int_inverse  disjoint consec union
            using select_convs(1) select_convs(2) select_convs(3) union_dict by force
          then have "(v'=vl\<parallel>v1)\<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu)" using hchops by auto
          thus ?thesis by blast
        next
          assume "(nat_int.maximum (lan v)) \<noteq> nat_int.maximum (lan v')"
          then have max:"nat_int.maximum (lan v) < nat_int.maximum (lan v')"
            by (metis assm_exp atLeastatMost_subset_iff nat_int.leq_max_sup nat_int.maximum_def nat_int.rep_non_empty_means_seq less_eq_nat_int.rep_eq neq2 order.not_eq_order_implies_strict v'_neq_empty)              
          obtain vd v3 vu where vd:"vd = \<lparr> ext = ext v2, lan = Abs_nat_int ({nat_int.minimum(lan v')..nat_int.minimum(lan v)-1}), own = own v'\<rparr>" 
            and v3:"v3 = \<lparr> ext = ext v2, lan = lan v \<squnion> lan vu, own = own v' \<rparr>"
            and vu:"vu = \<lparr> ext = ext v2, lan = Abs_nat_int ({nat_int.maximum(lan v)+1..nat_int.maximum(lan v')}) , own = own v' \<rparr>" by blast
          have vd_in_type:"{nat_int.minimum(lan v') ..nat_int.minimum(lan v)-1} \<in> {S . (\<exists> (m::nat) n . {m..n }=S)  }"  by auto
          have vu_in_type:"{nat_int.maximum(lan v) +1 ..nat_int.maximum(lan v')} \<in> {S . (\<exists> (m::nat) n . {m..n }=S)  }"  by auto
          have consec:"nat_int.consec (lan v) (lan vu)" using max 
            by (simp add:  Suc_leI   nat_int.consec_def nat_int.leq_min_inf' nat_int.leq_nat_non_empty neq2  vu)
          have v3_in_type:"{nat_int.minimum(lan v) ..nat_int.maximum(lan vu)} \<in> {S . (\<exists> (m::nat) n .  {m..n }=S)  }"  by auto
              
          have disjoint:"lan v \<sqinter> lan vu = \<emptyset>" using consec nat_int.consec_def vu vu_in_type 
            using nat_int.consec_inter_empty by blast
          have union:"lan v3 = lan v \<squnion> lan vu" using min max consec        
            by (simp add: v3)
              
          hence chop1:" (v3=v--vu)" using vd v3 vu vchop_def nat_int.nchop_def nat_int.un_empty_absorb1 nat_int.un_empty_absorb2 
            using assm_exp consec disjoint ext_v2 select_convs(1) select_convs(3) union_dict by auto
          have min_eq:"nat_int.minimum (lan v3) = nat_int.minimum (lan v)" using chop1 consec nat_int.chop_min vchop_def by blast
          have neq3:"lan v3 \<noteq> \<emptyset>" using consec inf_absorb1 nat_int.inter_empty1 nat_int.un_subset1 neq2 union union_dict by metis
          have consec2:"nat_int.consec (lan vd) (lan v3)" using min  consec union min_eq  
              Suc_leI   nat_int.consec_def nat_int.leq_max_sup' nat_int.leq_min_inf' nat_int.leq_nat_non_empty neq3  v3 vd 
            by (auto)
          have disjoint2:"lan vd \<sqinter> lan v3 = \<emptyset>" using min consec2 nat_int.consec_inter_empty  by auto
          have union2:" lan v' = lan vd \<squnion> lan v3" using min max consec2 neq3 union_dict
            by (smt Rep_nat_int_inverse atLeastatMost_empty_iff  bot_nat_int.rep_eq consec nat_int.card_seq nat_int.consec_def nat_int.leq_max_sup' nat_int.leq_min_inf' nat_int.union_def neq2 select_convs(2) nat_int.un_consec_seq union v'_neq_empty vd vu)
          then have "(v2=vd--v3) \<and> (v3=v--vu)" using vd v3  vchop_def nat_int.nchop_def nat_int.un_empty_absorb1 nat_int.un_empty_absorb2
              nat_int.inter_empty1 nat_int.inter_empty2 lanes_v2 own_v2 ext_v2 assm_exp vd_in_type  Abs_nat_int_inverse  disjoint2 consec2 union2
            using select_convs(1) select_convs(2) select_convs(3) chop1 union_dict by force
          then have "(v'=vl\<parallel>v1)\<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu)" using hchops by auto
          then show ?thesis by blast
        qed
      qed
    qed
  qed
next
  assume assm:"(\<exists>v1 v2 v3 vl vr vu vd. (v'=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu))"
  from this obtain v1 v2 v3 vl vr vu vd where " (v'=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu)" by blast
  thus "v \<le> v'" 
    by (meson horizontal_chop_leq1 horizontal_chop_leq2 order_trans vertical_chop_leq1 vertical_chop_leq2)
qed
  
  
  (* switch lemmas *)
lemma switch_unique:"(v =c> u) \<and> (v =c> w) \<longrightarrow>u = w"
  using switch_def by auto
    
lemma switch_exists:"\<exists>c u.( v=c>u)"
  using switch_def by auto
    
lemma switch_always_exists:"\<forall>c. \<exists>u. (v=c>u)"
  by (metis select_convs switch_def)
    
lemma switch_origin:" \<exists>u. (u=(own v)>v)" 
  using switch_def  by auto
    
lemma switch_refl:"(v=(own v)>v)"
  by (simp add:switch_def)
    
lemma switch_symm:"(v=c>u) \<longrightarrow> (u=(own v)>v)" 
  by (simp add:switch_def)
    
lemma switch_trans:"(v=c>u) \<and> (u=d>w) \<longrightarrow> (v=d>w)"
  by (simp add: switch_def)
    
lemma switch_triangle:"(v=c>u) \<and> (v=d>w) \<longrightarrow> (u=d>w)"
  using switch_def by auto
    
lemma switch_hchop1:"(v=v1\<parallel>v2) \<and> (v=c>v') \<longrightarrow> (\<exists> v1' v2'. (v1 =c> v1') \<and> (v2 =c> v2') \<and> (v'=v1'\<parallel>v2'))" 
  by (metis (no_types, hide_lams) select_convs view.hchop_def view.switch_def)
    
lemma switch_hchop2:"(v'=v1'\<parallel>v2') \<and> (v=c>v') \<longrightarrow> (\<exists> v1 v2. (v1 =c> v1') \<and> (v2 =c> v2') \<and> (v=v1\<parallel>v2))"
  by (metis (no_types, hide_lams) select_convs view.hchop_def view.switch_def)
    
lemma switch_vchop1:"(v=v1--v2) \<and> (v=c>v') \<longrightarrow> (\<exists> v1' v2'. (v1 =c> v1') \<and> (v2 =c> v2') \<and> (v'=v1'--v2'))"
  by (metis (no_types, hide_lams) select_convs view.vchop_def view.switch_def)
    
lemma switch_vchop2:"(v'=v1'--v2') \<and> (v=c>v') \<longrightarrow> (\<exists> v1 v2. (v1 =c> v1') \<and> (v2 =c> v2') \<and> (v=v1--v2))"
  by (metis (no_types, hide_lams) select_convs view.vchop_def view.switch_def)
    
lemma switch_leq:"u' \<le> u \<and> (v=c>u) \<longrightarrow> (\<exists>v'. (v'=c>u') \<and> v' \<le> v)" 
proof 
  assume assm: "u' \<le> u \<and> (v=c>u)"
  then have more_eq:"more v = more u" 
    using view.switch_def by blast
  then obtain v' where v'_def:"v'= \<lparr> ext =ext u', lan = lan u', own = own v\<rparr>" by blast
  have ext:"ext v' \<le> ext v" using assm switch_def 
    by (simp add: less_eq_view_ext_def v'_def)
  have lan:"lan v' \<le> lan v" using assm switch_def 
    by (simp add: less_eq_view_ext_def v'_def)
  have more:"more v' \<le> more v" using more_eq assm by simp
  have less: "v' \<le> v" using less_eq_view_ext_def ext lan more v'_def 
    by (simp add: less_eq_view_ext_def)
  have switch:"v' =c> u'" using v'_def switch_def assm 
    by (simp add: less_eq_view_ext_def)     
  show  "(\<exists>v'. ( v' = c > u') \<and> v' \<le> v)" using switch less by blast
qed
  
  
end
  
(*  lemmas[simp] = switch_dict hchop_dict vchop_dict *)
end