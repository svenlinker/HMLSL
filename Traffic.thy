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
text\<open>
Traffic snapshots define the spatial and dynamical arrangement of cars
on the whole of the motorway at a single point in time. A traffic snapshot
consists of several functions assigning spatial properties and dynamical
behaviour to each car. The functions are named as follows.
\begin{itemize}
\item pos: positions of cars
\item res: reservations of cars
\item clm: claims of cars
\item dyn: current dynamic behaviour of cars
\item physical\_size: the real sizes of cars
\item braking\_distance: braking distance each car needs in emergency
\end{itemize}
\<close>

theory Traffic
imports NatInt RealInt Cars
begin
type_synonym lanes = nat_int
type_synonym extension = real_int

record snapshot =
  pos :: "cars \<Rightarrow> real"
  res :: "cars \<Rightarrow> lanes"
  clm :: "cars \<Rightarrow> lanes"
  dyn :: "cars \<Rightarrow> real \<Rightarrow> real"
  physical_size ::" cars \<Rightarrow> real"
  braking_distance :: "cars \<Rightarrow> real"

print_theorems

definition sane :: "snapshot \<Rightarrow> bool"
  where "sane ts ==  (\<forall>c.(res ts c \<sqinter> clm ts c) = \<emptyset>)
                   \<and> (\<forall>c. continuous (res ts c))
                   \<and> (\<forall>c. continuous (clm ts c))
                   \<and> (\<forall>c. |res ts c| \<ge> 1 )
                   \<and> (\<forall>c. |res ts c| \<le> 2)
                   \<and> (\<forall>c. |clm ts c| \<le> 1)
                   \<and> (\<forall>c. |res ts c| + |clm ts c| \<le> 2)
                   \<and> (\<forall>c. clm ts c \<noteq> \<emptyset> \<longrightarrow>( \<exists>n. n \<^bold>\<in> clm ts c \<squnion> res ts c \<and> (n+1) \<^bold>\<in> clm ts c \<squnion> res ts c )) \<comment>\<open>fix his!\<close>
                   \<and> (\<forall>c. physical_size ts c > 0)
                   \<and> (\<forall>c. braking_distance ts c > 0)  " 

text \<open>Definition of the type of traffic snapshots. 
The constraints on the different functions are the \emph{sanity conditions}
of traffic snapshots.\<close>
(*
typedef traffic = 
  "{ts :: (cars\<Rightarrow>real)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>real\<Rightarrow>real)*(cars\<Rightarrow>real)*(cars\<Rightarrow>real).
          (\<forall>c. ((fst (snd ts))) c \<sqinter> ((fst (snd (snd ts)))) c = \<emptyset> )  \<and>
          (\<forall>c. |(fst (snd ts)) c| \<ge> 1) \<and>
          (\<forall>c. |(fst (snd ts)) c| \<le> 2) \<and>
          (\<forall>c. |(fst (snd (snd ts)) c)| \<le> 1) \<and>
          (\<forall>c. |(fst (snd ts)) c| + |(fst (snd (snd ts))) c| \<le> 2) \<and>
          (\<forall>c. (fst(snd(snd (ts)))) c \<noteq> \<emptyset> \<longrightarrow>
                (\<exists> n. Rep_nat_int(fst (snd ts) c)\<union>Rep_nat_int(fst (snd (snd ts)) c)
                      = {n, n+1})) \<and>
          (\<forall>c . fst (snd (snd (snd (snd (ts))))) c > 0) \<and>
          (\<forall>c.  snd (snd (snd (snd (snd (ts))))) c > 0)
 } "
proof -
  let ?type = 
    "{ts ::(cars\<Rightarrow>real)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>real\<Rightarrow>real)*(cars\<Rightarrow>real)*(cars\<Rightarrow>real).
           (\<forall>c. ((fst (snd ts))) c \<sqinter> ((fst (snd (snd ts)))) c = \<emptyset> )  \<and>
           (\<forall>c. |(fst (snd ts)) c| \<ge> 1) \<and>
           (\<forall>c. |(fst (snd ts)) c| \<le> 2) \<and>
           (\<forall>c. |(fst (snd (snd ts)) c)| \<le> 1) \<and>
           (\<forall>c. |(fst (snd ts)) c| + |(fst (snd (snd ts))) c| \<le> 2) \<and>
           (\<forall>c. (fst(snd(snd (ts)))) c \<noteq> \<emptyset> \<longrightarrow> 
                (\<exists> n. Rep_nat_int(fst (snd ts) c)\<union>Rep_nat_int(fst (snd (snd ts)) c)
                  = {n, n+1})) \<and>
           (\<forall>c . fst (snd (snd (snd (snd (ts))))) c > 0) \<and>
           (\<forall>c.  snd (snd (snd (snd (snd (ts))))) c > 0)  
 }"
  obtain pos where sp_def:"\<forall>c::cars. pos c = (1::real)" by force
  obtain re where re_def:"\<forall>c::cars. re c = Abs_nat_int {1}" by force
  obtain cl where cl_def:"\<forall>c::cars. cl c = \<emptyset>" by force
  obtain dyn where dyn_def:"\<forall>c::cars. \<forall>x::real . (dyn c) x  = (0::real)"  by force
  obtain ps where ps_def :"\<forall>c::cars . ps c = (1::real)" by force
  obtain sd where sd_def:"\<forall>c::cars . sd c = (1::real)" by force
  obtain ts where ts_def:"ts =  (pos,re,cl, dyn, ps, sd)" by simp

  have disj:"\<forall>c .((re c) \<sqinter> (cl c) = \<emptyset>)" 
    by (simp add: cl_def nat_int.inter_empty1)
  have re_geq_one:"\<forall>c. |re c| \<ge> 1" 
    by (simp add: Abs_nat_int_inverse re_def)
  have re_leq_two:"\<forall>c. |re c| \<le> 2" 
    using re_def nat_int.rep_single by auto
  have cl_leq_one:"\<forall>c. |cl c| \<le> 1"
    using nat_int.card_empty_zero cl_def by auto
  have add_leq_two:"\<forall>c . |re c| + |cl c| \<le> 2"
    using nat_int.card_empty_zero cl_def re_leq_two by (simp )
  have consec_re:" \<forall>c. |(re c)| =2 \<longrightarrow> (\<exists>n . Rep_nat_int (re c) = {n,n+1})" 
    by (simp add: Abs_nat_int_inverse  re_def)
  have  clNextRe :
    "\<forall>c. ((cl c) \<noteq> \<emptyset> \<longrightarrow> (\<exists> n. Rep_nat_int (re c) \<union> Rep_nat_int (cl c) = {n, n+1}))"
    by (simp add: cl_def)
  from dyn_def have dyn_geq_zero:"\<forall>c. \<forall>x. dyn(c) x \<ge> 0" 
    by auto
  from ps_def have ps_ge_zero:"\<forall>c. ps c > 0" by auto
  from sd_def have sd_ge_zero:"\<forall>c. sd c > 0" by auto
  
  have "ts\<in>?type"
    using sp_def re_def cl_def disj re_geq_one re_leq_two cl_leq_one add_leq_two
      consec_re ps_def sd_def ts_def by auto
  thus ?thesis by blast
qed 
*)
typedef traffic = "{ts. sane ts}" 
proof - 
  obtain pos where sp_def:"\<forall>c::cars. pos c = (1::real)" by force
  obtain re where re_def:"\<forall>c::cars. re c = Abs_nat_int {1}" by force
  obtain cl where cl_def:"\<forall>c::cars. cl c = \<emptyset>" by force
  obtain dyn where dyn_def:"\<forall>c::cars. \<forall>x::real . (dyn c) x  = (0::real)"  by force
  obtain ps where ps_def :"\<forall>c::cars . ps c = (1::real)" by force
  obtain sd where sd_def:"\<forall>c::cars . sd c = (1::real)" by force
  obtain ts where ts_def:"ts =  \<lparr>pos = pos,res = re,clm =cl, dyn = dyn, physical_size = ps, braking_distance =sd \<rparr>" by simp
  have 0:"\<forall>c.  \<forall>l. l \<in> {1} \<longleftrightarrow> l \<^bold>\<in> (res ts c)" using re_def ts_def 
    by (simp add: Abs_nat_int_inverse)
  then have 1:"\<forall>c. continuous (res ts c)" using nat_int.singleton_continuous 
    by blast
  have 2: "\<forall>c. continuous (clm ts c)" using empty_continuous ts_def cl_def by auto
  have 3: "(\<forall>c. clm ts c \<noteq> \<emptyset> \<longrightarrow>( \<exists>n. n \<^bold>\<in> clm ts c \<squnion> res ts c \<and> (n+1) \<^bold>\<in> clm ts c \<squnion> res ts c ))" using cl_def ts_def by simp
  have "sane ts" 
    using card_empty_zero cl_def nat_int.inter_empty1 ps_def re_def  sane_def sd_def ts_def 1 2 3 
    by (simp add: Abs_nat_int_inverse)  
  then have  "ts \<in> {ts. sane ts}" by simp
  then show ?thesis by blast
qed 
setup_lifting type_definition_traffic


locale traffic
begin   

notation nat_int.consec ("consec")

text\<open>For brevity, we define names for the different functions
within a traffic snapshot.\<close>

lift_definition pos :: "traffic \<Rightarrow> (cars \<Rightarrow> real)" is snapshot.pos .
lift_definition res :: "traffic \<Rightarrow> (cars \<Rightarrow> nat_int)" is snapshot.res .
lift_definition clm :: "traffic \<Rightarrow> (cars \<Rightarrow> nat_int)" is snapshot.clm .
lift_definition dyn :: "traffic \<Rightarrow> (cars \<Rightarrow> real \<Rightarrow> real)" is snapshot.dyn .
lift_definition physical_size :: "traffic \<Rightarrow> (cars \<Rightarrow> real)" is snapshot.physical_size .
lift_definition braking_distance :: "traffic \<Rightarrow> (cars \<Rightarrow> real)" is snapshot.braking_distance .

(*definition pos::"traffic \<Rightarrow> (cars \<Rightarrow> real)"
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
*)

text \<open>
It is helpful to be able to refer to the sanity conditions of a traffic 
snapshot via lemmas, hence we prove that the sanity conditions hold
for each traffic snapshot.
\<close>

lemma disjoint: "(res ts c) \<sqinter> (clm ts c) = \<emptyset>"
  using Rep_traffic res.rep_eq clm.rep_eq sane_def by auto
  
lemma atLeastOneRes: "1 \<le> |res ts c|" 
  using Rep_traffic res.rep_eq sane_def by auto

lemma atMostTwoRes:" |res ts c| \<le> 2"
  using Rep_traffic res.rep_eq sane_def by auto

lemma  atMostOneClm: "|clm ts c| \<le> 1" 
  using Rep_traffic clm.rep_eq sane_def by auto

lemma atMostTwoLanes: "|res ts c| +|clm ts c| \<le> 2"
  using Rep_traffic res.rep_eq clm.rep_eq sane_def by auto

lemma  consecutiveRes:" |res ts  c| =2 \<longrightarrow> (\<exists>n . n \<^bold>\<in> (res ts c) \<and> (n+1) \<^bold>\<in> (res ts c))" 
proof
  assume assm:"|res ts  c| =2" 
  then have not_empty:"(res ts c) \<noteq> \<emptyset>" 
    by (simp add: card_non_empty_geq_one)
  obtain m and n where "\<forall>l. l \<in> {m..n} \<longleftrightarrow> l\<^bold>\<in> (res ts c)" 
    by (metis Rep_traffic continuous_nonE_atLeastAtMost mem_Collect_eq not_empty sane_def  traffic.res.rep_eq ) 
  then have "card {m..n} = 2" using assm atLeastAtMost_card by simp
  from this and assm have "n = m +1" 
    by simp 
  show "\<exists>n. n \<^bold>\<in> res ts c \<and> n + 1 \<^bold>\<in> res ts c" 
    using \<open>\<forall>l. (l \<in> {m..n}) = (l \<^bold>\<in> local.res ts c)\<close> \<open>n = m + 1\<close> le_eq_less_or_eq by auto
qed

 
(*
  have "Rep_nat_int (res ts  c) = {} \<or> (\<exists>n . Rep_nat_int (res ts c) = {n,n+1})" 
    by (metis add_diff_cancel_left' atLeastAtMost_singleton insert_is_Un nat_int.un_consec_seq
        one_add_one order_refl)  

  with assump show "(\<exists>n . Rep_nat_int (res ts c) = {n,n+1})" 
    using Rep_nat_int_inject bot_nat_int.rep_eq card_non_empty_geq_one 
    by (metis not_empty)
qed
*)  
lemma clmNextRes : 
  "(clm ts c) \<noteq> \<emptyset> \<longrightarrow> (\<exists> n. n \<^bold>\<in> res ts c \<squnion> clm ts c \<and> (n+1) \<^bold>\<in> res ts c \<squnion> clm ts c )"
  using res_def clm_def sane_def 
  by (metis Rep_traffic mem_Collect_eq sup_commute traffic.clm.rep_eq traffic.res.rep_eq)

lemma psGeZero:"\<forall>c. (physical_size ts c > 0)"
  using sane_def Rep_traffic traffic.physical_size.rep_eq by auto

lemma sdGeZero:"\<forall>c. (braking_distance ts c > 0)"
  using sane_def Rep_traffic braking_distance.rep_eq by auto 


lemma res_non_empty: "res ts c \<noteq> \<emptyset>"
 using sane_def  Rep_traffic res.rep_eq
  by (simp add: card_non_empty_geq_one)

text \<open>
While not a sanity condition directly, the following lemma helps to establish
general properties of HMLSL later on. It is a consequence of clmNextRes. 
\<close>

lemma clm_two_lanes: "clm ts c \<noteq> \<emptyset> \<longrightarrow> |clm ts c \<squnion> res ts c| = 2"
proof
  assume assm:"clm ts c \<noteq> \<emptyset>"
  have 1:"|res ts c| \<ge> 1" 
    using card_non_empty_geq_one traffic.res_non_empty by auto
  have 2:"|clm ts c| \<ge> 1"   
    using \<open>local.clm ts c \<noteq> bot\<close> card_non_empty_geq_one by blast
  have "clm ts c \<sqinter> res ts c = \<emptyset>" using sane_def 
    by (metis Rep_traffic clm.rep_eq inf_aci(1) mem_Collect_eq res.rep_eq)
  then have 3:"|clm ts c| + |res ts c| = |clm ts c \<squnion> res ts c|" 
    using card_un_add by auto
  then have "|clm ts c \<squnion> res ts c| \<ge> 2" using sane_def 1 2 
    by linarith
  have "|clm ts c \<squnion> res ts c| \<le> 2" using assm sane_def 3  
    by (metis "2" Rep_traffic add_numeral_left clm.rep_eq le_antisym mem_Collect_eq not_less_eq_eq numeral_One numeral_plus_numeral one_add_one plus_1_eq_Suc res.rep_eq)
  then show "|clm ts c \<squnion> res ts c| = 2" 
    using \<open>2 \<le> |local.clm ts c \<squnion> local.res ts c|\<close> le_antisym by blast
qed  
  
lemma clm_consec_res:
" (clm ts c) \<noteq> \<emptyset> \<longrightarrow> consec (clm ts c) (res ts c) \<or> consec (res ts c) (clm ts c)" 
proof
  assume "(clm ts c) \<noteq> \<emptyset>"
  then obtain n where 0:" n \<^bold>\<in> clm ts c \<squnion> res ts c \<and> (n+1) \<^bold>\<in> clm ts c \<squnion> res ts c" using sane_def 
    by (metis sup_commute traffic.clmNextRes)
  have "|clm ts c \<squnion> res ts c| = 2" 
    using \<open>local.clm ts c \<noteq> bot\<close> traffic.clm_two_lanes by blast
  have 1:"clm ts c \<sqinter> res ts c = \<emptyset>" using sane_def 
    by (metis Rep_traffic clm.rep_eq inf_aci(1) mem_Collect_eq res.rep_eq)
  have 2:"|clm ts c| = 1" using sane_def 
    by (metis "1" \<open>local.clm ts c \<noteq> bot\<close> \<open>|local.clm ts c \<squnion> local.res ts c| = 2\<close> add_le_same_cancel1 card_non_empty_geq_one card_un_add le_antisym not_less_eq_eq one_add_one plus_1_eq_Suc traffic.res_non_empty)
  have 3:"|res ts c| = 1" using sane_def 
    using "1" "2" \<open>local.clm ts c \<noteq> bot\<close> \<open>|local.clm ts c \<squnion> local.res ts c| = 2\<close> card_non_empty_geq_one card_un_add by auto
  show "consec (clm ts c) (res ts c) \<or> consec (res ts c) (clm ts c)"
  proof (cases "n \<^bold>\<in> clm ts c")
    case True
    then have 4:" n \<^bold>\<notin> res ts c" using 1 excl_el1 by blast
    have "(n+1) \<^bold>\<in> clm ts c \<squnion> res ts c" using 0 by blast
    have "(n+1) \<^bold>\<notin> clm ts c" using 2 True singleton 
      by (metis add_eq_self_zero in_not_in_iff2 one_neq_zero singletonD)
    then have "(n+1) \<^bold>\<in> res ts c" using 1 2 3 4 singleton un_excl_el1 
      using \<open>n + 1 \<^bold>\<in> local.clm ts c \<squnion> local.res ts c\<close> by blast
    then show ?thesis 
      by (metis "2" "3" True \<open>local.clm ts c \<noteq> bot\<close> consec_def maximum_in minimum_in singleton singletonD traffic.res_non_empty)
  next
    case False
    then have "n \<^bold>\<notin> clm ts c" by auto
    then have 4:"(n+1) \<^bold>\<in> clm ts c" 
      by (metis "0" "1" "3" add_eq_self_zero in_not_in_iff1 one_neq_zero singleton singletonD un_excl_el1)
    have "n \<^bold>\<in> res ts c" 
      using "0" "1" \<open>n \<^bold>\<notin> local.clm ts c\<close> un_excl_el1 by blast
    then show ?thesis using 4  
        by (metis "2" "3"  \<open>local.clm ts c \<noteq> bot\<close> consec_def maximum_in minimum_in singleton singletonD traffic.res_non_empty)
  qed
qed

(*proof (rule impI)+
  assume assm:"clm (ts::traffic) c \<noteq>\<emptyset>"
  hence adj:"(\<exists> n. res ts c \<squnion> clm ts c = Abs_nat_int{n, n+1})" 
    using clmNextRes by blast
  obtain n where n_def:"res ts c \<squnion> clm ts c = Abs_nat_int{n, n+1}" 
    using adj by blast
  have disj:"res ts c \<sqinter> clm ts c = \<emptyset>"  
    using Rep_traffic clm.rep_eq res.rep_eq sane_def by auto
  from n_def and disj 
    have "(n \<^bold>\<in> res ts c \<and> n \<^bold>\<notin> clm ts c) \<or> (n \<^bold>\<in> clm ts c \<and> n \<^bold>\<notin> res ts c)" 
      by (metis UnE bot_nat_int.rep_eq disjoint_insert(1) el.rep_eq inf_nat_int.rep_e q
          insertI1 insert_absorb not_in.rep_eq) 
  thus "consec (clm ts c) (res ts c) \<or> consec (res ts c) (clm ts c)" 
  proof
    assume n_in_res: "n \<^bold>\<in> res ts c \<and>  n \<^bold>\<notin> clm ts c"
    hence suc_n_in_clm:"n+1 \<^bold>\<in> clm ts c" 
      by (metis UnCI assm el.rep_eq in_not_in_iff1 insert_iff n_def non_empty_elem_ in 
          singletonD)
    have "Rep_nat_int (res ts c) \<noteq> {n, n + 1}" 
      by (metis assm disj n_def inf_absorb1 inf_commute less_eq_nat_int.rep_eq 
          sup.cobounded2)
    then have suc_n_not_in_res:"n+1 \<^bold>\<notin> res ts c" 
      using n_def n_in_res nat_int.el.rep_eq nat_int.not_in.rep_eq
        by auto
    from n_in_res have n_not_in_clm:"n \<^bold>\<notin> clm ts c" by blast
    have max:"nat_int.maximum (res ts c) = n"  
      using n_in_res suc_n_not_in_res nat_int.el.rep_eq nat_int.not_in.rep_eq n_def 
        nat_int.maximum_in nat_int.non_empty_elem_in inf_sup_aci(4) 
      by fastforce 
    have min:"nat_int.minimum (clm ts c) = n+1" 
      using suc_n_in_clm n_not_in_clm nat_int.el.rep_eq nat_int.not_in.rep_eq
        n_def nat_int.minimum_in nat_int.non_empty_elem_in  using inf_sup_aci(4)  
        not_in.rep_eq by fastforce
    show ?thesis 
      using assm max min n_in_res nat_int.consec_def nat_int.non_empty_elem_in
      by auto
  next
    assume n_in_clm: "n \<^bold>\<in> clm ts c \<and> n \<^bold>\<notin> res ts c "
    have suc_n_in_res:"n+1 \<^bold>\<in> res ts c" 
    proof (rule ccontr)
      assume "\<not>n+1 \<^bold>\<in> res ts c"
      then have "n \<^bold>\<in> res ts c " 
        by (metis Int_insert_right_if0 One_nat_def Suc_leI add.right_neutral add_Suc_right 
            atMostTwoRes el.rep_eq inf_bot_right inf_sup_absorb insert_not_empty le_antisym 
            n_def one_add_one order.not_eq_order_implies_strict singleton traffic.atLeastOneRes
            traffic.consecutiveRes)
      then show False using n_in_clm 
        using nat_int.el.rep_eq nat_int.not_in.rep_eq by auto
    qed
    have max:"nat_int.maximum (clm ts c) = n"       
      by (metis Rep_nat_int_inverse assm n_in_clm card_non_empty_geq_one 
          le_antisym nat_int.in_singleton nat_int.maximum_in singleton traffic.atMostOneClm)
    have min:"nat_int.minimum (res ts c) = n+1" 
      by (metis Int_insert_right_if0 Int_insert_right_if1 Rep_nat_int_inverse 
          bot_nat_int.rep_eq el.rep_eq in_not_in_iff1 in_singleton inf_nat_int.rep_eq 
          inf_sup_absorb insert_not_empty inter_empty1 minimum_in n_def 
          n_in_clm suc_n_in_res)
    then show ?thesis 
      using assm max min nat_int.consec_def nat_int.non_empty_elem_in 
        suc_n_in_res by auto
  qed
qed
*)

text \<open>We define several possible transitions between traffic snapshots. 
Cars may create or withdraw claims and reservations, as long as the sanity conditions 
of the traffic snapshots are fullfilled. 

In particular, a car can only create
a claim, if it possesses only a reservation on a single lane, and does not 
already possess a claim. Withdrawing a claim can be done in any situation. 
It only has an effect, if the car possesses a claim. Similarly, the 
transition for a car to create a reservation is always possible, but only
changes the spatial situation on the road, if the car already has a claim.
Finally, a car may withdraw its reservation to a single lane, if its
current reservation consists of two lanes.

All of these transitions concern the spatial properties of a single car at a time, i.e., 
for several cars to change their properties, several transitions have to be taken.
\<close>
  
definition create_claim ::
  "traffic\<Rightarrow>cars\<Rightarrow>nat\<Rightarrow>traffic\<Rightarrow>bool" ("_ \<^bold>\<midarrow>c'( _, _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>c(c,n)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)
                                \<and> |clm ts c| = 0
                                \<and> |res ts c| = 1
                                \<and> ((n+1) \<^bold>\<in> res ts c \<or> (n-1 \<^bold>\<in> res ts c))
                                \<and> (clm ts') = (clm ts)(c:=Abs_nat_int {n})"

definition withdraw_claim ::
  "traffic\<Rightarrow>cars \<Rightarrow>traffic\<Rightarrow>bool" ("_ \<^bold>\<midarrow>wdc'( _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)
                                \<and> (clm ts') = (clm ts)(c:=\<emptyset>)"


definition create_reservation ::
  "traffic\<Rightarrow>cars\<Rightarrow>traffic\<Rightarrow>bool" ("_ \<^bold>\<midarrow>r'( _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)(c:=( (res ts c)\<squnion> (clm ts c) ))
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (clm ts') = (clm ts)(c:=\<emptyset>)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)"

definition withdraw_reservation ::
  "traffic\<Rightarrow>cars\<Rightarrow>nat\<Rightarrow>traffic\<Rightarrow> bool" ("_ \<^bold>\<midarrow>wdr'( _, _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>wdr(c,n)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)(c:= Abs_nat_int{n} )
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (clm ts') = (clm ts)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)
                                \<and> n \<^bold>\<in> (res ts c)
                                \<and> |res ts c| = 2"

text \<open>
The following two transitions concern the dynamical behaviour of the cars. 
Similar to the spatial properties, a car may change its dynamics, by setting
it to a new function \(f\) from real to real. Observe that this function is indeed 
arbitrary and does not constrain the possible behaviour in any way. However,
this transition allows a car to change the function determining their braking
distance (in fact, all cars are allowed to change this function, if a car changes
sets a new dynamical function). That is, our model describes an over-approximation
of a concrete situation, where the braking distance is determined by the dynamics. 

The final transition describes the passing of \(x\) time units. That is, all cars 
update their position according to their current dynamical behaviour. Observe that
this transition requires that the dynamics of each car is at least \(0\), for each time
point between \(0\) and \(x\). Hence, this condition denotes that all cars drive
into the same direction. If the current dynamics of a car violated this constraint,
it would have to reset its dynamics, until time may pass again.
\<close>

definition change_dyn::
  "traffic\<Rightarrow>cars\<Rightarrow>(real\<Rightarrow>real)\<Rightarrow>traffic\<Rightarrow> bool" (" _ \<^bold>\<midarrow> dyn'(_,_') \<^bold>\<rightarrow> _" 27)
where "(ts \<^bold>\<midarrow>dyn(c, f)\<^bold>\<rightarrow> ts') == (pos ts' = pos ts) 
                              \<and> (res ts' = res ts)
                              \<and> (clm ts' = clm ts)
                              \<and> (dyn ts' = (dyn ts)(c:= f))
                              \<and> (physical_size ts') = (physical_size ts)"


definition drive::
  "traffic\<Rightarrow>real\<Rightarrow>traffic\<Rightarrow>bool" (" _ \<^bold>\<midarrow> _ \<^bold>\<rightarrow> _" 27)
where "(ts \<^bold>\<midarrow> x \<^bold>\<rightarrow> ts') == (\<forall>c. (pos ts' c = (pos ts c) + (dyn ts c x))) 
                              \<and> (\<forall> c y. 0 \<le> y \<and> y \<le> x \<longrightarrow> dyn ts c y \<ge> 0)  
                              \<and> (res ts' = res ts)
                              \<and> (clm ts' = clm ts)
                              \<and> (dyn ts' = dyn ts)
                              \<and> (physical_size ts') = (physical_size ts)
                              \<and> (braking_distance ts') = (braking_distance ts)
                             "

text\<open>
We bundle the dynamical transitions into \emph{evolutions}, since
we will only reason about combinations of the dynamical behaviour. 
This fits to the level of abstraction by hiding the dynamics completely
inside of the model.
\<close>

inductive evolve::"traffic \<Rightarrow> traffic \<Rightarrow> bool" ("_ \<^bold>\<leadsto> _")
where refl : "ts \<^bold>\<leadsto> ts" |
 change: "\<exists>c. \<exists>f. (ts \<^bold>\<midarrow>dyn(c,f)\<^bold>\<rightarrow>ts') \<Longrightarrow> ts' \<^bold>\<leadsto> ts'' \<Longrightarrow> ts \<^bold>\<leadsto> ts''" |
 drive:  "\<exists>x. x \<ge> 0 \<and>  ( ts \<^bold>\<midarrow>x\<^bold>\<rightarrow> ts') \<Longrightarrow> ts' \<^bold>\<leadsto> ts''    \<Longrightarrow> ts \<^bold>\<leadsto> ts''" 

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

text \<open>
For general transition sequences, we introduce \emph{abstract transitions}. 
A traffic snapshot \(ts^\prime\) is reachable from \(ts\) via an abstract transition,
if there is an arbitrary sequence of transitions from \(ts\) to \(ts^\prime\).
\<close>
 
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


text \<open>
Most properties of the transitions are straightforward. However, to show
that the transition to create a reservation is always possible,
we need to explicitly construct the resulting traffic snapshot. Due
to the size of such a snapshot, the proof is lengthy.
\<close>
  
    
lemma create_res_subseteq1:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<longrightarrow> res ts c \<sqsubseteq> res ts' c "
proof
  assume assm:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"
  hence "res ts' c = res ts c \<squnion> clm ts c" using create_reservation_def
    using fun_upd_apply by auto
  thus "res ts c \<sqsubseteq> res ts' c" by simp
qed

lemma create_res_subseteq2:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<longrightarrow> clm ts c \<sqsubseteq> res ts' c "
proof
  assume assm:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"
  hence "res ts' c = res ts c \<squnion> clm ts c" using create_reservation_def
    using fun_upd_apply by auto
  thus "clm ts c \<sqsubseteq> res ts' c" 
    by simp
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

lemma create_res_continuous: "(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<longrightarrow> continuous (res ts' c)" 
proof
  assume "ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts'"
  show "continuous (res ts' c)"
  proof (cases "clm ts c = \<emptyset>")
    case True
    then have "res ts c = res ts' c" 
      using \<open>ts \<^bold>\<midarrow>r( c ) \<^bold>\<rightarrow> ts'\<close> traffic.create_reservation_def by auto
    then have "\<forall>c. continuous (res ts' c)" using sane_def Rep_traffic Abs_traffic_inverse 
      by (simp add: traffic.res.rep_eq)
    then show ?thesis using sane_def 
      by blast
  next
      case False
      then have "res ts' c = (res ts c \<squnion> clm ts c)"
        using \<open>ts \<^bold>\<midarrow>r( c ) \<^bold>\<rightarrow> ts'\<close> traffic.create_reservation_def by auto
    then have "\<forall>c. continuous (res ts' c)" using sane_def Rep_traffic Abs_traffic_inverse 
      by (simp add: traffic.res.rep_eq)
    then show ?thesis using sane_def 
      by blast
  qed
qed 

declare [[show_types]]

lemma always_create_res:"\<exists>ts'. (ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"  
proof -
  fix ts
  show " \<exists>ts'. (ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"
  proof (cases "clm ts c = \<emptyset>")
    case True
    obtain ts' where ts'_def:"ts' = ts" by simp
    then have "ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts'" 
      using create_reservation_def True fun_upd_triv 
      by auto
    thus ?thesis ..
  next
    case False
    obtain ts1 :: snapshot where ts1_def:"ts1 = Rep_traffic ts" by blast
    then have 1:"sane ts1" 
      using Rep_traffic by blast
    obtain ts' where ts'_def : "ts' = \<lparr> snapshot.pos = snapshot.pos ts1, 
                        snapshot.res = (snapshot.res ts1)(c:=((snapshot.res ts1 c)\<squnion>(snapshot.clm ts1 c) )),
                        snapshot.clm = (snapshot.clm ts1)(c:=\<emptyset>),
                                snapshot.dyn = (snapshot.dyn ts1), 
                                snapshot.physical_size =(snapshot.physical_size ts1), 
                                snapshot.braking_distance =(snapshot.braking_distance ts1)
                         \<rparr>" by blast
    have "snapshot.clm ts' c = \<emptyset>" using ts'_def  by simp
    have disj:"\<forall>c. snapshot.res ts' c \<sqinter> snapshot.clm ts' c = \<emptyset>" using 1 
      by (simp add: inter_empty1 sane_def ts'_def)
    have ps_ge_zero: "(\<forall>c . snapshot.physical_size ts' c > 0)" 
      using ts'_def sane_def 1 by simp
    have sd_ge_zero: "(\<forall>c . snapshot.braking_distance ts' c > 0)" 
      using ts'_def sane_def 1 by simp
    have re_geq_one:"\<forall>d. |snapshot.res ts' d| \<ge> 1" 
    proof 
      fix d
      show " |snapshot.res ts' d| \<ge> 1"
      proof (cases "c = d")
        case True
        then have "snapshot.res ts' d = res ts d \<squnion> clm ts c" 
          by (simp add: ts1_def traffic.clm.rep_eq traffic.res.rep_eq ts'_def) 
        then have "res ts d \<sqsubseteq> snapshot.res ts' d" by simp
        then show ?thesis using sane_def 
          by (metis bot.extremum_unique card_non_empty_geq_one traffic.res_non_empty)
      next
        case False
        then show ?thesis 
          using "1" sane_def ts'_def by auto
      qed
    qed
    have re_leq_two:"\<forall>c. |(snapshot.res ts') c| \<le> 2" using ts'_def sane_def 1 clmNextRes ts1_def 
      using card_un_add by auto
    have cl_leq_one:"\<forall>c. |(snapshot.clm ts') c| \<le> 1" 
      using sane_def 1 nat_int.card_empty_zero ts'_def by auto
    have add_leq_two:"\<forall>c . |snapshot.res ts' c| + |snapshot.clm ts' c| \<le> 2" 
      by (metis "1" add.right_neutral card_empty_zero fun_upd_apply re_leq_two sane_def select_convs(2) simps(3) ts'_def) 
   
    have clNextRe :
      "\<forall>c. (snapshot.clm ts' c) \<noteq> \<emptyset> \<longrightarrow> 
        (\<exists> n.  n \<^bold>\<in> (snapshot.res ts' c) \<squnion> (snapshot.clm ts' c) \<and> (n+1) \<^bold>\<in> (snapshot.res ts' c) \<squnion> (snapshot.clm ts' c))"
      using sane_def 1 ts'_def 
      using traffic.clm.rep_eq traffic.clmNextRes traffic.res.rep_eq ts1_def by auto
    have cont1: "\<forall>c. continuous (snapshot.res ts' c)" 
    proof 
      fix d
      show "continuous (snapshot.res ts' d)"
      proof (cases "c = d")
        case False
        then show ?thesis using sane_def ts'_def 
          using "1" by auto
      next
        case True
        then have "continuous (res ts c \<squnion> clm ts c)" 
          by (metis "1"    nchop_cont nchop_def sane_def sup_bot.left_neutral sup_commute traffic.clm.rep_eq traffic.clm_consec_res  traffic.res.rep_eq  ts1_def) 
        then show ?thesis using sane_def ts'_def 
          by (simp add: True traffic.clm.rep_eq traffic.res.rep_eq ts1_def)
      qed
    qed
    have cont2: "\<forall>c. continuous (snapshot.clm ts' c)" 
      using "1" empty_continuous sane_def ts'_def by auto
    then have "sane ts'" using 1 
      using add_leq_two cl_leq_one disj re_geq_one re_leq_two sane_def ts'_def cont1 cont2 
      by (simp add: re_leq_two)
    then have "ts' \<in> {ts. sane ts}" by blast
    then have "ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> Abs_traffic ts'" 
    proof -
      obtain tt :: "snapshot \<Rightarrow> traffic" where
    f1: "\<lparr>snapshot.pos = snapshot.pos ts1, res = (snapshot.res ts1) (c := snapshot.res ts1 c \<squnion> snapshot.clm ts1 c), clm = (snapshot.clm ts1)(c := bot), dyn = snapshot.dyn ts1, physical_size = snapshot.physical_size ts1, braking_distance = snapshot.braking_distance ts1\<rparr> = Rep_traffic (tt \<lparr>snapshot.pos = snapshot.pos ts1, res = (snapshot.res ts1) (c := snapshot.res ts1 c \<squnion> snapshot.clm ts1 c), clm = (snapshot.clm ts1)(c := bot), dyn = snapshot.dyn ts1, physical_size = snapshot.physical_size ts1, braking_distance = snapshot.braking_distance ts1\<rparr>)"
    by (metis (full_types) Rep_traffic_cases \<open>(ts'::snapshot) \<in> {ts::snapshot. sane ts}\<close> ts'_def)
  then have "Abs_traffic ts' = tt \<lparr>snapshot.pos = snapshot.pos ts1, res = (snapshot.res ts1) (c := snapshot.res ts1 c \<squnion> snapshot.clm ts1 c), clm = (snapshot.clm ts1)(c := bot), dyn = snapshot.dyn ts1, physical_size = snapshot.physical_size ts1, braking_distance = snapshot.braking_distance ts1\<rparr>"
    by (metis (no_types) Rep_traffic_inverse ts'_def)
  then show ?thesis
    using f1 by (simp add: ts1_def traffic.braking_distance.rep_eq traffic.clm.rep_eq traffic.create_reservation_def traffic.dyn.rep_eq traffic.physical_size.rep_eq traffic.pos.rep_eq traffic.res.rep_eq)
  qed
    then show ?thesis by blast
  qed
qed

lemma create_clm_eq_res:"(ts \<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow> ts')  \<longrightarrow> res ts c = res ts' c "
  using create_claim_def by auto

lemma withdraw_clm_eq_res:"(ts \<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow> ts') \<longrightarrow> res ts c= res ts' c "
  using withdraw_claim_def by auto

lemma withdraw_res_subseteq:"(ts \<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow> ts') \<longrightarrow> res ts' c \<sqsubseteq> res ts c "
  using withdraw_reservation_def order_refl less_eq_nat_int.rep_eq nat_int.el.rep_eq 
       fun_upd_apply subset_eq  Abs_nat_int_inverse by auto

end
end
