(*  Title:      NatInt.thy
    Author:     Sven Linker, University of Liverpool

Intervals based on natural numbers. Defines a 
bottom element (empty set), infimum (set intersection),
partial order (subset relation), cardinality (set cardinality).

The union of intervals i and j can only be created, if they are consecutive, i.e.,
max i +1 = min j (or vice versa). To express consecutiveness, we employ the 
predicate consec.

Also contains a "chopping" predicate N_Chop(i,j,k): i can be divided into
consecutive intervals j and k.
*)

section \<open>Discrete Intervals based on Natural Numbers\<close>
  
theory NatInt
  imports Main 
begin
typedef nat_int = "{S . (\<exists> (m::nat) n . {m..n }=S) }"  
  by auto
setup_lifting type_definition_nat_int
  
  
class nat_int 
begin
  
lemma un_consec_seq: "(m::nat)\<le> n \<and> n+1 \<le> l \<longrightarrow> {m..n} \<union> {n+1..l} = {m..l}" 
  by auto
    
lemma int_conseq_seq: " {(m::nat)..n} \<inter> {n+1..l} = {}"
  by auto
        
lemma empty_type: "{} \<in> { S . \<exists> (m:: nat) n . {m..n}=S}"
  by auto
    
lemma inter_result: "\<forall>x \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }. 
         \<forall>y \<in> {S . (\<exists> (m::nat) n . {m..n }=S) }. 
           x \<inter> y \<in>{S . (\<exists> (m::nat) n .  {m..n }=S)}" 
  using Int_atLeastAtMost by blast      
    
lemma union_result: "\<forall>x \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }. 
         \<forall>y \<in> {S . (\<exists> (m::nat) n .  {m..n }=S)  }. 
           x \<noteq> {} \<and> y \<noteq> {} \<and> Max x +1 = Min y \<longrightarrow> x \<union> y \<in>{S . (\<exists> (m::nat) n . {m..n }=S)  }"  
proof (rule ballI)+
  fix x y
  assume "x\<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }" and "y\<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }"
  then have x_def:"(\<exists>m n.  {m..n} = x) "  
    and y_def:"(\<exists>m n.  {m..n} = y) " by blast+    
  show   " x \<noteq> {} \<and> y \<noteq> {} \<and>   Max x+1 = Min y \<longrightarrow> x \<union>  y \<in> {S. (\<exists>m n.  {m..n} = S) }"
  proof
    assume pre:"x \<noteq> {} \<and> y \<noteq> {} \<and> Max x + 1 = Min y"
    then have x_int:"\<exists>m n. m \<le> n \<and> {m..n} = x" and y_int:"(\<exists>m n. m \<le> n \<and> {m..n} = y)"
      using  x_def y_def by force+      
    {
      fix ya yb xa xb
      assume y_prop:"ya \<le> yb \<and> {ya..yb} = y"
      assume x_prop:"xa \<le> xb \<and> {xa..xb} = x"          
      from  x_prop have upper_x:"Max x = xb" 
        by (metis Sup_nat_def cSup_atLeastAtMost)
      from y_prop have lower_y:"Min y = ya" 
        by (metis Inf_fin.coboundedI Inf_fin_Min Min_in add.right_neutral finite_atLeastAtMost le_add1 ord_class.atLeastAtMost_iff order_class.antisym pre)
      from upper_x and lower_y and pre have upper_eq_lower: "xb+1 = ya" 
        by blast
      hence "y= {xb+1 .. yb}" using y_prop by blast
      hence "x \<union> y = {xa..yb}" 
        using un_consec_seq upper_eq_lower x_prop y_prop by blast
      then have " x \<union> y \<in> {S.(\<exists>m n.  {m..n} = S) }"
        by auto
    }      
    then show "x \<union> y \<in> {S.(\<exists>m n.  {m..n} = S)}" 
      using x_int y_int by blast
  qed
qed
  
  
lemma union_empty_result1: "\<forall>i \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }.
                                  i \<union> {} \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }" 
  by blast 
    
lemma union_empty_result2: "\<forall>i \<in> {S . (\<exists> (m::nat) n . {m..n }=S)  }.
                                  {} \<union> i \<in> {S . (\<exists> (m::nat) n . {m..n }=S)  }" 
  by blast 
    
lemma finite:" \<forall>i \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) } . (finite i)"
  by blast
    
lemma not_empty_means_seq:"\<forall>i \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) } . i \<noteq> {} \<longrightarrow> 
 ( \<exists>m n . m \<le> n \<and> {m..n} = i)" 
  using atLeastatMost_empty_iff 
  by force
    
end
  
  
instantiation nat_int :: bot
begin
lift_definition bot_nat_int :: "nat_int" is Set.empty by force
instance by standard
end
instantiation nat_int ::  inf
begin
lift_definition inf_nat_int  ::"nat_int \<Rightarrow> nat_int \<Rightarrow> nat_int" is Set.inter  by force
instance
proof qed
end
  
instantiation nat_int :: "order_bot"
begin
lift_definition less_eq_nat_int :: "nat_int \<Rightarrow> nat_int \<Rightarrow> bool" is Set.subset_eq .
lift_definition less_nat_int :: "nat_int \<Rightarrow> nat_int \<Rightarrow> bool" is Set.subset .
instance
proof
  fix i j k ::nat_int
  show "(i < j) = (i \<le> j \<and> \<not> j \<le> i)" 
    by (simp add: less_eq_nat_int.rep_eq less_le_not_le less_nat_int.rep_eq)
  show "i \<le> i" by (simp add:less_eq_nat_int.rep_eq) 
  show " i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> i \<le> k" by (simp add:less_eq_nat_int.rep_eq)
  show "i \<le> j \<Longrightarrow> j \<le> i \<Longrightarrow> i = j"  
    by (simp add: Rep_nat_int_inject less_eq_nat_int.rep_eq )
  show "bot \<le> i" using  less_eq_nat_int.rep_eq 
    using bot_nat_int.rep_eq by blast
qed
end  
instantiation nat_int ::  "semilattice_inf"
begin
instance 
proof
  fix i j k :: nat_int
  show "i \<le> j \<Longrightarrow> i \<le> k \<Longrightarrow> i \<le> inf j k" 
    by (simp add: inf_nat_int.rep_eq less_eq_nat_int.rep_eq)
  show " inf i   j \<le> i" 
    by (simp add: inf_nat_int.rep_eq less_eq_nat_int.rep_eq) 
  show "inf i  j \<le> j" 
    by (simp add: inf_nat_int.rep_eq less_eq_nat_int.rep_eq) 
qed      
end
  
instantiation nat_int:: "equal"
begin
definition equal_nat_int :: "nat_int \<Rightarrow> nat_int \<Rightarrow> bool"  
  where "equal_nat_int i  j \<equiv> i \<le> j \<and> j \<le> i"
instance 
proof
  fix i j :: nat_int
  show " equal_class.equal i j = (i = j)" using equal_nat_int_def  by auto
qed
end
  
  
context nat_int 
begin
abbreviation subseteq :: "nat_int \<Rightarrow> nat_int\<Rightarrow> bool" (infix "\<sqsubseteq>" 30)
  where  "i \<sqsubseteq> j == i \<le> j "
abbreviation empty :: "nat_int" ("\<emptyset>")
  where "\<emptyset> \<equiv> bot"
    
notation inf (infix "\<sqinter>" 70)

definition union :: "nat_int \<Rightarrow> nat_int \<Rightarrow> nat_int" (infix "\<squnion>" 65)
  where "i \<squnion> j = Abs_nat_int (Rep_nat_int i \<union> Rep_nat_int j)"
    
definition maximum :: "nat_int \<Rightarrow> nat"
  where maximum_def: "i \<noteq> \<emptyset> \<Longrightarrow> maximum (i) =   Max (Rep_nat_int i)" 
    
definition minimum :: "nat_int \<Rightarrow> nat"
  where minimum_def: "i \<noteq> \<emptyset> \<Longrightarrow> minimum(i) = Min (Rep_nat_int i)"
    
definition consec:: "nat_int\<Rightarrow>nat_int \<Rightarrow> bool" 
  where "consec i j \<equiv> (i\<noteq>\<emptyset> \<and> j \<noteq> \<emptyset> \<and> (maximum(i)+1 = minimum j))"
    
definition N_Chop :: "nat_int \<Rightarrow> nat_int \<Rightarrow> nat_int \<Rightarrow> bool" ("N'_Chop'(_,_,_')" 51)
  where nchop_def :
    "N_Chop(i,j,k) \<equiv> (i =  j \<squnion> k  \<and> j \<sqinter> k = \<emptyset> \<and> (j = \<emptyset> \<or>  k = \<emptyset> \<or> consec j k))"
    

    

lift_definition el::"nat \<Rightarrow> nat_int \<Rightarrow> bool" (infix "\<^bold>\<in>" 50) is "Set.member" .
(*notation el (infix " \<^bold>\<in> " 40) *)
  
lift_definition not_in ::"nat \<Rightarrow> nat_int \<Rightarrow> bool" (infix "\<^bold>\<notin>" 40)  is Set.not_member .

  
lift_definition card' ::"nat_int \<Rightarrow> nat"  ( "|_|" 70) is card .

end
  
lemmas[simp] = nat_int.el.rep_eq nat_int.not_in.rep_eq nat_int.card'.rep_eq

context nat_int 
begin
  
lemma in_not_in_iff1 :"n \<^bold>\<in> i \<longleftrightarrow> \<not> n\<^bold>\<notin> i" by simp
lemma in_not_in_iff2: "n\<^bold>\<notin> i \<longleftrightarrow> \<not> n \<^bold>\<in> i" by simp
    
    
lemma rep_non_empty_means_seq:"i \<noteq>\<emptyset> \<longrightarrow> (\<exists>m n. m \<le> n \<and> ({m..n} =( Rep_nat_int i)))" 
  by (metis Rep_nat_int Rep_nat_int_inject bot_nat_int.rep_eq nat_int.not_empty_means_seq)
  
lemma non_empty_max: "i \<noteq> \<emptyset> \<longrightarrow> (\<exists>m . maximum(i) = m)" 
  by auto
    
lemma non_empty_min: "i \<noteq> \<emptyset> \<longrightarrow> (\<exists>m . minimum(i) = m)" 
  by auto
    
lemma minimum_in: "i \<noteq> \<emptyset> \<longrightarrow> minimum i \<^bold>\<in> i"
  by (metis Min_in atLeastatMost_empty_iff2 finite_atLeastAtMost minimum_def el.rep_eq rep_non_empty_means_seq)
    
lemma maximum_in: "i \<noteq> \<emptyset> \<longrightarrow> maximum i \<^bold>\<in> i"
  by (metis Max_in atLeastatMost_empty_iff2 finite_atLeastAtMost maximum_def el.rep_eq rep_non_empty_means_seq)
    
lemma non_empty_elem_in:"i \<noteq> \<emptyset> \<longleftrightarrow> (\<exists>n. n \<^bold>\<in> i)"   
proof
  assume assm:"i \<noteq> \<emptyset>"
  show "\<exists>n . n \<^bold>\<in> i" 
    by (metis assm Rep_nat_int_inverse all_not_in_conv el.rep_eq bot_nat_int_def)
next
  assume assm:"\<exists>n. n \<^bold>\<in> i"
  show "i \<noteq> \<emptyset>" 
    using Abs_nat_int_inverse assm el.rep_eq bot_nat_int_def by fastforce
qed
  
lemma leq_nat_non_empty:"(m::nat) \<le> n \<longrightarrow> Abs_nat_int{m..n} \<noteq> \<emptyset>"  
proof
  assume assm:"m \<le>n"
  then have non_empty:"{m..n} \<noteq> {} " 
    using atLeastatMost_empty_iff by blast
  with assm have "{m..n} \<in> {S . (\<exists> (m::nat) n .  {m..n }=S)  }" by blast
  then show "Abs_nat_int {m..n} \<noteq> \<emptyset>" 
    using Abs_nat_int_inject empty_type non_empty bot_nat_int_def 
    by (simp add: bot_nat_int.abs_eq)
qed
  
lemma leq_max_sup:"(m::nat) \<le> n \<longrightarrow> Max {m..n} = n" 
  by (metis Sup_nat_def cSup_atLeastAtMost)
    
lemma leq_min_inf: "(m::nat) \<le> n \<longrightarrow> Min {m..n} = m"
  by (meson Min_in Min_le antisym atLeastAtMost_iff atLeastatMost_empty_iff eq_imp_le finite_atLeastAtMost)
    
lemma leq_max_sup':"(m::nat) \<le> n \<longrightarrow> maximum(Abs_nat_int{m..n}) = n" 
proof 
  assume assm:"m \<le> n"
  hence in_type:"{m..n} \<in> {S . (\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={} }" by blast
  from assm have "Abs_nat_int{m..n} \<noteq> \<emptyset>" using leq_nat_non_empty by blast
  hence max:"maximum(Abs_nat_int{m..n}) = Max (Rep_nat_int (Abs_nat_int {m..n}))" using  maximum_def 
    by blast
  from in_type have " (Rep_nat_int (Abs_nat_int {m..n})) = {m..n}" using Abs_nat_int_inverse
    by blast
  hence  "Max (Rep_nat_int (Abs_nat_int{m..n})) = Max {m..n}" by simp
  with max have simp_max:"maximum(Abs_nat_int{m..n}) = Max {m..n}" by simp
  from assm have "Max {m..n} = n" using leq_max_sup by blast
  with simp_max show "maximum(Abs_nat_int{m..n}) = n" by simp
qed
  
lemma leq_min_inf':"(m::nat) \<le> n \<longrightarrow> minimum(Abs_nat_int{m..n}) = m" 
proof 
  assume assm:"m \<le> n"
  hence in_type:"{m..n} \<in> {S . (\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={} }" by blast
  from assm have "Abs_nat_int{m..n} \<noteq> \<emptyset>" using leq_nat_non_empty by blast
  hence min:"minimum(Abs_nat_int{m..n}) = Min (Rep_nat_int (Abs_nat_int {m..n}))" 
    using  minimum_def by blast
  from in_type have " (Rep_nat_int (Abs_nat_int {m..n})) = {m..n}" using Abs_nat_int_inverse
    by blast
  hence  "Min (Rep_nat_int (Abs_nat_int{m..n})) = Min {m..n}" by simp
  with min have simp_min:"minimum(Abs_nat_int{m..n}) = Min {m..n}" by simp
  from assm have "Min {m..n} = m" using leq_min_inf by blast
  with simp_min show "minimum(Abs_nat_int{m..n}) = m" by simp
qed
  
lemma in_refl:"(n::nat)  \<^bold>\<in> Abs_nat_int {n}"
proof -
  have "(n::nat) \<le> n" by simp
  hence "{n} \<in> {S . (\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={} }" by auto
  then show "n \<^bold>\<in> Abs_nat_int {n}" 
    by (simp add: Abs_nat_int_inverse el_def)
qed
  
lemma in_singleton:" m \<^bold>\<in> Abs_nat_int{n} \<longrightarrow> m = n"
proof
  assume assm:" m \<^bold>\<in> Abs_nat_int{n}"
  have "(n::nat) \<le> n" by simp
  hence "{n} \<in> {S . (\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={} }" by auto
  with assm show "m=n" by (simp add: Abs_nat_int_inverse el_def)
qed
  
lemma inter_empty1:"(i::nat_int) \<sqinter> \<emptyset> = \<emptyset>" 
  using Rep_nat_int_inject inf_nat_int.rep_eq bot_nat_int.abs_eq bot_nat_int.rep_eq by fastforce 
    
lemma inter_empty2:"\<emptyset> \<sqinter> (i::nat_int) = \<emptyset>" 
  by (metis inf_commute nat_int.inter_empty1)
        
lemma un_empty_absorb1:"i \<squnion> \<emptyset> = i" 
  using  Abs_nat_int_inverse Rep_nat_int_inverse union_def empty_type bot_nat_int.rep_eq by auto
    
lemma un_empty_absorb2:"\<emptyset> \<squnion> i = i" 
  using  Abs_nat_int_inverse Rep_nat_int_inverse union_def empty_type bot_nat_int.rep_eq by auto
          
lemma consec_un:"consec i j \<and> n \<notin> Rep_nat_int(i) \<union> Rep_nat_int j \<longrightarrow> n \<^bold>\<notin>  (i \<squnion> j)"
proof
  assume assm:"consec i j \<and> n \<notin>  Rep_nat_int i \<union> Rep_nat_int j" 
  thus "n \<^bold>\<notin> (i \<squnion> j)" 
  proof -
    have f1: "Abs_nat_int (Rep_nat_int (i \<squnion> j)) = Abs_nat_int (Rep_nat_int i \<union> Rep_nat_int j)"
      using Rep_nat_int_inverse union_def by presburger
    have "i \<noteq> \<emptyset> \<and> j \<noteq> \<emptyset> \<and> maximum i + 1 = minimum j"
      using assm consec_def by auto
    then have "\<exists>n na. {n..na} = Rep_nat_int i \<union> Rep_nat_int j" 
      by (metis (no_types) leq_max_sup leq_min_inf maximum_def minimum_def rep_non_empty_means_seq un_consec_seq)
    then show ?thesis
      using f1 Abs_nat_int_inject Rep_nat_int not_in.rep_eq assm by auto
  qed
qed
  
lemma un_assoc: "consec i j \<and> consec j k \<longrightarrow> (i \<squnion> j) \<squnion> k = i \<squnion> (j \<squnion> k)" 
  by (smt Abs_nat_int_inverse dual_order.trans le_add1 leq_max_sup leq_min_inf maximum_def mem_Collect_eq minimum_def consec_def rep_non_empty_means_seq union_def un_consec_seq) 
    
    
    
lemma un_subset1: "consec i j \<longrightarrow> i \<sqsubseteq> i \<squnion> j"
proof
  assume "consec i j"
  then have assm:"i \<noteq> \<emptyset> \<and> j \<noteq> \<emptyset> \<and> maximum i+1 = minimum j" 
    using consec_def by blast
  have "Rep_nat_int i \<union> Rep_nat_int j =  {minimum i.. maximum j}" 
    by (metis assm nat_int.leq_max_sup nat_int.leq_min_inf nat_int.maximum_def nat_int.minimum_def nat_int.rep_non_empty_means_seq nat_int.un_consec_seq )    
  then show "i \<sqsubseteq> i \<squnion> j" using Abs_nat_int_inverse Rep_nat_int 
    by (metis (mono_tags, lifting) Un_upper1 less_eq_nat_int.rep_eq mem_Collect_eq nat_int.union_def)
qed
  
lemma un_subset2: "consec i j \<longrightarrow> j \<sqsubseteq> i \<squnion> j"
proof
  assume "consec i j"
  then have assm:"i \<noteq> \<emptyset> \<and> j \<noteq> \<emptyset> \<and> maximum i+1 = minimum j" 
    using consec_def by blast
  have "Rep_nat_int i \<union> Rep_nat_int j =  {minimum i.. maximum j}" 
    by (metis assm nat_int.leq_max_sup nat_int.leq_min_inf nat_int.maximum_def nat_int.minimum_def nat_int.rep_non_empty_means_seq nat_int.un_consec_seq )          
  then show "j \<sqsubseteq> i \<squnion> j" using Abs_nat_int_inverse Rep_nat_int
    by (metis (mono_tags, lifting) Un_upper2 less_eq_nat_int.rep_eq mem_Collect_eq nat_int.union_def)
qed
  
  
lemma inter_distr1:"consec j k \<longrightarrow> i \<sqinter> (j \<squnion> k) = (i \<sqinter> j) \<squnion> (i \<sqinter> k)"  
  unfolding consec_def
proof  
  assume assm:"j \<noteq> \<emptyset> \<and> k \<noteq> \<emptyset> \<and> maximum j +1 = minimum k"
  then show " i \<sqinter> (j \<squnion> k) = (i \<sqinter> j) \<squnion> (i \<sqinter> k)" using Abs_nat_int_inverse 
    by (smt bot_nat_int.rep_eq Rep_nat_int Rep_nat_int_inject atLeastatMost_empty_iff inf_nat_int.rep_eq inf_sup_distrib1 mem_Collect_eq nat_int.leq_max_sup' nat_int.leq_min_inf nat_int.minimum_def nat_int.union_def un_consec_seq)
qed
  
lemma inter_distr2:"consec j k \<longrightarrow> (j \<squnion> k) \<sqinter> i = (j \<sqinter> i) \<squnion> (k \<sqinter> i)"
  by (simp add: inter_distr1 inf_commute)
    
lemma consec_un_not_elem1:"consec i j \<and> n\<^bold>\<notin> i \<squnion> j \<longrightarrow>  n \<^bold>\<notin> i"
  using un_subset1 less_eq_nat_int.rep_eq not_in.rep_eq by blast 
    
lemma consec_un_not_elem2:"consec i j \<and> n\<^bold>\<notin> i \<squnion> j \<longrightarrow>  n \<^bold>\<notin> j"
  using  un_subset2 less_eq_nat_int.rep_eq not_in.rep_eq by blast
    
    
lemma consec_un_element1:"consec i j \<and> n \<^bold>\<in> i \<longrightarrow> n \<^bold>\<in> i \<squnion> j" 
  using less_eq_nat_int.rep_eq nat_int.el.rep_eq nat_int.un_subset1 by blast
    
lemma consec_un_element2:"consec i j \<and> n \<^bold>\<in> j \<longrightarrow> n \<^bold>\<in> i \<squnion> j"
  using less_eq_nat_int.rep_eq nat_int.el.rep_eq nat_int.un_subset2 by blast
    
lemma consec_lesser:" consec i j  \<longrightarrow> (\<forall>n m. (n \<^bold>\<in> i \<and> m \<^bold>\<in> j \<longrightarrow> n < m))" 
proof (rule allI|rule impI)+
  assume "consec i j"
  fix n and m  
  assume assump:"n \<^bold>\<in> i \<and> m \<^bold>\<in> j "
  then have  max:"n \<le> maximum i" 
    by (metis \<open>consec i j\<close> atLeastAtMost_iff leq_max_sup maximum_def consec_def el.rep_eq rep_non_empty_means_seq)
  from assump have min: "m \<ge> minimum j" 
    by (metis Min_le \<open>consec i j\<close> finite_atLeastAtMost minimum_def consec_def el.rep_eq rep_non_empty_means_seq)
  from min and max show less:"n < m" 
    using One_nat_def Suc_le_lessD \<open>consec i j\<close> add.right_neutral add_Suc_right dual_order.trans leD leI consec_def by auto
qed

lemma consec_in_exclusive1:"consec i j \<and> n \<^bold>\<in> i \<longrightarrow> n \<^bold>\<notin> j" 
  using nat_int.consec_lesser nat_int.in_not_in_iff2 by blast

lemma consec_in_exclusive2:"consec i j \<and> n \<^bold>\<in> j \<longrightarrow> n \<^bold>\<notin> i"
  using consec_in_exclusive1 el.rep_eq not_in.rep_eq by blast
  
lemma consec_trans_lesser:" consec i j \<and> consec j k \<longrightarrow> (\<forall>n m. (n \<^bold>\<in> i \<and> m \<^bold>\<in> k \<longrightarrow> n < m))"
proof (rule allI|rule impI)+
  assume cons:" consec i j \<and> consec j k"
  fix n and m
  assume assump:"n \<^bold>\<in> i \<and> m \<^bold>\<in> k "
  have "\<forall>k . k \<^bold>\<in> j \<longrightarrow> k < m" using consec_lesser assump cons by blast
  hence m_greater:"maximum j < m" using cons maximum_in consec_def by blast
  then show "n < m" 
    by (metis assump cons consec_def dual_order.strict_trans nat_int.consec_lesser nat_int.maximum_in)      
qed
  
lemma consec_inter_empty:"consec i j \<Longrightarrow> i \<sqinter> j = \<emptyset>"  
proof -
  assume "consec i j"
  then have "i \<noteq> bot \<and> j \<noteq> bot \<and> maximum i + 1 = minimum j"
    using consec_def by force
  then show ?thesis
    by (metis (no_types) Rep_nat_int_inverse bot_nat_int_def inf_nat_int.rep_eq int_conseq_seq nat_int.leq_max_sup nat_int.leq_min_inf nat_int.maximum_def nat_int.minimum_def nat_int.rep_non_empty_means_seq)
qed 

  
lemma consec_intermediate1:"consec j k \<and> consec i (j \<squnion> k) \<longrightarrow> consec i j "
proof
  assume assm:"consec j k \<and> consec i (j \<squnion> k)"
  hence min_max_yz:"maximum j +1=minimum k" using consec_def by blast 
  hence min_max_xyz:"maximum i +1 = minimum (j \<squnion> k)" using consec_def using assm by blast
  have min_y_yz:"minimum j = minimum (j \<squnion> k)" using consec_lesser assm 
  proof -
    have f1: "j \<noteq> \<emptyset> \<and> k \<noteq> \<emptyset> \<and> maximum j + 1 = minimum k"
      using assm consec_def by auto
    have "\<forall>n. n = \<emptyset> \<or> (\<exists>na nb. na \<le> nb \<and> {na..nb} = Rep_nat_int n)"
      by (meson rep_non_empty_means_seq)
    then obtain nn :: "nat_int \<Rightarrow> nat" and nna :: "nat_int \<Rightarrow> nat" where
      f2: "\<forall>n. n = \<emptyset> \<or> nn n \<le> nna n \<and> {nn n..nna n} = Rep_nat_int n"
      by moura
    then have "nn j \<le> nna j \<and> {nn j..nna j} = Rep_nat_int j"
      using f1 by blast
    then show ?thesis
      using f2 f1 by (metis dual_order.trans le_add1 leq_max_sup leq_min_inf maximum_def minimum_def leq_min_inf' union_def un_consec_seq)
  qed 
  hence min_max_xy:"maximum i+1 = minimum j" using min_max_xyz by simp
  thus consec_x_y:"consec i j" using assm consec_def by auto
qed
  
lemma consec_intermediate2:"consec i j \<and> consec (i \<squnion> j) k \<longrightarrow> consec j k "
proof
  assume assm:"consec i j \<and> consec (i \<squnion> j) k"
  hence min_max_yz:"maximum i +1=minimum j" using consec_def by blast 
  hence min_max_xyz:"maximum (i \<squnion> j) +1 = minimum ( k)" using consec_def using assm by blast
  have min_y_yz:"maximum j = maximum (i \<squnion> j)" 
  proof -
    from assm have cons:"consec i j" by best
    hence "\<forall> n m. (n \<^bold>\<in> i \<and> m \<^bold>\<in> j \<longrightarrow> n < m)" using consec_lesser by best
    hence "\<forall>n. n \<^bold>\<in> i \<longrightarrow> n < maximum j" using maximum_in cons consec_def by blast
    thus "maximum j = maximum (i \<squnion> j)" using union_def 
      by (smt assm consec_def dual_order.trans le_add1 leq_max_sup' nat_int.leq_max_sup nat_int.leq_min_inf nat_int.maximum_def nat_int.minimum_def nat_int.rep_non_empty_means_seq nat_int.un_consec_seq) 
  qed
  hence min_max_xy:"maximum j+1 = minimum k" using min_max_xyz by simp
  thus consec_x_y:"consec j k" using assm consec_def by auto
qed
  
lemma consec_assoc1:"consec j k \<and> consec i (j \<squnion> k) \<longrightarrow> consec (i \<squnion> j) k "
proof
  assume assm:"consec j k \<and> consec i (j \<squnion> k)"
  hence min_max_yz:"maximum j +1=minimum k" using consec_def by blast 
  hence min_max_xyz:"maximum i +1 = minimum (j \<squnion> k)" using consec_def using assm by blast
  have min_y_yz:"minimum j = minimum (j \<squnion> k)" using consec_lesser assm 
  proof -
    from assm have cons:"consec j k" by best
    hence "\<forall> n m. (n \<^bold>\<in> j \<and> m \<^bold>\<in> k \<longrightarrow> n < m)" using consec_lesser by best
    hence "\<forall>m. m \<^bold>\<in> k \<longrightarrow>  minimum j < m" using minimum_in cons consec_def by blast
    thus "minimum j = minimum (j \<squnion> k)" using union_def 
      by (metis assm consec_intermediate1 consec_def)
  qed
  hence min_max_xy:"maximum i+1 = minimum j" using min_max_xyz by simp
  hence consec_x_y:"consec i j" using assm _consec_def by auto
  hence max_y_xy:"maximum j = maximum (i \<squnion> j)" using consec_lesser assm 
    by (smt Un_empty atLeastatMost_empty_iff leq_max_sup leq_min_inf maximum_def minimum_def consec_def leq_max_sup' rep_non_empty_means_seq union_def un_consec_seq)
  have none_empty:"i \<noteq> \<emptyset> \<and> j \<noteq> \<emptyset> \<and> k \<noteq> \<emptyset>" using assm by (simp add: consec_def)
  hence un_non_empty:"i\<squnion>j \<noteq> \<emptyset>" 
    by (metis consec_x_y add_eq_self_zero assm inf.absorb_iff2 inf_commute le_add1 leq_max_sup leq_min_inf maximum_def min_max_yz min_y_yz minimum_def rep_non_empty_means_seq  un_assoc un_empty_absorb2 un_subset2  zero_neq_one)
  have max:"maximum (i\<squnion>j) +1 = minimum k" using min_max_yz max_y_xy by auto  
  thus "consec (i \<squnion> j) k"  using max un_non_empty none_empty consec_def by blast
qed
  
lemma consec_assoc2:"consec i j \<and> consec (i\<squnion> j) k \<longrightarrow> consec i  (j\<squnion> k) "
proof
  assume assm:"consec i j \<and> consec (i\<squnion> j) k"
  hence consec_y_z:"consec j k" using assm  consec_def consec_intermediate2 
    by blast
  hence max_y_xy:"maximum j = maximum (i \<squnion> j)" using consec_lesser assm 
    by (smt Un_empty atLeastatMost_empty_iff leq_max_sup leq_min_inf maximum_def minimum_def consec_def leq_max_sup' rep_non_empty_means_seq union_def un_consec_seq)
  have min_y_yz:"minimum j = minimum (j \<squnion> k)" 
    by (smt Rep_nat_int bot_nat_int.rep_eq Rep_nat_int_inverse Un_empty atLeastatMost_empty_iff consec_y_z leq_max_sup maximum_def mem_Collect_eq consec_def leq_min_inf' union_def un_consec_seq)
  have none_empty:"i \<noteq> \<emptyset> \<and> j \<noteq> \<emptyset> \<and> k \<noteq> \<emptyset>" using assm by (simp add: consec_def)
  then have un_non_empty:"j\<squnion>k \<noteq> \<emptyset>" 
    by (metis  bot_nat_int.rep_eq Rep_nat_int_inject consec_y_z  less_eq_nat_int.rep_eq un_subset1 subset_empty)
  have max:"maximum (i) +1 = minimum (j\<squnion> k)" using assm min_y_yz consec_def by auto
  thus "consec i ( j \<squnion> k)"  using max un_non_empty none_empty consec_def by blast
qed
  
  
lemma consec_assoc_mult:"(i2=\<emptyset>\<or> consec i1 i2 ) \<and> (i3 =\<emptyset> \<or> consec i3 i4) \<and> (consec (i1 \<squnion> i2) (i3 \<squnion> i4)) \<longrightarrow> (i1 \<squnion> i2) \<squnion> (i3 \<squnion> i4) = (i1 \<squnion> (i2 \<squnion> i3)) \<squnion> i4"
proof
  assume assm:"(i2=\<emptyset>\<or> consec i1 i2 ) \<and> (i3 =\<emptyset> \<or> consec i3 i4) \<and> (consec (i1 \<squnion> i2) (i3 \<squnion> i4))"
  hence "(i2=\<emptyset>\<or> consec i1 i2 )" by simp
  thus " (i1 \<squnion> i2) \<squnion> (i3 \<squnion> i4) = (i1 \<squnion> (i2 \<squnion> i3)) \<squnion> i4"
  proof
    assume empty2:"i2 = \<emptyset>"
    hence only_l1:"(i1 \<squnion> i2) = i1" using un_empty_absorb1 by simp
    from assm have "(i3 =\<emptyset> \<or> consec i3 i4)" by simp
    thus " (i1 \<squnion> i2) \<squnion> (i3 \<squnion> i4) = (i1 \<squnion> (i2 \<squnion> i3)) \<squnion> i4"
    proof
      assume empty3:"i3 = \<emptyset>"
      show ?thesis  by (simp add: empty2 empty3 un_empty_absorb2)
    next
      assume consec34:" consec i3 i4"
      from assm and only_l1 have consec13:"consec i1 (i3 \<squnion> i4)" by simp
      hence consec134:"consec (i1\<squnion>i3) i4" by (simp add: consec34 consec_assoc1)
      hence consec11:"consec i1 i3" using consec13 consec34 consec_intermediate1 by blast
      have " (i1 \<squnion> (i2 \<squnion> i3)) = (i1 \<squnion> i3)" by (simp add: empty2 un_empty_absorb2)
      hence "(i1 \<squnion> (i2 \<squnion> i3)) \<squnion> i4 = (i1 \<squnion> i3) \<squnion> i4" by simp
      have "i1 \<squnion> (i3 \<squnion> i4) = (i1 \<squnion> i3) \<squnion> i4" using un_assoc consec13 consec34 consec11 by auto
      thus ?thesis 
        using consec134 consec13 consec34 empty2 un_assoc un_empty_absorb2 only_l1 
        by auto
    qed
  next
    assume consec12:" consec i1 i2"
    from assm have "(i3 =\<emptyset> \<or> consec i3 i4)" by simp
    thus " (i1 \<squnion> i2) \<squnion> (i3 \<squnion> i4) = (i1 \<squnion> (i2 \<squnion> i3)) \<squnion> i4"
    proof
      assume empty3:"i3 = \<emptyset>"
      hence only_l4:"(i3 \<squnion> i4) = i4 " using un_empty_absorb2 by simp
      have "(i1 \<squnion> (i2 \<squnion> i3)) = i1 \<squnion> i2" using empty3 by (simp add: un_empty_absorb1)
      thus  ?thesis by (simp add: only_l4)
    next
      assume  consec34:" consec i3 i4"
      have consec12_3:"consec (i1 \<squnion> i2) i3" using assm consec34 consec_intermediate1 by blast
      show ?thesis by (metis consec12 consec12_3 consec34 consec_intermediate2 un_assoc)
    qed
  qed
qed
  
    
lemma card_subset_le: "i \<sqsubseteq> i' \<longrightarrow> |i| \<le> |i'|"  
proof -
  have "\<exists>n na. {n..na} = Rep_nat_int i'"
    using Rep_nat_int by fastforce
  then obtain nn :: "nat set \<Rightarrow> nat" and nna :: "nat set \<Rightarrow> nat" where
    "{nn (Rep_nat_int i')..nna (Rep_nat_int i')} = Rep_nat_int i'"
    by meson
  then show ?thesis
    by (metis (no_types) card_mono finite_atLeastAtMost card'.rep_eq less_eq_nat_int.rep_eq)
qed
  
lemma card_subset_less:"(i::nat_int) < i' \<longrightarrow> |i|<|i'|"  
proof -
  have "\<exists>n na. {n..na} = Rep_nat_int i'"
    using Rep_nat_int by fastforce
  then obtain nn :: "nat set \<Rightarrow> nat" and nna :: "nat set \<Rightarrow> nat" where
    "{nn (Rep_nat_int i')..nna (Rep_nat_int i')} = Rep_nat_int i'"
    by meson
  then show ?thesis 
    by (metis finite_atLeastAtMost less_nat_int.rep_eq nat_int.card'.rep_eq psubset_card_mono)
qed
  
lemma card_empty_zero:"|\<emptyset>| = 0"  
  using Abs_nat_int_inverse empty_type card'.rep_eq bot_nat_int.rep_eq by auto
    
lemma card_non_empty_geq_one:"i \<noteq> \<emptyset> \<longleftrightarrow> |i| \<ge> 1"
proof
  assume "i \<noteq> \<emptyset>"
  hence "Rep_nat_int i \<noteq> {}" by (metis Rep_nat_int_inverse bot_nat_int.rep_eq)
  hence "card (Rep_nat_int i) > 0" 
    by (metis \<open>i \<noteq> \<emptyset>\<close> card_0_eq finite_atLeastAtMost gr0I rep_non_empty_means_seq)
  thus "|i| \<ge> 1" by (simp add: card'_def) 
next
  assume "|i| \<ge> 1" thus "i \<noteq>\<emptyset>" 
    using card_empty_zero by auto
qed
  
lemma card_un_add: " consec i i' \<longrightarrow> |i \<squnion> i'| = |i| + |i'|"  
proof -
  have f1: "Rep_nat_int i = {} \<or> Rep_nat_int i' = {} \<or> Max (Rep_nat_int i) + 1 \<noteq> Min (Rep_nat_int i') \<or> Rep_nat_int i \<union> Rep_nat_int i' \<in> {N. \<exists>n na. {n..na} = N}"
    using Rep_nat_int nat_int.union_result by force
  { assume "Rep_nat_int i \<union> Rep_nat_int i' \<noteq> Rep_nat_int (i \<squnion> i')"
    then have "i = \<emptyset> \<or> i' = \<emptyset> \<or> maximum i + 1 \<noteq> minimum i'"
      using f1 by (metis (no_types) Abs_nat_int_inverse Rep_nat_int_inject bot_nat_int_def local.empty_type local.union_def nat_int.maximum_def nat_int.minimum_def)
    then have "\<not> consec i i'"
      using local.consec_def by presburger }
  then show ?thesis
    by (metis (no_types) Abs_nat_int_inverse Rep_nat_int add.right_neutral bot_nat_int_def card.empty card_Un_Int consec_inter_empty inf_nat_int.rep_eq local.card'.rep_eq local.empty_type local.finite)
qed

lemma singleton:"|i| = 1 \<longrightarrow> (\<exists>n. Rep_nat_int i = {n})"
  using card_1_singletonE card'.rep_eq by fastforce
    
lemma singleton2:" (\<exists>n. Rep_nat_int i = {n}) \<longrightarrow> |i| = 1"
  using card_1_singletonE card'.rep_eq by fastforce
    
    
lemma card_seq:"\<forall>i .|i| = x \<longrightarrow> (Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n..n+(x-1)}))" 
proof (induct x)
  show IB:"\<forall>i. |i| = 0 \<longrightarrow> (Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n..n+(0-1)}))" 
    by (metis  card_non_empty_geq_one bot_nat_int.rep_eq  not_one_le_zero)
  fix x
  assume IH:"\<forall>i. |i| = x \<longrightarrow> Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n.. n + (x - 1)})"
  show   " \<forall>i. |i| = Suc x \<longrightarrow>
             Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n.. n + (Suc x - 1)})"
  proof (rule allI|rule impI)+
    fix i
    assume assm_IS:"|i| = Suc x"
    show " Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n.. n + (Suc x - 1)})"
    proof (cases "x = 0")
      assume "x=0"
      hence "|i| = 1" 
        using assm_IS by auto 
      then have "\<exists>n'. Rep_nat_int i = {n'}" 
        using nat_int.singleton by blast 
      hence "\<exists>n'. Rep_nat_int i = {n'.. n' + (Suc x) -1}"
        by (simp add: \<open>x = 0\<close>)
      thus "Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n.. n + (Suc x - 1)})"            
        by simp
    next
      assume x_neq_0:"x \<noteq>0 "
      hence x_ge_0:"x > 0" using gr0I by blast
      from assm_IS have i_is_seq:"\<exists>n m. n \<le> m \<and> Rep_nat_int i = {n..m}" 
        by (metis One_nat_def Suc_le_mono card_non_empty_geq_one le0 rep_non_empty_means_seq)
      obtain n and m where seq_def:" n  \<le> m \<and> Rep_nat_int i = {n..m}" 
        using i_is_seq by auto
      have n_le_m:"n < m"
      proof (rule ccontr)
        assume "\<not>n < m"
        hence "n = m" by (simp add: less_le seq_def)
        hence "Rep_nat_int i = {n}" by (simp add: seq_def)
        hence "x = 0" using assm_IS card'.rep_eq by auto
        thus False by (simp add: x_neq_0)
      qed
      hence "n \<le> (m-1)" by simp
      obtain i' where  "i' = Abs_nat_int {n..m-1}" by blast
      have card_i':"|i'| = x" 
        by (metis One_nat_def Suc_leI \<open>i' = Abs_nat_int {n..m - 1}\<close> \<open>n \<le> m - 1\<close> add_gr_0 assm_IS card_atLeastAtMost diff_Suc_1 diff_Suc_diff_eq2 diff_diff_left leq_max_sup leq_min_inf less_imp_add_positive maximum_def minimum_def n_le_m card'.rep_eq leq_max_sup' leq_min_inf' leq_nat_non_empty rep_non_empty_means_seq seq_def)
      hence "Rep_nat_int i' = {} \<or> (\<exists>n. Rep_nat_int i' = {n.. n + (x - 1)})" 
        using IH by auto
      hence " (\<exists>n. Rep_nat_int i' = {n.. n + (x - 1)})" using x_neq_0 
        using card.empty card_i' card'.rep_eq by auto
      hence "m-1 = n + x -1" using assm_IS card'.rep_eq seq_def by auto
      hence "m = n +x" using n_le_m x_ge_0 by linarith
      hence "( Rep_nat_int i = {n.. n + (Suc x -1) })" using seq_def by (simp )
      hence "\<exists>n. (Rep_nat_int i = {n.. n + (Suc x -1) })" ..
      thus  "Rep_nat_int i = {} \<or> (\<exists>n. (Rep_nat_int i = {n.. n + (Suc x -1) }))" by blast
    qed
  qed
qed
  
  
    
lemma rep_single: "Rep_nat_int (Abs_nat_int {m..m}) = {m}"
  by (simp add: Abs_nat_int_inverse)
    
lemma chop_empty_right: "\<forall>i. N_Chop(i,i,\<emptyset>)"  
  using bot_nat_int.abs_eq nat_int.inter_empty1 nat_int.nchop_def nat_int.un_empty_absorb1 by auto
    
lemma chop_empty_left: "\<forall>i. N_Chop(i, \<emptyset>, i)"
  using bot_nat_int.abs_eq nat_int.inter_empty2 nat_int.nchop_def nat_int.un_empty_absorb2 by auto
    
lemma chop_empty : "N_Chop(\<emptyset>,\<emptyset>,\<emptyset>)"
  by (simp add: chop_empty_left)
    
lemma chop_always_possible:"\<forall>i.\<exists> j k. N_Chop(i,j,k)" 
  by (metis  chop_empty_right)
    
lemma chop_add1: "N_Chop(i,j,k) \<longrightarrow> |i| = |j| + |k|"
  using card_empty_zero card_un_add un_empty_absorb1 un_empty_absorb2 nchop_def by auto
    
lemma chop_add2:"|i| = x+y \<longrightarrow> (\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y)"
proof
  assume assm:"|i| = x+y"
  show "(\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y)"
  proof (cases "x+y = 0")
    assume "x+y =0"
    hence i_empty:"i = \<emptyset>" 
      using Rep_nat_int Rep_nat_int_inject assm card_empty_zero card'_def finite card_non_empty_geq_one by force
    obtain j and k where j_k_def:"j = \<emptyset> \<and> k = \<emptyset>" by simp
    from j_k_def have "|j|=0 \<and> |k| = 0" using card_empty_zero by blast
    have chop:"N_Chop(i,j,k)" by (simp add: j_k_def i_empty chop_empty)
    hence "N_Chop(i,j,k) \<and> |j|=x \<and> |k| = y" 
      using \<open>x + y = 0\<close> \<open>|j| = 0 \<and> |k| = 0\<close> add_is_0 by auto
    thus "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" by blast
  next 
    assume "x+y \<noteq> 0"
    show "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" 
    proof (cases "x = 0")
      assume x_eq_0:"x=0"
      obtain j and k where j_empty:"j = \<emptyset> \<and> k = i" by simp
      hence "N_Chop(i,j,k) \<and> |j| = x \<and> |k| = y" 
        using assm card_empty_zero chop_empty_left  x_eq_0 by auto
      thus "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" by blast
    next
      assume x_neq_0:"x \<noteq>0"
      show "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" 
      proof (cases "y = 0")
        assume y_eq_0:"y=0"
        obtain j and k where k_empty:"j = i \<and> k = \<emptyset>" by simp
        hence "N_Chop(i,j,k) \<and> |j| = x \<and> |k| = y" 
          using assm card_empty_zero chop_empty_right y_eq_0 by auto 
        thus "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" by blast
      next
        assume y_neq_0:"y \<noteq> 0"
        have rep_i:"\<exists>n. Rep_nat_int i = {n..n + (x+y)-1}" 
          using assm card'.rep_eq card_seq x_neq_0 by fastforce
        obtain n where n_def:"Rep_nat_int i = {n..n + (x+y) -1}" using rep_i by auto
        have n_le:"n \<le> n+(x-1)" by simp
        have x_le:"n+(x) \<le> n + (x+y)-1" using y_neq_0 by linarith
        obtain j  where j_def:" j = Abs_nat_int {n..n+(x-1)}" by blast
        from n_le have j_in_type:" {n..n+(x-1)} \<in> {S . (\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={} }"
          by blast
        obtain k where k_def:" k =Abs_nat_int {n+x..n+(x+y)-1}" by blast
        from x_le have k_in_type:" {n+x..n+(x+y)-1} \<in> {S . (\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={} }"
          by blast
        have consec: "consec j k" 
          by (metis j_def k_def One_nat_def Suc_leI add.assoc diff_add n_le consec_def leq_max_sup' leq_min_inf' leq_nat_non_empty neq0_conv x_le x_neq_0)
        have union:"i = j \<squnion> k" 
          by (smt Abs_nat_int_inverse j_def k_def Rep_nat_int_inverse consec mem_Collect_eq n_def n_le consec_def leq_max_sup' leq_min_inf' union_def un_consec_seq x_le)
        have disj:"j \<sqinter> k = \<emptyset>" using consec by (simp add: consec_inter_empty)
        have chop:"N_Chop(i,j,k)" using consec union disj nchop_def by simp
        have card_j:"|j| = x" 
          using Abs_nat_int_inverse j_def n_le card'.rep_eq x_neq_0 by auto
        have card_k:"|k| = y"
          using Abs_nat_int_inverse k_def x_le card'.rep_eq x_neq_0 y_neq_0 by auto
        have "N_Chop(i,j,k) \<and> |j| = x \<and> |k| = y" using chop card_j card_k by blast
        thus "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" by blast
      qed
    qed
  qed
qed
  
lemma chop_single:"(N_Chop(i,j,k) \<and> |i| = 1) \<longrightarrow> ( |j| =0 \<or> |k|=0)"
  using chop_add1 by force
    
lemma chop_leq_max:"N_Chop(i,j,k) \<and> consec j k \<longrightarrow> 
  (\<forall>n . n \<in> Rep_nat_int i \<and> n \<le> maximum j \<longrightarrow> n \<in> Rep_nat_int j)" 
  by (smt Rep_nat_int_inverse atLeastAtMost_iff bot_nat_int.rep_eq consec_def dual_order.trans equals0D le_add1 leq_min_inf' nat_int.leq_max_sup nat_int.maximum_def nat_int.nchop_def nat_int.rep_non_empty_means_seq nat_int.un_consec_seq union_def)
    
lemma chop_geq_min:"N_Chop(i,j,k) \<and> consec j k \<longrightarrow> 
  (\<forall>n . n \<in> Rep_nat_int i \<and> minimum k \<le> n \<longrightarrow> n \<in> Rep_nat_int k)" 
  by (smt Rep_nat_int_inverse atLeastAtMost_iff atLeastatMost_empty_iff bot_nat_int.rep_eq consec_def leq_max_sup' nat_int.card_seq nat_int.leq_min_inf' nat_int.nchop_def nat_int.un_consec_seq union_def)
    
    
lemma chop_min:"N_Chop(i,j,k) \<and> consec j k \<longrightarrow> minimum i = minimum j"
proof 
  assume assm:"N_Chop(i,j,k) \<and> consec j k"
  then have j_subs_l:"\<forall>n . n \<in> Rep_nat_int i \<and> n \<le> maximum j \<longrightarrow> n \<in> Rep_nat_int j"
    using chop_leq_max by blast   
  from assm have j_non_e:"j \<noteq> \<emptyset>" and k_non_e:"k \<noteq> \<emptyset>"  using consec_def by blast+
  have min_in_l:"minimum i \<in> Rep_nat_int i" 
    using assm card_non_empty_geq_one minimum_in consec_def el_def chop_add1 by auto
  hence min_in_j:"minimum i \<in> Rep_nat_int j" 
  proof -
    have f1: "i \<noteq> \<emptyset>"
      using Abs_nat_int_inverse empty_type bot_nat_int.rep_eq min_in_l by blast
    then obtain nn :: "nat_int \<Rightarrow> nat" and nna :: "nat_int \<Rightarrow> nat" where "nn i \<le> nna i \<and> {nn i..nna i} = Rep_nat_int i"
      by (meson rep_non_empty_means_seq)
    then show ?thesis
      using f1 by (metis (no_types) Min_le assm finite_atLeastAtMost j_subs_l maximum_in min_in_l minimum_def consec_def el.rep_eq less_eq_nat_int.rep_eq un_subset1 nchop_def set_rev_mp)
  qed
  have "\<forall>n . n \<in> Rep_nat_int j \<longrightarrow>  minimum i \<le> n" 
    by (metis (no_types, lifting) Min_le bot_nat_int.rep_eq assm empty_iff  finite_atLeastAtMost minimum_def card_seq less_eq_nat_int.rep_eq un_subset1 nchop_def subsetCE)
  thus "minimum i = minimum j" 
    by (metis Min_in Min_le all_not_in_conv antisym assm finite_atLeastAtMost min_in_j minimum_def consec_def rep_non_empty_means_seq)
qed
  
lemma chop_max:"N_Chop(i,j,k) \<and> consec j k \<longrightarrow> maximum i = maximum k"
proof
  assume assm:"N_Chop(i,j,k) \<and> consec j k"
  then have j_non_e:"j \<noteq> \<emptyset>" and k_non_e:"k \<noteq> \<emptyset>" by (simp add: consec_def)+
  from assm have "maximum i \<in> Rep_nat_int i" 
    using add_is_0 card_empty_zero card_non_empty_geq_one j_non_e maximum_in el_def chop_add1 by auto
  from assm have k_subs_l:"\<forall>n . n \<in> Rep_nat_int i \<and> minimum k \<le> n \<longrightarrow> n \<in> Rep_nat_int k"
    using chop_geq_min by blast   
  then have max_in_k:"maximum i \<in> Rep_nat_int k" 
    by (metis Rep_nat_int_inverse \<open>maximum i \<in> Rep_nat_int i\<close> assm atLeastAtMost_iff contra_subsetD k_non_e less_eq_nat_int.rep_eq nat_int.el.rep_eq nat_int.leq_max_sup' nat_int.minimum_in nat_int.nchop_def nat_int.non_empty_elem_in nat_int.rep_non_empty_means_seq un_subset2)
  have "\<forall>n . n \<in> Rep_nat_int k \<longrightarrow>  n \<le> maximum i" 
    by (metis assm atLeastAtMost_iff bot_nat_int.rep_eq contra_subsetD empty_iff less_eq_nat_int.rep_eq nat_int.leq_max_sup nat_int.maximum_def nat_int.nchop_def nat_int.rep_non_empty_means_seq nat_int.un_subset2)
  then show "maximum i = maximum k" 
    by (metis Max_ge max_in_k dual_order.antisym finite_atLeastAtMost k_non_e maximum_def maximum_in el.rep_eq rep_non_empty_means_seq)
qed
  
lemma chop_assoc1:"N_Chop(i,i1,i2) \<and> N_Chop(i2,i3,i4) \<longrightarrow> (N_Chop(i, i1 \<squnion> i3, i4) \<and> N_Chop(i1 \<squnion> i3, i1, i3))"
proof 
  assume assm:"N_Chop(i,i1,i2) \<and> N_Chop(i2,i3,i4)"
  then have chop_def:"(i =  i1 \<squnion> i2  \<and> i1 \<sqinter> i2 = \<emptyset> \<and>
        (i1 = \<emptyset> \<or>  i2 = \<emptyset> \<or> ( consec i1 i2)))"
    using nchop_def by blast
  hence "(i1 = \<emptyset> \<or>  i2 = \<emptyset> \<or> ( consec i1 i2))" by simp 
  then show "N_Chop(i, i1 \<squnion> i3, i4) \<and> N_Chop(i1 \<squnion> i3, i1, i3)"
  proof 
    assume empty:"i1 = \<emptyset>"
    then have l_eq_i2:"i = i2" by (simp add: chop_def un_empty_absorb2)
    from empty have i1_un_i3:"i1 \<squnion> i3 = i3" by (simp add: un_empty_absorb2 )
    thus "N_Chop(i,i1 \<squnion> i3, i4) \<and> N_Chop(i1 \<squnion> i3, i1, i3)"
      by (simp add: assm empty l_eq_i2 chop_empty_left)
  next
    assume "i2 = \<emptyset> \<or> ( consec i1 i2)"
    then show "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)"
    proof 
      assume empty:"i2 = \<emptyset>"
      then have l_eq_i1:" i= i1" by (simp add: chop_def un_empty_absorb1)
      from empty have i3_empty:"i3 = \<emptyset>" 
        by (metis assm inf.absorb1 inter_empty1 un_empty_absorb1 un_subset1 nchop_def)
      from empty have i4_empty:"i4 = \<emptyset>" 
        using assm i3_empty un_empty_absorb2 nchop_def by auto  
      then show "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
        using assm chop_def empty i3_empty l_eq_i1 by auto
    next
      assume " consec i1 i2"
      then have consec_i1_i2:"i1 \<noteq>\<emptyset> \<and> i2 \<noteq>\<emptyset> \<and> maximum i1 +1 = minimum i2" 
        using consec_def by blast
      from assm have "i3 = \<emptyset> \<or> i4 = \<emptyset> \<or> consec i3 i4" 
        using nchop_def by blast
      then show "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
      proof
        assume i3_empty:"i3 = \<emptyset>"
        then have i1_sq_i3:"i1 \<squnion> i3 = i1" using un_empty_absorb1 by blast
        from i3_empty have "i2 = i4" 
          using assm un_empty_absorb2 nchop_def by auto
        thus "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" using assm i1_sq_i3 
          by (simp add: i3_empty chop_empty_right)
      next 
        assume "i4 = \<emptyset> \<or> consec i3 i4"
        then show "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
        proof
          assume i4_empty:"i4 = \<emptyset>"
          then have  i2_eq_i3:"i2 = i3" 
            using assm un_empty_absorb1 nchop_def by auto
          thus "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)"  
            using assm chop_def i4_empty chop_empty_right by auto
        next
          assume consec_i3_i4:"consec i3 i4"
          hence i3_max_i4_min:"maximum i3+1 = minimum i4" using consec_def by blast
          have "minimum i3 = minimum i2" 
            using \<open>consec i3 i4\<close> assm chop_min by auto
          hence consec_i1_i3:"consec i1 i3" 
            using consec_i1_i2 consec_i3_i4 consec_def by auto
          hence "consec (i1 \<squnion> i3) i4" 
            using assm consec_assoc1 consec_i1_i2 consec_i3_i4  nchop_def by auto
          thus "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
            using assm consec_inter_empty consec_i1_i3 consec_i3_i4 un_assoc nchop_def by auto 
        qed
      qed
    qed
  qed
qed
  
lemma chop_assoc2:"N_Chop(i,i1,i2) \<and> N_Chop(i1,i3,i4) \<longrightarrow> N_Chop(i, i3, i4 \<squnion> i2) \<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
proof 
  assume assm: "N_Chop(i,i1,i2) \<and> N_Chop(i1,i3,i4)"
  hence "(i1 = \<emptyset> \<or>  i2 = \<emptyset> \<or> ( consec i1 i2))" 
    using nchop_def by blast 
  then show "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)"
  proof
    assume i1_empty:"i1 = \<emptyset>"
    then have i3_empty:"i3 = \<emptyset>" 
      by (metis assm inf_absorb1 inter_empty1 un_empty_absorb1 un_subset1 nchop_def)
    from i1_empty have i4_empty:"i4 = \<emptyset>" 
      using assm i3_empty un_empty_absorb2 nchop_def by auto
    then show "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
      using assm i3_empty chop_empty_left nchop_def by auto
  next
    assume "i2 = \<emptyset> \<or> consec i1 i2"
    thus "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)"
    proof
      assume i2_empty:"i2=\<emptyset>"
      then have l_eq_i1:"i = i1" 
        using assm chop_empty_right nchop_def by auto
      have "i4 \<squnion> i2 = i4" 
        by (simp add: i2_empty un_empty_absorb1)
      thus "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
        by (simp add: assm i2_empty l_eq_i1 chop_empty_right) 
    next
      assume consec_i1_i2:"consec i1 i2"
      from assm have "(i3 = \<emptyset> \<or>  i4 = \<emptyset> \<or> ( consec i3 i4))" 
        by (simp add: nchop_def)
      thus "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)"
      proof
        assume i3_empty:"i3=\<emptyset>"
        then have i1_eq_i3:"i1 = i4" 
          using assm un_empty_absorb2 nchop_def by auto
        thus "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
          using assm i3_empty chop_empty_left nchop_def by auto
      next
        assume " i4 = \<emptyset> \<or> ( consec i3 i4)"
        thus "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
        proof
          assume i4_empty:"i4=\<emptyset>"
          hence i1_eq_i3:"i1 = i3" 
            using assm un_empty_absorb1 nchop_def by auto
          thus "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
            using assm i4_empty un_empty_absorb2 chop_empty_left by auto 
        next
          assume consec_i3_i4:"consec i3 i4"
          have "maximum i4 = maximum i1" 
            using assm consec_i3_i4 chop_max by auto 
          then have consec_i4_i2:"consec i4 i2" 
            using consec_i1_i2 consec_i3_i4 consec_def by auto 
          then have consec_i3_un:"consec i3 (i4 \<squnion> i2)" 
            using assm consec_assoc2 consec_i1_i2 consec_i3_i4 nchop_def by auto
          thus "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
            using assm consec_inter_empty consec_i3_i4 consec_i4_i2 un_assoc nchop_def by auto
        qed
      qed
    qed
  qed
qed
  
lemma chop_subset1:"N_Chop(i,j,k) \<longrightarrow> j \<sqsubseteq> i"
  using nat_int.chop_empty_right nat_int.nchop_def nat_int.un_subset1 by auto
    
lemma chop_subset2:"N_Chop(i,j,k) \<longrightarrow> k \<sqsubseteq> i" 
  using nat_int.chop_empty_left nat_int.nchop_def nat_int.un_subset2 by auto
    
end
end