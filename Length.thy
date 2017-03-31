(*  Title:      perfect/Length.thy
    Author:     Sven Linker

FIXME:
The length of cars visible to the owner of a given view given 
perfect sensors. The length is stable, of we switch owners of the view.
*)

section\<open>Visible Length of Cars with Perfect Sensors\<close>
theory Length
imports "Traffic" Sensors
begin

context sensors
begin
  
definition len:: "view \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real_int"
  where len_def :"len v ( ts ) c ==
    if (left (space ts v c) > right (ext v))  
      then  Abs_real_int (right (ext v),right (ext v)) 
    else
      if (right (space ts v c) < left (ext v)) 
        then Abs_real_int (left (ext v),left (ext v))
      else  
        Abs_real_int (max (left (ext v)) (left (space ts v c)), 
                      min (right (ext v)) (right (space ts v c)))"

lemma len_left: " left ((len v  ts) c) \<ge> left (ext v)" 
proof - 
  have "(left ((space ts v) c) \<le> right (ext v) \<and> right ((space ts v) c) \<ge> left (ext v)) 
      \<or> left ((space ts v) c) > right (ext v) \<or> right ((space ts v) c) < left (ext v)" 
    using leI by blast
  then show "left ((len v  ts) c) \<ge> left (ext v)"
  proof
    assume  "left ((space ts v) c) \<le> right (ext v) \<and> left (ext v) \<le> right ((space ts v) c)"
    with len_def have " len v ( ts) c = Abs_real_int (max (left (ext v)) (left ((space ts v) c)),
        min (right (ext v)) (right ((space ts v) c)))" by simp
    hence "left (len v ( ts) c) = max (left (ext v)) (left ((space ts v) c))" 
      using Abs_real_int_inverse Rep_real_int \<open>left ((space ts v) c) \<le> right (ext v) \<and> left (ext v) \<le> right ((space ts v) c)\<close> 
      by auto
    thus "left ((len v  ts) c) \<ge> left (ext v)" by simp
  next 
    show "right (ext v) < left ((space ts v) c) \<or> right ((space ts v) c) < left (ext v) \<Longrightarrow>
        left (ext v) \<le> left (len v ( ts) c)" using len_def 
      using Abs_real_int_inverse CollectI fst_conv real_int.left_leq_right snd_conv by auto 
  qed
qed  

lemma len_right: " right ((len v  ts) c) \<le> right (ext v)"
proof  -
  have "(left ((space ts v) c) \<le> right (ext v) \<and> right ((space ts v) c) \<ge> left (ext v)) 
      \<or> left ((space ts v) c) > right (ext v) \<or> right ((space ts v) c) < left (ext v)" 
    using leI by blast
  then show "right ((len v  ts) c) \<le> right (ext v) "
  proof
    assume  "left ((space ts v) c) \<le> right (ext v) \<and> left (ext v) \<le> right ((space ts v) c)"
    with len_def have " len v ( ts) c = Abs_real_int (max (left (ext v)) (left ((space ts v) c)),
        min (right (ext v)) (right ((space ts v) c)))" by simp
    hence "right (len v ( ts) c) = min (right (ext v)) (right ((space ts v) c))" 
      using Abs_real_int_inverse Rep_real_int \<open>left ((space ts v) c) \<le> right (ext v) \<and> left (ext v) \<le> right ((space ts v) c)\<close> 
      by auto
    thus "right ((len v  ts) c) \<le> right (ext v) " by simp
  next 
    show "right (ext v) < left ((space ts v) c) \<or> right ((space ts v) c) < left (ext v) \<Longrightarrow>
      right ((len v  ts) c) \<le> right (ext v)" 
      using   Abs_real_int_inverse CollectI fst_conv real_int.left_leq_right snd_conv len_def by auto
  qed
qed

lemma len_sub_int:"len v ts c \<le> ext v" 
  using less_eq_real_int_def len_left len_right by blast

lemma len_space_left: "left (space ts v c) \<le> right (ext v) \<longrightarrow> left (len v ts c) \<ge> left (space ts v c)" 
proof
  assume assm:"left (space ts v c) \<le> right (ext v)"
  then show "left (len v ts c) \<ge> left (space ts v c)" 
  proof (cases "right ((space ts v) c) < left (ext v)" )
    case True
    then show ?thesis using len_def len_left real_int.left_leq_right 
      by (meson le_less_trans not_less order.asym)
  next
    case False
    then have "len v ts c = (Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), min (right (ext v)) (right ((space ts v) c))))"
      using len_def assm by auto
    then have "left (len v ts c) = max (left (ext v)) (left ((space ts v) c))" using Abs_real_int_inverse 
      using False assm real_int.left_leq_right by auto
    then show ?thesis  by linarith
  qed
qed    

lemma len_space_right: "right (space ts v c) \<ge> left (ext v) \<longrightarrow> right (len v ts c) \<le> right (space ts v c)" 
proof
  assume assm:"right (space ts v c) \<ge> left (ext v)"
  then show "right (len v ts c) \<le> right (space ts v c)" 
  proof (cases "left ((space ts v) c) > right (ext v)" )
    case True
    then show ?thesis using len_def len_right real_int.left_leq_right 
      by (meson le_less_trans not_less order.asym)
  next
    case False
    then have "len v ts c = (Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), min (right (ext v)) (right ((space ts v) c))))"
      using len_def assm by auto
    then have "right (len v ts c) = min (right (ext v)) (right ((space ts v) c))" using Abs_real_int_inverse 
      using False assm real_int.left_leq_right by auto
    then show ?thesis  by linarith
  qed
qed    

    
lemma len_hchop_left_right_border: "((len v ts) c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> (right ((len v1 ts) c) = right (ext v1))"
proof
  assume assm:"((len v ts) c = ext v) \<and> (v=v1\<parallel>v2)"
  have l1:"left ((len v ts) c) = left (ext v)" using assm by auto 
  from assm have l2:"left (ext v) = left (ext v1)" 
    by (simp add: hchop_def real_int.rchop_def)
  from l1 and l2 have l3:"left ((len v ts) c) = left (ext v1)" by simp  
  have r1:"right ((len v ts) c) = right (ext v)" using assm by auto
  have r2:"right (ext v1) \<le> right (ext v)" 
    by (metis (no_types, lifting) assm hchop_def real_int.rchop_def real_int.left_leq_right)  
  have r3:"right ((len v1 ts) c) \<le> right (ext v1)" 
    using len_right by blast
  show "right ((len v1 ts) c) = right (ext v1)" 
  proof (rule ccontr)
    assume contra:"right ((len v1 ts) c) \<noteq> right (ext v1)"
    with r3 have less:"right ((len v1 ts) c) < right (ext v1)" by simp
    show False
    proof (cases "left ((space ts v) c) \<le> right (ext v1)")
      assume neg1:"\<not> left ((space ts v) c) \<le> right (ext v1)" 
      have "right ((len v1 ts) c) = right (ext v1)" 
      proof -   
        have "(len v1 ts) c = Abs_real_int (right (ext v1),right (ext v1))"
          using len_def  neg1 using assm hchop_def space_def by auto
        thus "right ((len v1 ts) c) = right (ext v1)" 
          by (metis real_int.chop_assoc2 real_int.chop_singleton_right real_int.rchop_def)
      qed
      with contra show False ..
    next
      assume less1:"left ((space ts v) c) \<le> right (ext v1)"
      show False
      proof (cases "right ((space ts v) c) \<ge> left (ext v1)")
        assume neg2:"\<not> left (ext v1) \<le> right ((space ts v) c)"
        have "right ((len v1 ts) c) = right (ext v1)" 
        proof -
          have "(len v1 ts) c = Abs_real_int (left (ext v1),left (ext v1))"
            using len_def  neg2 assm hchop_def real_int.left_leq_right less1 space_def by auto 
          hence  "right ((len v1 ts) c) = left ((len v1 ts )c)" 
            using l3 assm contra less1 len_def neg2 r2 r3  real_int.left_leq_right  by auto
          with l1 have "right((len v1 ts)c ) = right (ext v)" 
            using assm l2 len_def neg2 assm hchop_def less1 real_int.left_leq_right r2 space_def by auto
          hence "right (ext v) = right (ext v1)" 
            using r2 r3 by auto
          thus "right ((len v1 ts) c) = right (ext v1)" 
            using \<open>right (len v1 ts c) = right (ext v)\<close> by auto
        qed
        with contra  show False ..
      next
        assume less2:"left (ext v1) \<le> right ((space ts v) c)"
        have len_in_type:"((max (left (ext v1)) (left ((space ts v) c)), min (right (ext v1)) (right ((space ts v) c)))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
          using Rep_real_int less1 less2 by auto
        from less1 and less2 have len_def_v1:"len v1 ( ts) c = 
                Abs_real_int ((max (left (ext v1)) (left ((space ts v) c))), 
                              min (right (ext v1)) (right ((space ts v) c)))" 
          using len_def assm hchop_def  space_def by auto
        with less have "min (right (ext v1)) (right ((space ts v) c)) = right ((space ts v) c)"
          using Abs_real_int_inverse len_in_type snd_conv by auto
        hence "right ((space ts v) c) \<le> right (ext v1)" by simp
        hence "right ((space ts v) c) \<le> right (ext v)" 
          using r2 by linarith
        from len_def_v1 and less and len_in_type
        have "right ((space ts v) c) < right (ext v1)" 
          using Abs_real_int_inverse sndI by auto
        hence "right ((space ts v) c) < right (ext v)" 
          using r2 by linarith
        from assm have len_v_in_type:"((max (left (ext v)) (left ((space ts v) c)), min (right (ext v)) (right ((space ts v) c)))) \<in> {r :: real*real . fst r \<le> snd r}"                 
          using \<open>right ((space ts v) c) < right (ext v)\<close> l2 len_in_type by auto            
        hence " right (len v ( ts) c) \<noteq> right (ext v)" 
          using Abs_real_int_inverse Pair_inject \<open>right ((space ts v) c) < right (ext v)\<close> len_def real_int.left_leq_right surjective_pairing by auto 
        with r1 show False by best
      qed 
    qed
  qed
qed

lemma len_hchop_left_left_border: "((len v ts) c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> (left ((len v1 ts) c) = left (ext v1))"
proof
  assume assm:"((len v ts) c = ext v) \<and> (v=v1\<parallel>v2)"
  have l1:"left ((len v ts) c) = left (ext v)" using assm by auto 
  from assm have l2:"left (ext v) = left (ext v1)" 
    by (simp add: hchop_def real_int.rchop_def)
  from l1 and l2 have l3:"left ((len v ts) c) = left (ext v1)" by simp  
  have r1:"right ((len v ts) c) = right (ext v)" using assm by auto
  have r2:"right (ext v1) \<le> right (ext v)" 
    by (metis (no_types, lifting) assm hchop_def real_int.rchop_def real_int.left_leq_right)  
  have r3:"right ((len v1 ts) c) \<le> right (ext v1)" 
    using len_right by blast
  show "(left ((len v1 ts) c) = left (ext v1))"  
  proof (cases "left ((space ts v) c) \<le> right (ext v1) \<and> right ((space ts v) c) \<ge> left (ext v1)")
    assume inside:"left ((space ts v) c) \<le> right (ext v1) \<and> right ((space ts v) c) \<ge> left (ext v1)"      
    show "(left ((len v1 ts) c) = left (ext v1))"
    proof (rule ccontr)
      assume neq:" left (len v1 ( ts) c) \<noteq> left (ext v1)"
      then have greater: "left (len v1 ( ts) c) > left (ext v1)" 
      proof -
        have "left (ext v1) \<noteq> left (len v1 ( ts) c) \<and> left (ext v1) + - 1 * left (len v1 ( ts) c) \<le> 0"
          using len_left neq by fastforce
        then show ?thesis by auto
      qed
      have len_in_type:"((max (left (ext v1)) (left ((space ts v) c)), min (right (ext v1)) (right ((space ts v) c)))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
        using Rep_real_int inside by auto
      from inside have "len v1 ( ts) c =  Abs_real_int ((max (left (ext v1)) (left ((space ts v) c))), 
                              min (right (ext v1)) (right ((space ts v) c)))" 
        using len_def assm hchop_def space_def by auto
      hence maximum:"left (len v1 ( ts) c) = max (left (ext v1)) (left ((space ts v) c))" 
        using Abs_real_int_inverse len_in_type by auto  
      have "max (left (ext v1)) (left ((space ts v) c)) = left ((space ts v) c)" 
        using maximum neq by linarith
      hence "left ((space ts v) c) > left (ext v1)" 
        using greater maximum by auto
      hence "left ((space ts v) c) > left (ext v)" using l2 by auto
      with assm have len_v_in_type:"((max (left (ext v)) (left ((space ts v) c)), min (right (ext v)) (right ((space ts v) c)))) \<in> {r :: real*real . fst r \<le> snd r}"   
        using len_in_type r2 by auto 
      hence " left (len v ( ts) c) \<noteq> left (ext v)" 
        using Abs_real_int_inverse Pair_inject \<open>left ((space ts v) c) > left (ext v)\<close> len_def real_int.left_leq_right surjective_pairing by auto 
      thus False using l1 by best
    qed
  next
    assume outside:"\<not>(left ((space ts v) c) \<le> right (ext v1) \<and> right ((space ts v) c) \<ge> left (ext v1))"
    then have "\<not>left ((space ts v) c) \<le> right (ext v1) \<or> \<not>right ((space ts v) c) \<ge> left (ext v1)"
      by auto
    thus "(left ((len v1 ts) c) = left (ext v1))"
    proof
      assume negative:"\<not> left ((space ts v) c) \<le> right (ext v1)"
      then have "len v1 ( ts) c = Abs_real_int (right (ext v1),right (ext v1))"
        using len_def assm hchop_def space_def by auto
      hence empty:"left (len v1 ( ts) c) = right (len v1 ( ts) c)" 
        by (metis real_int.chop_assoc2 real_int.chop_singleton_right real_int.rchop_def)
      have len_geq:"left(len v1 ( ts) c) \<ge> left (ext v)"  
        using l2 len_left by auto
      show "left (len v1 ( ts) c) = left (ext v1)"
      proof (rule ccontr)
        assume contra:"left (len v1 ( ts) c) \<noteq> left (ext v1)"
        with len_left have "left (ext v1) < left (len v1 ( ts) c)  " 
        proof -
          have "left (ext v1) \<noteq> left (len v1 ( ts) c) \<and> left (ext v1) + - 1 * left (len v1 ( ts) c) \<le> 0"
            using contra len_left by fastforce
          then show ?thesis by simp
        qed
        hence "left (ext v) < left (len v1 ( ts) c)" using l2 by auto 
        hence "left (len v ( ts) c) < left (len v1 ( ts) c)" using l1 by auto
        show "False" 
        proof (cases "left ((space ts v) c) \<le> right (ext v)")
          assume ls_leq_vr:"left ((space ts v) c) \<le> right (ext v)"
          have well_sp:"left ((space ts v) c) \<le> right ((space ts v) c)"  
            using real_int.left_leq_right by auto
          have well_v:"left (ext v) \<le> right (ext v)"
            using real_int.left_leq_right by auto   
          hence rs_geq_vl:"right ((space ts v) c) \<ge> left (ext v)" 
            using empty len_geq negative r3 well_sp by linarith
          from ls_leq_vr and rs_geq_vl have len_in_type:"((max (left (ext v)) (left ((space ts v) c)), min (right (ext v)) (right ((space ts v) c)))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
            using CollectD CollectI Rep_real_int fst_conv snd_conv by auto
          have "len v ( ts) c  = Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), 
                              min (right (ext v)) (right ((space ts v) c)))" 
            using len_def using ls_leq_vr rs_geq_vl by auto 
          hence max_less:"max (left (ext v)) (left ((space ts v) c)) <  left (len v1 ( ts) c)" 
            using Abs_real_int_inverse 
            by (metis (full_types) \<open>left (ext v) < left (len v1 ts c)\<close> assm fst_conv left.rep_eq len_in_type)
          show False 
            using empty max_less negative r3 by auto 
        next
          assume "\<not> left ((space ts v) c) \<le> right (ext v)"
          then have "len v ( ts) c = Abs_real_int (right (ext v), right (ext v))"
            using len_def by auto
          hence empty_len_v:"left (len v ( ts) c) = right (ext v)" using Abs_real_int_inverse 
            by simp
          show False 
            using \<open>left (len v ( ts) c) < left (len v1 ( ts) c)\<close> empty empty_len_v r2 r3 by linarith
        qed 
      qed
    next
      have "space ts v1 c \<le> space ts v c" using assm hchop_def space_def by auto
      hence r4:"right (space ts v1 c) \<le> right (space ts v c)" using  less_eq_real_int_def by auto 
      assume left_outside:"\<not> left (ext v1) \<le> right ((space ts v) c)"
      hence "left (ext v1 ) > right (space ts v1 c)" using r4 by linarith
      then have "len v1 ( ts) c = Abs_real_int (left (ext v1),left (ext v1))"
        using len_def assm hchop_def real_int.left_leq_right r1 r2 l1 l2 l3 r3  
        by (meson le_less_trans less_trans not_less)
      thus "(left ((len v1 ts) c) = left (ext v1))"
        using  Abs_real_int_inverse by auto
    qed
  qed
qed

lemma len_view_hchop_left: "((len v ts) c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> ((len v1 ts) c = ext v1)"
  using Abs_real_int_inverse len_hchop_left_left_border len_hchop_left_right_border prod.expand
  by (metis Rep_real_int_inject left.rep_eq right.rep_eq)

lemma len_hchop_right_left_border: "((len v ts) c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> (left ((len v2 ts) c) = left (ext v2))"
proof
  assume assm:"((len v ts) c = ext v) \<and> (v=v1\<parallel>v2)"
  have r1:"right ((len v ts) c) = right (ext v)" using assm by auto 
  from assm have r2:"right (ext v) = right (ext v2)" 
    by (simp add: hchop_def real_int.rchop_def)
  from r1 and r2 have r3:"right ((len v ts) c) = right (ext v2)" by simp  
  have l1:"left ((len v ts) c) = left (ext v)" using assm by auto
  have l2:"left (ext v2) \<ge> left (ext v)" 
    by (metis (no_types, lifting) assm hchop_def real_int.rchop_def real_int.left_leq_right)  
  have l3:"left ((len v2 ts) c) \<ge> left (ext v2)" 
    using len_left by blast
  show "left ((len v2 ts) c) = left (ext v2)" 
  proof (rule ccontr)
    assume contra:"left ((len v2 ts) c) \<noteq> left (ext v2)"
    with l3 have less:"left ((len v2 ts) c) > left (ext v2)" by simp
    show False
    proof (cases "left ((space ts v) c) \<le> right (ext v2)")
      assume neg1:"\<not> left ((space ts v) c) \<le> right (ext v2)" 
      have "left ((len v2 ts) c) = left (ext v2)" 
      proof -   
        have "(len v2 ts) c = Abs_real_int (right (ext v2),right (ext v2))"
          using len_def  neg1 assm hchop_def space_def by auto
        thus "left ((len v2 ts) c) = left (ext v2)" 
          using assm l2 l3 len_def neg1 r3 by auto
      qed
      with contra show False ..
    next
      assume less1:"left ((space ts v) c) \<le> right (ext v2)"
      show False
      proof (cases "right ((space ts v) c) \<ge> left (ext v2)")
        assume neg2:"\<not> left (ext v2) \<le> right ((space ts v) c)"
        have "space ts v2 c \<le> space ts v c" using assm hchop_def space_def by auto
        hence "right (space ts v2 c) \<le> right (space ts v c)" using less_eq_real_int_def by auto
        with neg2 have greater:"left (ext v2 ) > right (space ts v2 c)" by auto
        have "left ((len v2 ts) c) = left (ext v2)"
        proof -
          have len_empty:"(len v2 ts) c = Abs_real_int (left (ext v2),left (ext v2))"
            using len_def  neg2 assm hchop_def   less1 space_def by auto
          have "left((len v2 ts)c ) = left (ext v)" 
            using Abs_real_int_inverse len_def less neg2  assm hchop_def 
              CollectI len_empty prod.collapse prod.inject by auto 
          hence "left (ext v) = left (ext v2)" 
            using l2 l3 by auto
          thus "left ((len v2 ts) c) = left (ext v2)" using   \<open>left (len v2 ( ts) c) = left (ext v)\<close> by auto
        qed
        with contra  show False ..
      next
        assume less2:"left (ext v2) \<le> right ((space ts v) c)"
        have len_in_type:"((max (left (ext v2)) (left ((space ts v) c)), min (right (ext v2)) (right ((space ts v) c)))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
          using Rep_real_int less1 less2 by auto
        from less1 and less2 have len_def_v2:"len v2 ( ts) c = 
                Abs_real_int ((max (left (ext v2)) (left ((space ts v) c))), 
                              min (right (ext v2)) (right ((space ts v) c)))" 
          using len_def assm hchop_def space_def by auto
        with less have "max (left (ext v2)) (left ((space ts v) c)) = left ((space ts v) c)"
          using Abs_real_int_inverse len_in_type snd_conv by auto
        hence "left ((space ts v) c) \<ge> left (ext v2)" by simp
        hence "left ((space ts v) c) \<ge> left (ext v)" 
          using l2 by auto
        from len_def_v2 and less and len_in_type
        have "left ((space ts v) c) > left (ext v2)" 
          using Abs_real_int_inverse sndI by auto
        hence "left ((space ts v) c) > left (ext v)" 
          using l2 by linarith
        from assm have len_v_in_type:"((max (left (ext v)) (left ((space ts v) c)), min (right (ext v)) (right ((space ts v) c)))) \<in> {r :: real*real . fst r \<le> snd r}"                 
          using \<open>left ((space ts v) c) > left (ext v)\<close> r2 len_in_type by auto
            
        hence " left (len v ( ts) c) \<noteq> left (ext v)" 
          using Abs_real_int_inverse Pair_inject \<open>left ((space ts v) c) > left (ext v)\<close> len_def real_int.left_leq_right surjective_pairing by auto 
        with l1 show False by best
      qed 
    qed
  qed
qed

lemma len_hchop_right_right_border: "((len v ts) c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> (right ((len v2 ts) c) = right (ext v2))"
proof
  assume assm:"((len v ts) c = ext v) \<and> (v=v1\<parallel>v2)"
  have r1:"right ((len v ts) c) = right (ext v)" using assm by auto 
  from assm have r2:"right (ext v) = right (ext v2)" 
    by (simp add: hchop_def real_int.rchop_def)
  from r1 and r2 have r3:"right ((len v ts) c) = right (ext v2)" by simp  
  have l1:"left ((len v ts) c) = left (ext v)" using assm by auto
  have l2:"left (ext v2) \<le> right (ext v)" 
    by (metis (no_types, lifting) assm hchop_def real_int.rchop_def real_int.left_leq_right)  
  have l3:"left ((len v2 ts) c) \<ge> left (ext v2)" 
    using len_left by blast
  show "(right ((len v2 ts) c) = right (ext v2))"  
  proof (cases "left ((space ts v) c) \<le> right (ext v2) \<and> right ((space ts v) c) \<ge> left (ext v2)")
    assume inside:"left ((space ts v) c) \<le> right (ext v2) \<and> right ((space ts v) c) \<ge> left (ext v2)"
    show "(right ((len v2 ts) c) = right (ext v2))"
    proof (rule ccontr)
      assume neq:" right (len v2 ( ts) c) \<noteq> right (ext v2)"
      then have lesser: "right (len v2 ( ts) c) < right (ext v2)" 
        using len_right less_eq_real_def by blast 
      have len_in_type:"((max (left (ext v2)) (left ((space ts v) c)), min (right (ext v2)) (right ((space ts v) c)))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
        using Rep_real_int inside by auto
      from inside have "len v2 ( ts) c =  Abs_real_int ((max (left (ext v2)) (left ((space ts v) c))), 
                              min (right (ext v2)) (right ((space ts v) c)))" 
        using len_def assm hchop_def space_def by auto
      hence maximum:"right (len v2 ( ts) c) = min (right (ext v2)) (right ((space ts v) c))" 
        using Abs_real_int_inverse len_in_type by auto  
      have min_right:"min (right (ext v2)) (right ((space ts v) c)) = right ((space ts v) c)" 
        using maximum neq by linarith
      hence "right ((space ts v) c) < right (ext v2)" 
        using lesser maximum by auto
      hence "right ((space ts v) c) < right (ext v)" using r2 by auto
      have right_inside:"right ((space ts v) c) \<ge> left (ext v)"
      proof -
        have f1: "left (ext v) = left (ext v1)"
          using assm hchop_def real_int.rchop_def by blast
        have "right (ext v1) = left (ext v2)"
          using assm hchop_def real_int.rchop_def by blast
        then show ?thesis
          using f1 by (metis (no_types) \<open>min (right (ext v2)) (right ((space ts v) c)) = right ((space ts v) c)\<close> assm len_hchop_right_left_border maximum order_trans real_int.left_leq_right)
      qed 
      with assm and inside and right_inside
      have len_v_in_type:"((max (left (ext v)) (left ((space ts v) c)), min (right (ext v)) (right ((space ts v) c)))) \<in> {r :: real*real . fst r \<le> snd r}"   
        using min_right r2 real_int.left_leq_right by auto
      hence " right (len v ( ts) c) \<noteq> right (ext v)" 
        using Abs_real_int_inverse Pair_inject \<open>right ((space ts v) c) < right (ext v)\<close> len_def real_int.left_leq_right surjective_pairing 
        by auto 
      thus False using r1 by best
    qed
  next
    assume outside:"\<not>(left ((space ts v) c) \<le> right (ext v2) \<and> right ((space ts v) c) \<ge> left (ext v2))"
    then have "\<not>left ((space ts v) c) \<le> right (ext v2) \<or> \<not>right ((space ts v) c) \<ge> left (ext v2)"
      by auto
    thus "(right ((len v2 ts) c) = right (ext v2))"
    proof
      assume negative:"\<not> left ((space ts v) c) \<le> right (ext v2)"
      then have "len v2 ( ts) c = Abs_real_int (right (ext v2),right (ext v2))"
        using len_def assm hchop_def space_def by auto
      hence empty:"left (len v2 ( ts) c) = right (len v2 ( ts) c)" 
        by (simp add: Abs_real_int_inverse)
      have len_geq:"right(len v2 ( ts) c) \<le> right (ext v)"  
        using len_right r2 by auto  
      show "right (len v2 ( ts) c) = right (ext v2)"
      proof (rule ccontr)
        assume contra:"right (len v2 ( ts) c) \<noteq> right (ext v2)"
        with len_right have "right (ext v2) > right (len v2 ( ts) c)  " 
          using less_eq_real_def by blast
        hence "right (ext v) > right (len v2 ( ts) c)" using r2 by auto 
        hence "right (len v ( ts) c) > right (len v2 ( ts) c)" 
          using r1 by auto
        show "False" 
        proof (cases "left ((space ts v) c) \<le> right (ext v)")
          assume ls_leq_vr:"left ((space ts v) c) \<le> right (ext v)"
          have well_sp:"left ((space ts v) c) \<le> right ((space ts v) c)"  
            using real_int.left_leq_right by auto
          have well_v:"left (ext v) \<le> right (ext v)"
            using real_int.left_leq_right by auto   
          hence rs_geq_vl:"right ((space ts v) c) \<ge> left (ext v)" 
            using empty len_geq negative l3 well_sp ls_leq_vr r2 by linarith 
          from ls_leq_vr and rs_geq_vl have len_in_type:"((max (left (ext v)) (left ((space ts v) c)), min (right (ext v)) (right ((space ts v) c)))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
            using CollectD CollectI Rep_real_int fst_conv snd_conv by auto
          have "len v ( ts) c  = Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), 
                              min (right (ext v)) (right ((space ts v) c)))" 
            using len_def using ls_leq_vr rs_geq_vl by auto 
          hence max_less:"max (left (ext v)) (left ((space ts v) c)) >  left (len v2 ( ts) c)"
            using ls_leq_vr negative r2 by auto
          show False 
            using empty max_less negative r3  ls_leq_vr r2 by auto
        next
          assume "\<not> left ((space ts v) c) \<le> right (ext v)"
          then have "len v ( ts) c = Abs_real_int (right (ext v), right (ext v))"
            using len_def by auto
          hence empty_len_v:"left (len v ( ts) c) = right (ext v)" using Abs_real_int_inverse by simp
          show False 
            using \<open>len v ( ts) c = Abs_real_int (right (ext v), right (ext v))\<close> 
              \<open>len v2 ( ts) c = Abs_real_int (right (ext v2), right (ext v2))\<close> assm 
              contra r2 by auto
        qed 
      qed
    next
      assume left_outside:"\<not> left (ext v2) \<le> right ((space ts v) c)"
      hence "left (ext v2) > right (space ts v2 c)" using assm hchop_def space_def by auto 
      then have len:"len v2 ( ts) c = Abs_real_int (left (ext v2),left (ext v2))"
        using len_def assm hchop_def 
        by (metis (no_types, hide_lams) l2 le_less_trans not_less order.asym space_nonempty r2)   
      show "(right ((len v2 ts) c) = right (ext v2))" 
      proof (cases "right ((space ts v) c) \<ge> left (ext v)")
        assume "\<not> left (ext v) \<le> right ((space ts v) c)"
        hence "len v (ts) c = Abs_real_int (left (ext v), left (ext v))" 
          using len_def real_int.left_leq_right Abs_real_int_inverse  
          by (meson less_trans not_less space_nonempty)
        show "(right ((len v2 ts) c) = right (ext v2))"  
        proof -
          obtain rr :: "real_int \<Rightarrow> real_int" where
            f1: "\<forall>r. R_Chop(r,rr r,r)"
            using real_int.chop_singleton_left by moura
          then have f2: "\<And>r. left r = right (rr r)"
            by (simp add: real_int.rchop_def)
          have f3: "lan v = lan v2"
            using assm hchop_def by blast
          have f4: "R_Chop(ext v,ext v1,ext v2)"
            using assm hchop_def by blast
          then have f5: "left (ext v) = left (ext v1)"
            using real_int.rchop_def by blast
          have f6: "right (ext v) = right (ext v2)"
            using f4 real_int.rchop_def by auto
          have f7: "left (ext v2) = right (ext v1)"
            using f4 by (simp add: real_int.rchop_def)
          have f8: "\<And>r. (left r, left r) = Rep_real_int (rr r)" 
            by (metis f1 left.rep_eq prod.collapse real_int.rchop_def right.rep_eq)
              
          have "left (ext v1) \<le> left (ext v2)" 
            using f7 real_int.left_leq_right by auto
          then show ?thesis
            using f8 f6 f5 f3 f2 
            using Rep_real_int_inverse \<open>len v ts c = Abs_real_int (left (ext v), left (ext v))\<close> assm l2 len by auto
        qed
      next
        assume rs_geq_vl: "left (ext v) \<le> right ((space ts v) c)"
        have empty:"left (len v2 ( ts) c) = right (len v2 ( ts) c)" 
          by (simp add: len Abs_real_int_inverse)
        have well_sp:"left ((space ts v) c) \<le> right ((space ts v) c)" 
          using real_int.left_leq_right by blast
        have "left (ext v) \<le> right (ext v)" 
          using real_int.left_leq_right by blast
        have ls_leq_vr:"left ((space ts v) c) \<le>  right (ext v)" 
          using l2 left_outside well_sp by auto
        from ls_leq_vr and rs_geq_vl have len_in_type:"((max (left (ext v)) (left ((space ts v) c)), min (right (ext v)) (right ((space ts v) c)))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
          using CollectD CollectI Rep_real_int fst_conv snd_conv by auto
        have len_at_v:"len v ( ts) c  = Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), 
                              min (right (ext v)) (right ((space ts v) c)))" 
          using len_def using ls_leq_vr rs_geq_vl by auto 
        have non_full:"right ((space ts v) c) < right (ext v)" using left_outside l2 by auto
        hence right_border:"right (len v ( ts) c) = right ((space ts v) c)" 
          using Abs_real_int_inverse len_at_v len_in_type by auto
        show ?thesis using non_full r1 right_border by auto
      qed
    qed
  qed
qed

lemma len_view_hchop_right: "((len v ts) c = ext v) \<and> (v=v1\<parallel>v2) \<longrightarrow> ((len v2 ts) c = ext v2)"
  using Abs_real_int_inverse len_hchop_right_left_border len_hchop_right_right_border prod.expand
  by (metis Rep_real_int_inject left.rep_eq right.rep_eq)


lemma len_compose_hchop:"(v=v1\<parallel>v2) \<and> (len v1 ( ts) c = ext v1) \<and> (len v2 ( ts) c = ext v2)
                          \<longrightarrow> (len v ( ts) c = ext v)"
proof
  assume assm:"(v=v1\<parallel>v2) \<and> (len v1 ( ts) c = ext v1) \<and> (len v2 ( ts) c = ext v2)"
  then have left_v1:"left (len v1 ( ts) c) = left (ext v1)" by auto
  from assm have right_v1:"right (len v1 ( ts) c) = left (ext v2)" 
    by (simp add: hchop_def real_int.rchop_def)
  from assm have left_v2:"left (len v2 ( ts) c) = right (ext v1)" 
    using right_v1 by auto
  from assm have right_v2:"right (len v2 ( ts) c) = right (ext v2)" by auto
  show "(len v ( ts) c = ext v)" 
  proof (cases " left ((space ts v) c) > right (ext v)")
    case True      
    then have "left (space ts v c) > right (ext v2)" using assm right_v2 
      by (simp add: hchop_def real_int.rchop_def)
    then have "left (space ts v2 c) > right( ext v2)" 
      using assm hchop_def sensors.space_def sensors_axioms by auto
    then have "len v2 ts c = Abs_real_int(right (ext v2), right (ext v2))" using len_def by simp
    then have "ext v2 = Abs_real_int(right (ext v2), right (ext v2))" using assm by simp
    then have "\<parallel>ext v2\<parallel> = 0" using real_int.length_def Abs_real_int_inverse 
      by (metis Rep_real_int_inverse fst_conv left.rep_eq real_int.chop_singleton_right real_int.length_zero_iff_borders_eq real_int.rchop_def right.rep_eq snd_conv surj_pair)
    then have "ext v = ext v1" using assm hchop_def real_int.rchop_def real_int.chop_empty2 by simp
    then show ?thesis 
      using assm hchop_def len_def sensors.space_def sensors_axioms by auto
  next
    case False
    then have in_left:"left (space ts v c) \<le> right (ext v)" by simp
    show "len v ts c = ext v"
    proof (cases "right (space ts v c) < left (ext v)")
      case True
      then have "right (space ts v c) < left (ext v1)" using assm left_v1 by (simp add: hchop_def real_int.rchop_def)
      then have out_v1:"right (space ts v1 c) < left (ext v1)"
        using assm hchop_def sensors.space_def sensors_axioms by auto
      then have "len v1 ts c = Abs_real_int(left (ext v1), left (ext v1))" using len_def in_left 
        by (meson le_less_trans less_trans not_le real_int.left_leq_right)   
      then have "ext v1 = Abs_real_int (left (ext v1), left (ext v1))" using assm by simp
      then have "\<parallel>ext v1\<parallel> = 0" using real_int.length_def Abs_real_int_inverse
        by (metis add.right_neutral real_int.chop_singleton_left real_int.length_zero_iff_borders_eq real_int.rchop_def real_int.shift_def real_int.shift_zero)
      then have "ext v = ext v2" using assm hchop_def real_int.rchop_def real_int.chop_empty1 by blast
      then show ?thesis 
        using assm hchop_def len_def sensors.space_def sensors_axioms by auto            
    next
      case False
      then  have in_right:"right (space ts v c) \<ge> left (ext v)"  by simp
      have f1: "own v = own v2"
        by (meson assm hchop_def)
      have f2: "own v = own v1"
        using assm hchop_def by blast
      have chop:"R_Chop(ext v,ext v1,ext v2)"
        by (meson assm hchop_def)
      have len:"len v ts c = Abs_real_int(max (left (ext v)) (left (space ts v c)), 
                      min (right (ext v)) (right (space ts v c)))" using len_def in_left in_right by simp
      have len1:"len v1 ts c = Abs_real_int(max (left (ext v1)) (left (space ts v1 c)), 
                      min (right (ext v1)) (right (space ts v1 c)))" using len_def in_left in_right assm f2 f1 chop 
        by (metis assm in_left in_right len_def len_space_left not_le real_int.rchop_def space_def)
      then have "max (left (ext v1)) (left (space ts v1 c)) = left (len v1 ts c)" 
        by (metis assm chop f1 f2 in_left len_space_left max.orderE real_int.rchop_def space_def)
      then have left_border:"max (left (ext v1)) (left (space ts v1 c)) = left (ext v1)" using left_v1 by simp
      have len2:"len v2 ts c = Abs_real_int(max (left (ext v2)) (left (space ts v2 c)), 
                      min (right (ext v2)) (right (space ts v2 c)))" using len_def in_left in_right assm f2 f1 chop 
        by (metis len_space_right not_le real_int.rchop_def space_def)
      then have "min (right (ext v2)) (right (space ts v2 c)) = right (len v2 ts c)" 
        by (metis assm chop f1 f2 in_right len_space_right min.absorb_iff1 real_int.rchop_def space_def)
      then have right_border:"min (right (ext v2)) (right (space ts v2 c)) = right (ext v2)" using right_v2 by simp
      have "left (space ts v c) = left (space ts v1 c)" 
        using assm hchop_def sensors.space_def sensors_axioms by auto
      then have max:"max (left (ext v)) (left (space ts v c)) = max (left (ext v1)) (left (space ts v1 c))" 
        using assm hchop_def real_int.rchop_def by auto
      have "right (space ts v c) = right (space ts v2 c)" 
        using assm hchop_def sensors.space_def sensors_axioms by auto
      then have min:"min (right (ext v)) (right (space ts v c)) = min (right (ext v2)) (right (space ts v2 c))" 
        using assm hchop_def real_int.rchop_def by auto
      show ?thesis using min max left_border right_border assm  
        by (metis False add.right_neutral chop in_left len_def not_le real_int.rchop_def real_int.shift_def real_int.shift_zero)
    qed
  qed
qed
  

lemma len_stable:"(v=v1--v2) \<longrightarrow> len v1 ( ts) c = len v2 ( ts) c"
proof
  assume assm:"v=v1--v2"
  then have ext_eq1:"ext v = ext v1" and ext_eq2:"ext v = ext v2" 
    using vchop_def by blast+
  hence ext1_eq_ext2:"ext v1 = ext v2" by simp
  show "len v1 ( ts) c = len v2 ( ts) c" 
  proof (cases " left ((space ts v) c) \<le> right (ext v)")
    assume outside_right:" \<not> left ((space ts v) c) \<le> right (ext v)"
    show "len v1 ( ts) c = len v2 ( ts) c" 
      using ext1_eq_ext2 ext_eq1 len_def outside_right vchop_def assm space_def by auto
  next
    assume inside_right:"left ((space ts v) c) \<le> right (ext v)"
    show "len v1 ( ts) c = len v2 ( ts) c" 
    proof (cases " right ((space ts v) c) \<ge> left (ext v)")
      assume outside_left:"\<not>right ((space ts v) c) \<ge> left (ext v)"
      show "len v1 ( ts) c = len v2 ( ts) c" 
        using ext1_eq_ext2 ext_eq1 len_def outside_left vchop_def assm space_def by auto 
    next
      assume inside_left :" right ((space ts v) c) \<ge> left (ext v)"
      show "len v1 ( ts) c = len v2 ( ts) c" 
        using ext1_eq_ext2 ext_eq1 inside_left inside_right len_def vchop_def assm space_def by auto
    qed
  qed
qed

lemma len_empty_on_subview1:"\<parallel>len v ( ts) c\<parallel> = 0 \<and> (v=v1\<parallel>v2) \<longrightarrow> \<parallel>len v1 ( ts) c\<parallel> = 0"
proof
  assume assm:"\<parallel>len v ( ts) c\<parallel> = 0 \<and> (v=v1\<parallel>v2)"
  then have len_v_borders:"left (len v ( ts) c) = right (len v ( ts) c)" by (simp add:real_int.length_zero_iff_borders_eq)  
  show "\<parallel>len v1 ( ts) c\<parallel> = 0" 
  proof (cases "left ((space ts v) c) > right (ext v1)")
    assume left_outside_v1:"left ((space ts v) c) > right (ext v1)"  
    thus "\<parallel>len v1 ( ts) c\<parallel> = 0" 
      using Abs_real_int_inverse assm fst_conv hchop_def len_def real_int.length_zero_iff_borders_eq mem_Collect_eq snd_conv space_def by auto
  next
    assume left_inside_v1:"\<not>left ((space ts v) c) > right (ext v1)"
    show "\<parallel>len v1 ( ts) c\<parallel> = 0" 
    proof (cases "left (ext v1) > right ((space ts v) c)")
      assume right_outside_v1:"left (ext v1) > right ((space ts v) c)" 
      hence "left (ext v1) > right ((space ts v1) c)" using assm hchop_def space_def by auto
      thus "\<parallel>len v1 (ts) c\<parallel> = 0" 
        using assm hchop_def len_def real_int.length_def  Abs_real_int_inverse by auto
    next 
      assume right_inside_v1:"\<not>left (ext v1) > right ((space ts v) c)"
      have len_v1:"len v1 ( ts) c = Abs_real_int ((max (left (ext v1)) (left ((space ts v) c))), 
                              min (right (ext v1)) (right ((space ts v) c)))" 
        using left_inside_v1 len_def right_inside_v1 assm hchop_def space_def by auto
      from left_inside_v1 and right_inside_v1 have inside_v:"\<not>left ((space ts v) c) > right (ext v) \<and> \<not>left (ext v) > right ((space ts v) c)"
        by (smt assm h_chop_middle2 hchop_def real_int.rchop_def)
      hence len_v:"len v ( ts) c = Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), 
                              min (right (ext v)) (right ((space ts v) c)))" 
        by (simp add: len_def)
      have less_eq:"(max (left (ext v)) (left ((space ts v) c))) \<le> min (right (ext v)) (right ((space ts v) c))"
        using inside_v real_int.left_leq_right by auto        
      from len_v have len_v_empty: "(max (left (ext v)) (left ((space ts v) c))) = min (right (ext v)) (right ((space ts v) c))" 
        using Abs_real_int_inverse Rep_real_int_inverse inside_v
        using len_v_borders local.less_eq by auto
      have left_len_eq:"(max (left (ext v)) (left ((space ts v) c))) = max (left (ext v1)) (left ((space ts v) c))"
        using assm hchop_def real_int.rchop_def by auto
      have right_len_leq:"min (right (ext v)) (right ((space ts v) c)) \<ge> min (right (ext v1)) (right ((space ts v) c))"
        by (smt assm h_chop_middle2 hchop_def real_int.rchop_def)
      hence left_geq_right:"max (left (ext v1)) (left ((space ts v) c))\<ge> min (right (ext v1)) (right ((space ts v) c))"
        using left_len_eq len_v_empty by auto
      thus "\<parallel>len v1 ( ts) c\<parallel> = 0" 
      proof -
        have f1: "\<not> max (left (ext v)) (left (space ts v c)) \<le> min (right (ext v1)) (right (space ts v c)) \<or> min (right (ext v1)) (right (space ts v c)) = max (left (ext v)) (left (space ts v c))"
          by (metis antisym_conv left_geq_right left_len_eq)
        have "\<And>r. \<not> left (ext v1) \<le> r \<or> \<not> left (space ts v c) \<le> r \<or> max (left (ext v)) (left (space ts v c)) \<le> r"
          using left_len_eq by auto
        then have "min (right (ext v1)) (right (space ts v c)) = max (left (ext v)) (left (space ts v c))"
          using f1 inside_v left_inside_v1 real_int.left_leq_right by force
        then show ?thesis
          using assm left_len_eq len_v len_v1 len_v_empty by auto
      qed
    qed
  qed
qed

lemma len_empty_on_subview2:"\<parallel>len v ( ts) c\<parallel> = 0 \<and> (v=v1\<parallel>v2) \<longrightarrow> \<parallel>len v2 ( ts) c\<parallel> = 0"
proof
  assume assm:"\<parallel>len v ( ts) c\<parallel> = 0 \<and> (v=v1\<parallel>v2)"
  then have len_v_borders:"left (len v ( ts) c) = right (len v ( ts) c)" by (simp add:real_int.length_zero_iff_borders_eq)  
  show "\<parallel>len v2 ( ts) c\<parallel> = 0" 
  proof (cases "left ((space ts v) c) > right (ext v2)")
    assume left_outside_v2:"left ((space ts v) c) > right (ext v2)"  
    thus "\<parallel>len v2 ( ts) c\<parallel> = 0" 
      using Abs_real_int_inverse assm fst_conv hchop_def len_def real_int.length_zero_iff_borders_eq mem_Collect_eq snd_conv space_def by auto
  next
    assume left_inside_v2:"\<not>left ((space ts v) c) > right (ext v2)"
    show "\<parallel>len v2 ( ts) c\<parallel> = 0" 
    proof (cases "left (ext v2) > right ((space ts v) c)")
      assume right_outside_v2:"left (ext v2) > right ((space ts v) c)" 
      thus "\<parallel>len v2 ( ts) c\<parallel> = 0" 
        using Abs_real_int_inverse assm fst_conv hchop_def len_def real_int.length_zero_iff_borders_eq mem_Collect_eq snd_conv right_outside_v2 space_def 
        by auto
    next 
      assume right_inside_v2:"\<not>left (ext v2) > right ((space ts v) c)"
      have len_v2:"len v2 ( ts) c = Abs_real_int ((max (left (ext v2)) (left ((space ts v) c))), 
                              min (right (ext v2)) (right ((space ts v) c)))" 
        using left_inside_v2 len_def right_inside_v2 assm hchop_def space_def by auto
      from left_inside_v2 and right_inside_v2 have inside_v:"\<not>left ((space ts v) c) > right (ext v) \<and> \<not>left (ext v) > right ((space ts v) c)"
        by (smt assm h_chop_middle1 hchop_def real_int.rchop_def)
      hence len_v:"len v ( ts) c = Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), 
                              min (right (ext v)) (right ((space ts v) c)))" 
        by (simp add: len_def)
      have less_eq:"(max (left (ext v)) (left ((space ts v) c))) \<le> min (right (ext v)) (right ((space ts v) c))"
        using inside_v real_int.left_leq_right by auto        
      from len_v have len_v_empty: "(max (left (ext v)) (left ((space ts v) c))) = min (right (ext v)) (right ((space ts v) c))"
        using Abs_real_int_inverse Rep_real_int_inverse inside_v
        using len_v_borders local.less_eq by auto
      have left_len_eq:"(max (left (ext v)) (left ((space ts v) c))) \<le> max (left (ext v2)) (left ((space ts v) c))"
        by (smt assm h_chop_middle1 h_chop_middle2 hchop_def len_v_empty real_int.rchop_def right_inside_v2)
      have right_len_leq:"min (right (ext v)) (right ((space ts v) c)) = min (right (ext v2)) (right ((space ts v) c))"
        by (smt assm h_chop_middle2 hchop_def real_int.rchop_def)   
      hence left_geq_right:"max (left (ext v2)) (left ((space ts v) c)) \<ge> min (right (ext v2)) (right ((space ts v) c))"
        using left_len_eq len_v_empty by auto
      then have "max (left (ext v2)) (left ((space ts v2) c)) \<ge> min (right (ext v2)) (right ((space ts v2) c))"
        using assm hchop_def space_def by auto
      then have "max (left (ext v2)) (left ((space ts v2) c)) = min (right (ext v2)) (right ((space ts v2) c))"
        using Abs_real_int_inverse 
        by (metis (no_types, hide_lams) antisym_conv assm hchop_def len_v_empty max_def min.bounded_iff not_le space_def right_inside_v2 right_len_leq view.h_chop_middle2)
      thus "\<parallel>len v2 ( ts) c\<parallel> = 0" using Abs_real_int_inverse 
        by (metis (no_types, hide_lams) assm hchop_def len_v len_v2 len_v_empty space_def right_len_leq)
    qed
  qed
qed

lemma len_hchop_add:"(v=v1\<parallel>v2) \<longrightarrow> \<parallel>len v ( ts) c\<parallel> = \<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel>"
proof
  assume chop:"v=v1\<parallel>v2"
  show "\<parallel>len v (ts) c\<parallel> = \<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel>"
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence len_zero:"\<parallel>len v ( ts) c\<parallel> = 0" 
      by (simp add: Abs_real_int_inverse  len_def real_int.length_zero_iff_borders_eq snd_eqD)
    with chop have "\<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel> = 0" 
      by (smt len_empty_on_subview1 len_empty_on_subview2)
    thus ?thesis by (simp add: len_zero)
  next 
    assume inside_right:"\<not>left ((space ts v) c) > right (ext v)"   
    show "\<parallel>len v ( ts) c\<parallel> = \<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel>"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence len_zero:"\<parallel>len v ( ts) c\<parallel> = 0" 
        by (simp add: Abs_real_int_inverse  len_def real_int.length_zero_iff_borders_eq snd_eqD)
      with chop have "\<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel> = 0" 
        by (smt len_empty_on_subview1 len_empty_on_subview2)
      thus ?thesis by (simp add: len_zero)
    next 
      assume inside_left:" \<not>left (ext v) > right ((space ts v) c) "
      hence len_def_v:"len v ( ts) c = 
                Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), 
                              min (right (ext v)) (right ((space ts v) c)))"
        using len_def inside_left inside_right by simp
      from inside_left and inside_right have len_in_type:"((max (left (ext v)) (left ((space ts v) c)), min (right (ext v)) (right ((space ts v) c)))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
        using CollectD CollectI Rep_real_int fst_conv snd_conv by auto          
      show "\<parallel>len v ( ts) c\<parallel> = \<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel>"
      proof (cases "right (len v ( ts) c) < right (ext v1)")
        assume inside_v1:"right (len v ( ts) c) < right (ext v1)"
        hence min_less_v1:"min (right (ext v)) (right ((space ts v) c)) < right (ext v1)" 
          using Abs_real_int_inverse len_in_type len_def_v by auto
        hence outside_v2:"right ((space ts v) c) < left (ext v2)" 
          using chop hchop_def real_int.rchop_def h_chop_middle2 by (smt h_chop_middle2)
        hence len_v2_0:"\<parallel>len v2 ( ts) c\<parallel> = 0" using  Abs_real_int_inverse len_def real_int.length_zero_iff_borders_eq outside_v2  snd_eqD
            Rep_real_int_inverse chop hchop_def prod.collapse real_int.rchop_def real_int.chop_singleton_right space_def by auto
        have inside_left_v1:"  \<not>left (ext v1) > right ((space ts v) c) " 
          using chop hchop_def inside_left real_int.rchop_def by auto 
        have inside_right_v1:"\<not>left ((space ts v) c) > right (ext v1)" 
          by (meson inside_right less_trans min_less_iff_disj min_less_v1 order.asym space_nonempty)
        have len1_def:"len v1 ( ts) c = 
                Abs_real_int ((max (left (ext v1)) (left ((space ts v) c))), 
                              min (right (ext v1)) (right ((space ts v) c)))"        
          using len_def inside_left_v1 inside_right_v1 chop hchop_def space_def by auto
        hence "\<parallel>len v ( ts) c\<parallel> = \<parallel>len v1 ( ts) c\<parallel>" using inside_v1 inside_left 
          by (smt chop h_chop_middle2 hchop_def len_def_v outside_v2 real_int.rchop_def)
        thus "\<parallel>len v ( ts) c\<parallel> = \<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel>" 
          by (simp add: len_v2_0)
      next
        assume r_inside_v2:"\<not> right (len v ( ts) c) < right (ext v1)"
        show "\<parallel>len v ( ts) c\<parallel> = \<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel>"
        proof (cases "left (len v ( ts) c) > left (ext v2)")
          assume inside_v2:"left (len v ( ts) c) > left (ext v2)"
          hence max_geq_v1:"max (left (ext v)) (left ((space ts v) c)) > left (ext v2)" 
            using Abs_real_int_inverse len_in_type len_def by (simp )
          hence outside_v1:"left ((space ts v) c) > right (ext v1)" 
            using chop hchop_def real_int.rchop_def h_chop_middle1 by smt
          hence len_v1_0:"\<parallel>len v1 ( ts) c\<parallel> = 0" using
              Abs_real_int_inverse len_def real_int.length_zero_iff_borders_eq outside_v1  snd_eqD
              Rep_real_int_inverse chop hchop_def prod.collapse real_int.rchop_def real_int.chop_singleton_right space_def by auto
          have inside_left_v2:"  \<not>left (ext v2) > right ((space ts v) c) "
            by (meson inside_left less_max_iff_disj less_trans max_geq_v1 order.asym space_nonempty)
          have inside_right_v2:"\<not>left ((space ts v) c) > right (ext v2)" 
            using chop hchop_def inside_right real_int.rchop_def by auto
          have len2_def:"len v2 ( ts) c = 
                Abs_real_int ((max (left (ext v2)) (left ((space ts v) c))), 
                              min (right (ext v2)) (right ((space ts v) c)))"        
            using len_def inside_left_v2 inside_right_v2 hchop_def chop space_def by auto
          hence "\<parallel>len v ( ts) c\<parallel> = \<parallel>len v2 ( ts) c\<parallel>" using inside_v2 inside_left    
            by (smt chop h_chop_middle1 hchop_def len_def_v outside_v1 real_int.rchop_def)       
          thus "\<parallel>len v ( ts) c\<parallel> = \<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel>" 
            by (simp add: len_v1_0)
        next
          assume l_inside_v1: "\<not>left (len v ( ts) c) > left (ext v2)"
          have inside_left_v1:"  \<not>left (ext v1) > right ((space ts v) c) " 
            using chop hchop_def inside_left real_int.rchop_def by auto 
          have inside_right_v1:"\<not>left ((space ts v) c) > right (ext v1)" 
            using Abs_real_int_inverse chop hchop_def l_inside_v1 len_in_type len_def real_int.rchop_def by auto
          hence len1_def:"len v1 ( ts) c = 
                Abs_real_int ((max (left (ext v1)) (left ((space ts v) c))), 
                              min (right (ext v1)) (right ((space ts v) c)))"
            using inside_left_v1 inside_right_v1 len_def chop hchop_def space_def                 
            by (simp )
          from inside_left_v1 and inside_right_v1 have len1_in_type:"((max (left (ext v1)) (left ((space ts v) c)), min (right (ext v1)) (right ((space ts v) c)))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
            using CollectD CollectI Rep_real_int fst_conv snd_conv by auto
              
          have inside_left_v2:"  \<not>left (ext v2) > right ((space ts v) c) " 
            using real_int.rchop_def hchop_def inside_left chop Abs_real_int_inverse len_def_v len_in_type r_inside_v2 snd_conv by auto 
          have inside_right_v2:"\<not>left ((space ts v) c) > right (ext v2)" 
            using Abs_real_int_inverse chop hchop_def l_inside_v1 len_in_type len_def real_int.rchop_def by auto
          hence len2_def:"len v2 ( ts) c = 
                Abs_real_int ((max (left (ext v2)) (left ((space ts v) c))), 
                              min (right (ext v2)) (right ((space ts v) c)))"
            using inside_left_v2 inside_right_v2 len_def chop hchop_def space_def                  
            by (auto )
          from inside_left_v2 and inside_right_v2 have len2_in_type:"((max (left (ext v2)) (left ((space ts v) c)), min (right (ext v2)) (right ((space ts v) c)))) 
            \<in> {r :: real*real . fst r \<le> snd r}" 
            using CollectD CollectI Rep_real_int fst_conv snd_conv by auto
          have left_v_v1:"left (ext v) = left (ext v1)" 
            using chop hchop_def real_int.rchop_def by blast
          have max: "(max (left (ext v)) (left ((space ts v) c))) = 
                (max (left (ext v1)) (left ((space ts v) c)))"                 
            using left_v_v1 by auto  
          have right_v_v2:"right (ext v) = right (ext v2)" 
            using chop hchop_def real_int.rchop_def by auto
          have min: "(min (right (ext v)) (right ((space ts v) c))) = 
                (min (right (ext v2)) (right ((space ts v) c)))"                 
            using right_v_v2 by auto
          from max have left_len_v1_v:"left (len v ( ts) c) = left (len v1 ( ts) c)"
            using Abs_real_int_inverse fst_conv len1_def len1_in_type len_def_v len_in_type by auto
          from min have right_len_v2_v:"right (len v ( ts) c) = right (len v2 ( ts) c)"
            using Abs_real_int_inverse fst_conv len1_def len2_in_type len_def_v 
              len_in_type using len2_def snd_eqD by auto
          have "right (len v1 ( ts) c) = left (len v2 ( ts) c)" 
            using Abs_real_int_inverse chop hchop_def len1_def len1_in_type len2_def len2_in_type real_int.rchop_def by auto
          thus "\<parallel>len v ( ts) c\<parallel> = \<parallel>len v1 ( ts) c\<parallel> + \<parallel>len v2 ( ts) c\<parallel>" 
            using left_len_v1_v real_int.consec_add right_len_v2_v by blast 
        qed
      qed
    qed
  qed
qed
  


lemma len_non_empty_inside: "\<parallel>len v ( ts) c\<parallel> > 0 \<longrightarrow> left ((space ts v) c) < right (ext v) \<and> right ((space ts v) c) > left (ext v)"
proof
  assume assm: "\<parallel>len v ( ts) c\<parallel> > 0"
  show "left ((space ts v) c) < right (ext v) \<and> right ((space ts v) c) > left (ext v)"
  proof (rule ccontr)
    assume "\<not>(left ((space ts v) c) < right (ext v) \<and> right ((space ts v) c) > left (ext v))"
    hence "\<not>left ((space ts v) c) < right (ext v) \<or> \<not>right ((space ts v) c) > left (ext v)" by best
    thus False
    proof
      assume "\<not>left ((space ts v) c) < right (ext v)"
      hence "(left ((space ts v) c) = right (ext v)) \<or> left ((space ts v) c) > right (ext v)" by auto
      thus False
      proof 
        assume left_eq:"left ((space ts v) c) = right (ext v)"
        hence inside_left:"right ((space ts v) c) \<ge> left (ext v)" by (metis order_trans real_int.left_leq_right)
        from left_eq and inside_left have 
          len_v: "len v ( ts) c = Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), 
                              min (right (ext v)) (right ((space ts v) c)))" using len_def by auto
        hence "len v ( ts) c = Abs_real_int (left ((space ts v) c), left((space ts v) c))" 
          by (metis left_eq max_def min_def real_int.left_leq_right)
        thus False using Abs_real_int_inverse assm real_int.length_def by auto
      next
        assume "left ((space ts v) c) > right (ext v)"
        thus False 
          using Abs_real_int_inverse assm len_def real_int.length_def by auto
      qed
    next
      assume "\<not>right ((space ts v) c) > left (ext v)"
      hence "right ((space ts v) c) = left (ext v) \<or> right ((space ts v) c) < left (ext v)" by auto
      thus False
      proof 
        assume right_eq:"right ((space ts v) c) = left (ext v)"
        hence inside_right:"right (ext v) \<ge> left ((space ts v) c)" by (metis order_trans real_int.left_leq_right)
        from right_eq and inside_right have 
          len_v: "len v ( ts) c = Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), 
                              min (right (ext v)) (right ((space ts v) c)))" using len_def by auto
        hence "len v ( ts) c = Abs_real_int(right ((space ts v) c), right ((space ts v) c))" 
          by (metis max.commute max_def min_def real_int.left_leq_right right_eq)
        thus False using Abs_real_int_inverse assm real_int.length_def by auto
      next
        assume "right ((space ts v) c) < left (ext v)"
        thus False 
          using Abs_real_int_inverse assm len_def real_int.length_def 
        proof -
          have "left (space ts v c) < right (ext v)"
            by (meson \<open>right (space ts v c) < left (ext v)\<close> less_le_trans linorder_not_less real_int.left_leq_right)
          then show ?thesis
            using \<open>\<And>y. y \<in> {r. fst r \<le> snd r} \<Longrightarrow> Rep_real_int (Abs_real_int y) = y\<close> \<open>right (space ts v c) < left (ext v)\<close> assm len_def real_int.length_def by force
        qed
      qed
    qed
  qed
qed
        
lemma len_fills_subview:"\<parallel>len v ( ts) c\<parallel> > 0 \<longrightarrow> 
                         ( \<exists> v1 v2 v3 v'. (v=v1\<parallel>v2) \<and> (v2=v'\<parallel>v3) \<and> len v' ( ts) c = ext v' \<and> \<parallel>len v' ( ts) c\<parallel> = \<parallel>len v ( ts) c\<parallel>)"
proof
  assume assm: "\<parallel>len v ( ts) c\<parallel> > 0" 
  show " \<exists> v1 v2 v3 v'. (v=v1\<parallel>v2) \<and> (v2=v'\<parallel>v3) \<and> len v' ( ts) c = ext v' \<and> \<parallel>len v' ( ts) c\<parallel> = \<parallel>len v ( ts) c\<parallel>"
  proof -
    from assm have inside:"left ((space ts v) c) < right (ext v) \<and> right ((space ts v) c) > left (ext v)" 
      using len_non_empty_inside by auto
    hence len_v: "len v ( ts) c = Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), 
                              min (right (ext v)) (right ((space ts v) c)))" using len_def by auto
    
    obtain v1 and v2 and v3 and v' where v1:"v1=\<lparr> ext = Abs_real_int(left (ext v), left (len v ( ts) c)), lan = lan v, own = own v \<rparr> "                              
      and v2:"v2=\<lparr> ext = Abs_real_int(left (len v ( ts) c), right (ext v)), lan = lan v, own = own v \<rparr>"
      and v':"v'=\<lparr> ext = Abs_real_int(left (len v ( ts) c), right (len v ( ts) c)), lan = lan v, own = own v \<rparr>"
      and v3:"v3=\<lparr> ext = Abs_real_int(right (len v ( ts) c), right (ext v)), lan = lan v, own = own v \<rparr>" by blast 
    hence 1:" (v=v1\<parallel>v2) \<and> (v2=v'\<parallel>v3)"
      using inside hchop_def real_int.rchop_def   Abs_real_int_inverse real_int.left_leq_right v1 v2 v' v3 
        len_def by auto
    have right:"right (ext v') = right (len v ts c)" 
      by (simp add: Rep_real_int_inverse  v')
    then have right':"left ((space ts v) c) \<le> right (ext v')" using len_non_empty_inside 
      by (metis inside len_space_left less_imp_le order_trans real_int.left_leq_right)
    have left:"left (ext v') = left (len v ts c)"
      by (simp add: Rep_real_int_inverse  v')
    then have left':"right ((space ts v) c) \<ge> left (ext v')" using len_non_empty_inside 
      by (metis inside len_space_right less_imp_le order_trans real_int.left_leq_right)      
    have inside': "left ((space ts v) c) < right (ext v') \<and> right ((space ts v) c) > left (ext v')"
      by (metis (no_types) left' right' antisym_conv assm inside left len_space_left len_space_right less_imp_le not_le real_int.left_leq_right real_int.length_zero_iff_borders_eq right)
    have inside'': "left ((space ts v') c) < right (ext v') \<and> right ((space ts v') c) > left (ext v')" 
      using "1" hchop_def inside' sensors.space_def sensors_axioms by auto
    have len_v_v':"len v ts c = ext v'" using Rep_real_int_inverse 
      by (metis left prod.collapse right left.rep_eq right.rep_eq)
    have "left (len v ts c) = max (left (ext v)) (left ((space ts v) c)) " using len_v Abs_real_int_inverse  Rep_real_int 
      using inside by auto
    with left have left_len':"left (ext v') = max (left (ext v)) (left (space ts v c))" by auto
    then have left_len:"left (ext v') = max (left (ext v')) (left (space ts v' c))" 
      using "1"  hchop_def space_def by fastforce 
    have "right (len v ts c) = min (right (ext v)) (right ((space ts v) c))" using len_v Abs_real_int_inverse inside Rep_real_int by auto
    with right have right_len':"right (ext v') = min (right (ext v)) (right ((space ts v) c))" by auto
    then have  right_len:"right (ext v') = min (right (ext v')) (right ((space ts v') c))"         
      using "1"  hchop_def space_def by fastforce 
    have 2:"len v' ( ts) c = ext v'" using inside'' len_def left_len right_len 
      by (metis left_len' right_len' len_v len_v_v' order.asym) 
    have 3:"  \<parallel>len v' ( ts) c\<parallel> = \<parallel>len v ( ts) c\<parallel>" using len_left len_right hchop_def 
      by (simp add: "2" len_v_v') 
    then show ?thesis using 1 2 3 by blast
  qed
qed

lemma ext_eq_len_eq:"ext v = ext v'\<and> own v = own v'  \<longrightarrow> len v ( ts) c = len v' ( ts) c" 
proof
  assume assm:"ext v = ext v' \<and>  own v = own v'"
  hence sp:"space ts v c = space ts v' c" by (simp add: sensors_def space_def)
  have left_eq:"left (ext v) = left (ext v')" using assm by simp
  have right_eq:"right (ext v) = right (ext v')" using assm by simp
  show "len v ( ts) c = len v' ( ts) c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts v) c) > right (ext v')" using right_eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: len_def right_eq assm sp)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts v) c) > right (ext v')" using right_eq by simp
    show "len v ( ts) c = len v' ( ts) c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v') > right ((space ts v) c) "using left_eq by simp
      from outside_left and outside_left' show ?thesis using len_def left_eq sp 
          right_eq by auto
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v') > right ((space ts v) c) " using left_eq by simp
      from inside_left inside_right inside_left' inside_right' left_eq right_eq
      show ?thesis by (simp add: len_def sp)
    qed
  qed
qed

  
(* These guys should be dependend on the sensor implementation! 
  However, they are valid for both perfect and imperfect information 
as defined in iFM paper

TODO: add them to proofs in the sensor implementations
*)  
(*  
lemma create_reservation_length_stable:"(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c"   by (simp add: create_reservation_def space_def sensors_def)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: len_def)
    qed
  qed
qed
  
lemma create_claim_length_stable:"(ts\<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c" by (simp add: create_claim_def sensors_def space_def)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: len_def)
    qed
  qed
qed
  
lemma withdraw_reservation_length_stable:"(ts\<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c" by (simp add: withdraw_reservation_def sensors_def  space_def)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: len_def)
    qed
  qed
qed
  
lemma withdraw_claim_length_stable:"(ts\<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c" by (simp add: withdraw_claim_def sensors_def space_def)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: len_def)
    qed
  qed
qed
  
  *)
end
end