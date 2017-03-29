(*  Title:      imperfect/Length_ip.thy
    Author:     Sven Linker

The length of cars visible to the owner of a given view given 
imperfect sensors. The length is may reduce, if we switch owners of the view.
*)

section\<open>Visible Length of Cars with Imperfect Sensors\<close>
theory Length_ip
  imports "../Traffic" Sensors_ip
begin
  
context imperfect_sensors
begin
  
definition len:: "view \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real_int"
  where len_def :"len v ( ts ) c \<equiv>
if (left (space ts v c) > right (ext v))  
      then  Abs_real_int (right (ext v),right (ext v)) else
if (right (space ts v c) < left (ext v)) then Abs_real_int (left (ext v),left (ext v))
      else  
  Abs_real_int (max (left (ext v)) (left ((space ts v) c)), min (right (ext v)) (right ((space ts v) c)))"
    
    
lemma len_left: " left ((len v  ts) c) \<ge> left (ext v)"
proof  -
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
        left (ext v) \<le> left (len v ( ts) c)"  
      using len_def Abs_real_int_inverse real_int.left_leq_right by auto
  qed
qed  
  
lemma len_right: " right ((len v  ts) c) \<le> right (ext v)" 
proof -  
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
      right ((len v  ts) c) \<le> right (ext v)" using len_def 
      using Abs_real_int_inverse real_int.left_leq_right by auto
  qed
qed  
  

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
  show "right (len v1 ts c) = right (ext v1)" 
  proof (cases "(left ((space ts v1) c) > right (ext v1))")
    case True
    then have "len v1 ts c = Abs_real_int (right (ext v1),right (ext v1))"
      using len_def by auto      
    then show "right ((len v1 ts) c) = right (ext v1)" using Abs_real_int_inverse by simp
  next
    case False
    then have leq:"left (space ts v1 c) \<le> right (ext v1)" by simp
    show "right ((len v1 ts) c) = right (ext v1)"
    proof (cases "right (space ts v1 c) < left (ext v1)")
      case True
      then have len_v1_empty:"len v1 ts c = Abs_real_int (left (ext v1), left (ext v1))" using leq len_def by auto
      from True have "right (space ts v c) < left (ext v1)" 
        by (metis (no_types, lifting) assm hchop_def space_eq)
      then have "right (space ts v c) < left (ext v)" using l2 by auto 
      then have len_v_empty:"len v ts c = Abs_real_int (left (ext v), left (ext v))" using leq len_def 
        by (meson le_less_trans less_trans h_chop_middle1 horizontal_chop_empty_right order.asym space_nonempty)
      then have "left (ext v) = right (ext v)" using assm Abs_real_int_inverse 
        using hchop_def real_int.rchop_def by auto
      then have "left (ext v1) = right (ext v1)" 
        using len_v_empty len_v1_empty assm l2 r2 r3 by auto
      then show ?thesis using len_v1_empty Abs_real_int_inverse by auto
    next
      case False
      then have geq:"right (space ts v1 c) \<ge> left (ext v1)" by auto
      have owners:"own v1 = own v" using assm hchop_def by auto
      have space:"space ts v1 c = space ts v c" using assm hchop_def space_eq by metis         
      then have right_geq:"right(space ts v1 c) \<ge> right(ext v1)" using assm Abs_real_int_inverse 
        by (metis (no_types, hide_lams) geq l2 len_space_right order_trans r2)
      then have min:"min (right (ext v1)) (right ((space ts v1) c)) = right (ext v1)" 
        by auto
      from leq and geq have len_v1:"len v1 ts c = Abs_real_int (max (left (ext v1)) (left ((space ts v1) c)), min (right (ext v1)) (right ((space ts v1) c)))" 
        using len_def by auto
      then have right:"right (len v1 ts c) = min (right (ext v1)) (right ((space ts v1) c))" 
        by (metis min prod.collapse Rep_real_int_inverse space assm l2 len_space_left left.rep_eq right.rep_eq leq max.orderE order_trans r2)       
      then show ?thesis using right_geq Abs_real_int_inverse len_v1 right by linarith
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
  proof (cases "(left ((space ts v1) c) > right (ext v1))")  
    case True
    then have len_v1_empty:"len v1 ts c = Abs_real_int (right (ext v1),right (ext v1))"
      using len_def by auto      
    from True have "left (space ts v c) > right (ext v1)" 
      by (metis (no_types, lifting) assm hchop_def space_eq)
    then have "left (space ts v c) > left (ext v)" 
      using assm h_chop_middle1 by fastforce    
    then have "left (space ts v c) > right (ext v)" using assm
      by (metis len_space_left not_less)
    then have len_v_empty:"len v ts c = Abs_real_int(right (ext v), right (ext v))" using len_def by auto
    then have "left (ext v) = right (ext v)" using assm Abs_real_int_inverse 
      using hchop_def real_int.rchop_def
      by (metis (no_types, hide_lams) Rep_real_int_inverse left.rep_eq right.rep_eq prod.collapse real_int.chop_singleton_right)
    then have "left (ext v1) = right (ext v1)" 
      using len_v_empty len_v1_empty assm l2 r2  
      using h_chop_middle1 by fastforce
    then show "left ((len v1 ts) c) = left (ext v1)" using Abs_real_int_inverse 
      by (simp add: len_v1_empty)
  next
    case False
    then have leq:"left (space ts v1 c) \<le> right (ext v1)" by simp
    show "left ((len v1 ts) c) = left (ext v1)"
    proof (cases "right (space ts v1 c) < left (ext v1)")
      case True
      then have len_v1_empty:"len v1 ts c = Abs_real_int (left (ext v1), left (ext v1))" using leq len_def by auto
      then show ?thesis using len_v1_empty Abs_real_int_inverse by auto
    next
      case False
      then have geq:"right (space ts v1 c) \<ge> left (ext v1)" by auto
      have owners:"own v1 = own v" using assm hchop_def by auto
      have space:"space ts v1 c = space ts v c" using assm hchop_def space_eq by metis         
      then have right_geq:"left(space ts v1 c) \<le> left(ext v1)" using assm Abs_real_int_inverse 
        by (metis (no_types, hide_lams) l2 le_less_trans len_space_left leq not_less r2)
      then have max:"max (left (ext v1)) (left ((space ts v1) c)) = left (ext v1)" 
        by auto
      from leq and geq have len_v1:"len v1 ts c = Abs_real_int (max (left (ext v1)) (left ((space ts v1) c)), min (right (ext v1)) (right ((space ts v1) c)))" 
        using len_def by auto
      then have left:"left (len v1 ts c) = max (left (ext v1)) (left ((space ts v1) c))" 
        by (smt Rep_real_int_inverse assm geq len_hchop_left_right_border left.rep_eq right.rep_eq len_space_right max prod.collapse)
      then show ?thesis using right_geq Abs_real_int_inverse len_v1 left by linarith
    qed
  qed
qed
  
lemma len_view_hchop_left: "len v ts c = ext v \<and> (v=v1\<parallel>v2) \<longrightarrow> len v1 ts c = ext v1"
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
  proof (cases "(left ((space ts v2) c) > right (ext v2))")  
    case True
    then have len_v2_empty:"len v2 ts c = Abs_real_int (right (ext v2),right (ext v2))"
      using len_def by auto      
    from True have "left (space ts v c) > right (ext v2)" 
      by (metis (no_types, lifting) assm hchop_def space_eq)
    then have "left (space ts v c) > right (ext v)" using assm 
      using r2 by auto 
    then have len_v_empty:"len v ts c = Abs_real_int(right (ext v), right (ext v))" using len_def by auto
    then have "left (ext v) = right (ext v)" using assm Abs_real_int_inverse 
      using hchop_def real_int.rchop_def
      by (metis (no_types, hide_lams) left.rep_eq right.rep_eq  Rep_real_int_inverse prod.collapse real_int.chop_singleton_right)
    then have "left (ext v2) = right (ext v2)" 
      using len_v_empty len_v2_empty assm l2 r2 l3 by auto
    then show "left ((len v2 ts) c) = left (ext v2)" using Abs_real_int_inverse 
      by (simp add: len_v2_empty)
  next
    case False
    then have leq:"left (space ts v2 c) \<le> right (ext v2)" by simp
    show "left ((len v2 ts) c) = left (ext v2)"
    proof (cases "right (space ts v2 c) < left (ext v2)")
      case True
      then have len_v2_empty:"len v2 ts c = Abs_real_int (left (ext v2), left (ext v2))" using leq len_def by auto
      then show ?thesis using len_v2_empty Abs_real_int_inverse by auto
    next
      case False
      then have geq:"right (space ts v2 c) \<ge> left (ext v2)" by auto
      have owners:"own v2 = own v" using assm hchop_def by auto
      have space:"space ts v2 c = space ts v c" using assm hchop_def space_eq by metis         
      then have right_geq:"left(space ts v2 c) \<le> left(ext v2)" using assm Abs_real_int_inverse 
        by (metis (no_types, hide_lams) l2 le_less_trans len_space_left leq not_less r2)
      then have max:"max (left (ext v2)) (left ((space ts v2) c)) = left (ext v2)" 
        by auto
      from leq and geq have len_v2:"len v2 ts c = Abs_real_int (max (left (ext v2)) (left ((space ts v2) c)), min (right (ext v2)) (right ((space ts v2) c)))" 
        using len_def by auto
      then have left:"left (len v2 ts c) = max (left (ext v2)) (left ((space ts v2) c))" 
        by (smt Rep_real_int_inverse left.rep_eq right.rep_eq geq l2 len_space_right max prod.collapse r3 space)
      then show ?thesis using right_geq Abs_real_int_inverse len_v2 left by linarith
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
  proof (cases "(left ((space ts v2) c) > right (ext v2))")
    case True
    then have "len v2 ts c = Abs_real_int (right (ext v2),right (ext v2))"
      using len_def by auto      
    then show "right ((len v2 ts) c) = right (ext v2)" using Abs_real_int_inverse by simp
  next
    case False
    then have leq:"left (space ts v2 c) \<le> right (ext v2)" by simp
    show "right ((len v2 ts) c) = right (ext v2)"
    proof (cases "right (space ts v2 c) < left (ext v2)")
      case True
      then have len_v2_empty:"len v2 ts c = Abs_real_int (left (ext v2), left (ext v2))" using leq len_def by auto
      from True have "right (space ts v c) < left (ext v2)" 
        by (metis (no_types, lifting) assm hchop_def space_eq)
      then have "right (space ts v c) < left (ext v)" 
        by (smt l2 len_space_right r2 r3)
      then have len_v_empty:"len v ts c = Abs_real_int (left (ext v), left (ext v))" using leq len_def 
        by (meson le_less_trans less_trans h_chop_middle1 horizontal_chop_empty_right order.asym space_nonempty)
      then have "left (ext v) = right (ext v)" using assm Abs_real_int_inverse 
        using hchop_def real_int.rchop_def by auto
      then have "left (ext v2) = right (ext v2)" 
        using len_v_empty len_v2_empty assm l2 r2 r3 
        by (smt less_eq_view_ext_def less_le_trans less_real_int_def horizontal_chop_leq2)
      then show ?thesis using len_v2_empty Abs_real_int_inverse by auto
    next
      case False
      then have geq:"right (space ts v2 c) \<ge> left (ext v2)" by auto
      have owners:"own v2 = own v" using assm hchop_def by auto
      have space:"space ts v2 c = space ts v c" using assm hchop_def space_eq by metis         
      then have right_geq:"right(space ts v2 c) \<ge> right(ext v2)" using assm Abs_real_int_inverse 
        by (smt False len_space_right less_eq_real_int_def less_eq_view_ext_def horizontal_chop_leq2) 
      then have min:"min (right (ext v2)) (right ((space ts v2) c)) = right (ext v2)" 
        by auto
      from leq and geq have len_v2:"len v2 ts c = Abs_real_int (max (left (ext v2)) (left ((space ts v2) c)), min (right (ext v2)) (right ((space ts v2) c)))" 
        using len_def by auto
      then have right:"right (len v2 ts c) = min (right (ext v2)) (right ((space ts v2) c))" 
        by (smt Rep_real_int_inverse left.rep_eq right.rep_eq assm len_hchop_right_left_border len_space_left leq min prod.collapse) 
      then show ?thesis using right_geq Abs_real_int_inverse len_v2 right by linarith
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
  from assm have right_v1':"right(len v1 ts c) = right (ext v1)" by auto    
  from assm have left_v2:"left (len v2 ( ts) c) = right (ext v1)" 
    using right_v1 by auto
  from assm have left_v2': "left(len v2 ts c) = left (ext v2)" by auto    
  from assm have right_v2:"right (len v2 ( ts) c) = right (ext v2)" by auto
  show "(len v ( ts) c = ext v)" 
  proof (cases "(left ((space ts v) c) > right (ext v))")
    case True
    then have len_v_empty:"len v ts c = Abs_real_int(right (ext v), right (ext v))" using len_def by auto
    from True have space_left1:"left (space ts v1 c) > right (ext v1)" 
      by (metis (no_types, hide_lams) assm le_less_trans left_v2  h_chop_middle2 hchop_def space_eq)
    from True have space_left2:"left (space ts v2 c) > right (ext v2)" 
      by (metis (no_types, hide_lams) assm left_v2 len_space_left horizontal_chop_own_trans not_less space_def space_left1) 
    from space_left1 have len_v1_empty:"len v1 ts c = Abs_real_int(right (ext v1), right (ext v1))" using len_def
      by auto
    from space_left2 have len_v2_empty:"len v2 ts c = Abs_real_int(right (ext v2), right (ext v2))" using len_def
      by auto
    from len_v1_empty have v1_empty:"left (ext v1) = right (ext v1)" using left_v1 right_v1' Abs_real_int_inverse by simp 
    from len_v2_empty have v2_empty:"left (ext v2) = right (ext v2)" using left_v2' right_v2 Abs_real_int_inverse by simp 
    from v1_empty and v2_empty have "left (ext v) = right (ext v)" using assm hchop_def 
      by (simp add: real_int.rchop_def) 
    then show ?thesis using len_v_empty  
      by (metis Rep_real_int_inverse prod.collapse left.rep_eq right.rep_eq)
  next
    case False
    then have leq:"(left ((space ts v) c) \<le> right (ext v))" by auto
    show "(len v ( ts) c = ext v)"
    proof (cases "right (space ts v c) < left (ext v)")
      case True
      then have len_v_empty:"len v ts c = Abs_real_int(left (ext v), left (ext v))" using leq len_def by auto
      from assm have space_v1:"space ts v c = space ts v1 c" using space_eq 
        using hchop_def by blast   
      from assm have space_v2:"space ts v c = space ts v2 c" using space_eq 
        using hchop_def by blast   
      from assm have left_v1_eq:"left (ext v1 ) = left (ext v)" using hchop_def 
        by (simp add: real_int.rchop_def)
      from assm have left_v2_geq:"left (ext v2 ) \<ge> left (ext v)" using hchop_def 
        using left_v2 h_chop_middle1 by metis
      from True have space_right1:"right (space ts v1 c) < left (ext v1)" using left_v1_eq space_v1
        by auto
      from True have space_right2:"right (space ts v2 c) < left (ext v2)" using left_v2_geq space_v2
        by auto
      from space_right1 have len_v1_empty:"len v1 ts c = Abs_real_int(left (ext v1), left (ext v1))" using leq len_def
      proof -
        have "left (space ts v1 c) < left (ext v1)"
          by (meson less_imp_le less_le_trans space_nonempty space_right1)
        then show ?thesis
          using assm left_v1_eq left_v2 left_v2_geq len_def space_right1 by force
      qed
      from space_right2 have len_v2_empty:"len v2 ts c = Abs_real_int(left (ext v2), left (ext v2))" using leq len_def
      proof -
        have "left (space ts v2 c) < left (ext v2)"
          by (meson less_imp_le less_le_trans space_nonempty space_right2)
        then show ?thesis
          using assm left_v1_eq left_v2 left_v2_geq len_def space_right2 
          by (meson le_less_trans order.asym real_int.left_leq_right)
      qed
      from len_v1_empty have v1_empty:"left (ext v1) = right (ext v1)" using left_v1 right_v1' Abs_real_int_inverse by simp 
      from len_v2_empty have v2_empty:"left (ext v2) = right (ext v2)" using left_v2' right_v2 Abs_real_int_inverse by simp 
      from v1_empty and v2_empty have "left (ext v) = right (ext v)" using assm hchop_def 
        by (simp add: real_int.rchop_def) 
      then show ?thesis using len_v_empty  
        by (metis Rep_real_int_inverse prod.collapse left.rep_eq right.rep_eq)
    next
      case False 
      then have geq:"right (space ts v c) \<ge> left (ext v)" by auto
      then have len_v:"len v ts c = (Abs_real_int ((max (left (ext v)) (left ((space ts v) c))), min (right (ext v)) (right ((space ts v) c))))"
        using leq geq len_def by auto
      have geq1:"right (space ts v1 c) \<ge> left (ext v1)" using assm hchop_def 
        by (metis (no_types, lifting) geq real_int.rchop_def space_eq)
      have leq2:"left (space ts v2 c) \<le> right (ext v2)" using assm hchop_def 
        by (metis (no_types, lifting) leq real_int.rchop_def space_eq)
      have leq1:"left (space ts v1 c) \<le> right (ext v1)" using assm hchop_def 
        by (metis (no_types, lifting) left_v2 len_space_left leq2 space_eq)         
      have geq2:"right (space ts v2 c) \<ge> left (ext v2)" using assm hchop_def 
        by (metis (no_types, lifting) geq1 left_v2 len_space_right space_eq) 
      from geq1 and leq1 have len_v1:"len v1 ts c = (Abs_real_int ((max (left (ext v1)) (left ((space ts v1) c))), min (right (ext v1)) (right ((space ts v1) c))))"
        using len_def by auto
      from geq2 and leq2 have len_v2:"len v2 ts c = (Abs_real_int ((max (left (ext v2)) (left ((space ts v2) c))), min (right (ext v2)) (right ((space ts v2) c))))"
        using len_def by auto
      from len_v1 and assm have max1:"max (left (ext v1)) (left ((space ts v1) c)) = left (ext v1)" 
        using len_space_left leq1 by force 
      have left_v:"left(ext v) = left (ext v1)"
        using assm hchop_def real_int.rchop_def by blast
      have left_space:"left (space ts v1 c) = left (space ts v c)"
        using assm hchop_def space_eq by metis         
      from left_v and left_space and max1 have max:"max (left (ext v)) (left ((space ts v) c)) = left (ext v)"
        by metis
      from len_v2 and assm have min2:"min (right (ext v2)) (right ((space ts v2) c)) = right (ext v2)" 
        using len_space_right geq2 by force 
      have right_v:"right(ext v) = right (ext v2)"
        using assm hchop_def real_int.rchop_def by simp
      have right_space:"right (space ts v2 c) = right (space ts v c)"
        using assm hchop_def space_eq by metis         
      from right_v and right_space and min2 have min:"min (right (ext v)) (right ((space ts v) c)) = right (ext v)"
        by metis
      show ?thesis using len_v min max Rep_real_int_inverse by auto       
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
  
lemma len_stable_down:"(v=v1--v2) \<longrightarrow> len v ( ts) c = len v1 ( ts) c"
proof
  assume assm:"v=v1--v2"
  then have ext_eq1:"ext v = ext v1" using vchop_def by blast
  show "len v ( ts) c = len v1 ( ts) c" 
  proof (cases " left ((space ts v) c) \<le> right (ext v)")
    assume outside_right:" \<not> left ((space ts v) c) \<le> right (ext v)"
    show "len v ( ts) c = len v1 ( ts) c" 
      using  ext_eq1 len_def outside_right vchop_def assm space_def by auto
  next
    assume inside_right:"left ((space ts v) c) \<le> right (ext v)"
    show "len v ( ts) c = len v1 ( ts) c" 
    proof (cases " right ((space ts v) c) \<ge> left (ext v)")
      assume outside_left:"\<not>right ((space ts v) c) \<ge> left (ext v)"
      show "len v ( ts) c = len v1 ( ts) c" 
        using  ext_eq1 len_def outside_left vchop_def assm space_def by auto 
    next
      assume inside_left :" right ((space ts v) c) \<ge> left (ext v)"
      show "len v ( ts) c = len v1 ( ts) c" 
        using  ext_eq1 inside_left inside_right len_def vchop_def assm space_def by auto
    qed
  qed
qed
  
lemma len_stable_up:"(v=v1--v2) \<longrightarrow> len v ( ts) c = len v2 ( ts) c"
proof
  assume assm:"v=v1--v2"
  then have ext_eq1:"ext v = ext v2" using vchop_def by blast
  show "len v ( ts) c = len v2 ( ts) c" 
  proof (cases " left ((space ts v) c) \<le> right (ext v)")
    assume outside_right:" \<not> left ((space ts v) c) \<le> right (ext v)"
    show "len v ( ts) c = len v2 ( ts) c" 
      using  ext_eq1 len_def outside_right vchop_def assm space_def by auto
  next
    assume inside_right:"left ((space ts v) c) \<le> right (ext v)"
    show "len v ( ts) c = len v2 ( ts) c" 
    proof (cases " right ((space ts v) c) \<ge> left (ext v)")
      assume outside_left:"\<not>right ((space ts v) c) \<ge> left (ext v)"
      show "len v ( ts) c = len v2 ( ts) c" 
        using  ext_eq1 len_def outside_left vchop_def assm space_def by auto 
    next
      assume inside_left :" right ((space ts v) c) \<ge> left (ext v)"
      show "len v ( ts) c = len v2 ( ts) c" 
        using  ext_eq1 inside_left inside_right len_def vchop_def assm space_def by auto
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
      using Abs_real_int_inverse assm fst_conv hchop_def len_def real_int.length_zero_iff_borders_eq mem_Collect_eq snd_conv space_def 
      by auto
  next
    assume left_inside_v1:"\<not>left ((space ts v) c) > right (ext v1)"
    show "\<parallel>len v1 ( ts) c\<parallel> = 0" 
    proof (cases "left (ext v1) > right ((space ts v) c)")
      assume right_outside_v1:"left (ext v1) > right ((space ts v) c)" 
      thus "\<parallel>len v1 (ts) c\<parallel> = 0" 
        using   real_int.rchop_def Abs_real_int_inverse assm fst_conv hchop_def len_def real_int.length_zero_iff_borders_eq mem_Collect_eq snd_conv space_def
        by auto
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
      hence len_v_empty: "(max (left (ext v)) (left ((space ts v) c))) = min (right (ext v)) (right ((space ts v) c))"
        by (smt Abs_real_int_inverse Rep_real_int_inverse left.rep_eq right.rep_eq fst_conv inside_v len_v_borders mem_Collect_eq prod_eq_iff snd_conv)
      have left_len_eq:"(max (left (ext v)) (left ((space ts v) c))) = max (left (ext v1)) (left ((space ts v) c))"
        using assm hchop_def real_int.rchop_def by auto
      have right_len_leq:"min (right (ext v)) (right ((space ts v) c)) \<ge> min (right (ext v1)) (right ((space ts v) c))"
        by (smt assm h_chop_middle2 hchop_def real_int.rchop_def)
      hence left_geq_right:"max (left (ext v1)) (left ((space ts v) c))\<ge> min (right (ext v1)) (right ((space ts v) c))"
        using left_len_eq len_v_empty by auto
      thus "\<parallel>len v1 ( ts) c\<parallel> = 0" 
        by (smt assm left_inside_v1 left_len_eq len_v len_v1 left.rep_eq right.rep_eq len_v_empty real_int.length_def real_int.length_ge_zero)
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
      hence len_v_empty: "(max (left (ext v)) (left ((space ts v) c))) = min (right (ext v)) (right ((space ts v) c))"
        by (smt Abs_real_int_inverse Rep_real_int_inverse left.rep_eq right.rep_eq fst_conv inside_v len_v_borders mem_Collect_eq prod_eq_iff snd_conv)
      have left_len_eq:"(max (left (ext v)) (left ((space ts v) c))) \<le> max (left (ext v2)) (left ((space ts v) c))"
        by (smt assm h_chop_middle1 h_chop_middle2 hchop_def len_v_empty real_int.rchop_def right_inside_v2)
      have right_len_leq:"min (right (ext v)) (right ((space ts v) c)) = min (right (ext v2)) (right ((space ts v) c))"
        by (smt assm h_chop_middle2 hchop_def real_int.rchop_def)
      hence left_geq_right:"max (left (ext v2)) (left ((space ts v) c)) \<ge> min (right (ext v2)) (right ((space ts v) c))"
        using left_len_eq len_v_empty by auto
      thus "\<parallel>len v2 ( ts) c\<parallel> = 0" 
        by (smt assm len_v len_v2 len_v_empty real_int.length_def left.rep_eq right.rep_eq real_int.length_ge_zero right_inside_v2 right_len_leq)
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
          by (meson imperfect_sensors.space_nonempty inside_right less_trans min_less_iff_disj min_less_v1 order.asym)
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
            by (meson imperfect_sensors.space_nonempty inside_left less_max_iff_disj less_trans max_geq_v1 order.asym)
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
  
lemma len_empty_subview:"\<parallel>len v ts c\<parallel> = 0 \<and> (v' \<le> v) \<longrightarrow> \<parallel>len v' ts c\<parallel> = 0"
proof
  assume assm:"\<parallel>len v ts c\<parallel> = 0 \<and> (v' \<le> v)"
  hence "\<exists>v1 v2 v3 vl vr vu vd. (v=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v'--vu)" using
      somewhere_leq by blast
  from this obtain v1 v2 v3 vl vr vu vd where views:"(v=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v'--vu)" by blast
  have "\<parallel>len v1 ts c\<parallel> = 0" using views assm len_empty_on_subview2 by blast
  hence "\<parallel>len v2 ts c\<parallel> = 0" using views len_empty_on_subview1 by blast
  hence "\<parallel>len v3 ts c \<parallel> = 0" using views len_stable_up by auto
  thus "\<parallel>len v' ts c \<parallel> = 0" using views len_stable_down by auto
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
        assume less:"right ((space ts v) c) < left (ext v)"
        then have "left (space ts v c) < right (ext v)" using assm len_left 
          by (meson le_less_trans not_le real_int.left_leq_right)
        then have "len v ts c = Abs_real_int(left (ext v), left (ext v))" using less len_def by auto  
        thus False 
          using Abs_real_int_inverse assm len_def real_int.length_def space_def by simp
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
    have 1:" (v=v1\<parallel>v2) \<and> (v2=v'\<parallel>v3)"  using inside hchop_def real_int.rchop_def   Abs_real_int_inverse real_int.left_leq_right v1 v2 v' v3 
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
      using space_eq assm by (metis (no_types, lifting) "1" hchop_def inside')
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
  
lemma ext_eq_len_eq:"ext v = ext v' \<and> own v = own v' \<longrightarrow> len v ( ts) c = len v' ( ts) c"
proof
  assume assm:"ext v = ext v' \<and> own v = own v'"
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
      from outside_left and outside_left' show ?thesis 
        by (simp add: assm len_def space_def)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v') > right ((space ts v) c) " using left_eq by simp
      from inside_left inside_right inside_left' inside_right' left_eq right_eq
      show ?thesis by (simp add: len_def sp)
    qed
  qed
qed
  
lemma view_leq_len_leq:"(ext v \<le> ext v') \<and> (own v = own v') \<and> \<parallel>len v ts c\<parallel> > 0 \<longrightarrow> len v ts c \<le> len v' ts c"
proof
  assume assm:"(ext v \<le> ext v') \<and> (own v = own v') \<and> \<parallel>len v ts c\<parallel> > 0"
  hence sp:"space ts v c = space ts v' c" by (simp add: sensors_def space_def)
  have left_eq:"left (ext v) \<ge> left (ext v')" using assm less_eq_real_int_def by simp
  have right_eq:"right (ext v) \<le> right (ext v')" using assm less_eq_real_int_def by simp
  show "len v ( ts) c \<le> len v' ( ts) c"   
  proof (cases "left ((space ts v') c) > right (ext v')")
    assume outside_right:"left ((space ts v') c) > right (ext v')"
    hence outside_right':"left ((space ts v') c) > right (ext v)" using right_eq by simp
    have False using  assm  real_int.length_def  len_non_empty_inside outside_right' space_def by fastforce
    thus ?thesis by best
  next
    assume inside_right:"\<not> left ((space ts v') c) > right (ext v')"
    have inside_right':"\<not> left ((space ts v') c) > right (ext v)"
    proof (rule ccontr)
      assume "\<not>\<not> left ((space ts v') c) > right (ext v)"
      hence " left ((space ts v') c) > right (ext v)" by blast
      thus False using assm real_int.length_def len_non_empty_inside space_def by fastforce
    qed
    show "len v ( ts) c \<le> len v' ( ts) c"
    proof (cases " left (ext v') > right ((space ts v') c) ")
      assume outside_left:" left (ext v') > right ((space ts v') c) "
      hence outside_left':"left (ext v) > right ((space ts v') c)" using left_eq by simp
      have False using assm real_int.length_def len_non_empty_inside outside_left' space_def by fastforce
      thus ?thesis by best
    next
      assume inside_left:"\<not>left (ext v') > right ((space ts v') c) "
      have inside_left':"\<not>left (ext v) > right ((space ts v')c )"
      proof (rule ccontr)
        assume "\<not>\<not>left (ext v) > right ((space ts v')c )" 
        hence "left (ext v) > right ((space ts v')c )" by blast
        thus False using assm real_int.length_def len_non_empty_inside space_def by fastforce
      qed    
      have max:"max (left (ext v)) (left ((space ts v ) c)) \<ge> max (left (ext v')) (left ((space ts v ) c))"
        using inside_left inside_right inside_left' inside_right' left_eq right_eq len_def sp by fastforce
      have min:"min (right (ext v)) (right ((space ts v ) c)) \<le> min (right (ext v')) (right ((space ts v ) c))"
        using inside_left inside_right inside_left' inside_right' left_eq right_eq len_def sp by fastforce
      have "max (left (ext v)) (left ((space ts v' ) c))\<le> min (right (ext v)) (right ((space ts v' ) c))"
        using assm inside_left' inside_right' space_nonempty sp  real_int.left_leq_right by auto
      hence len_v_in_type:"(max (left (ext v)) (left ((space ts v' ) c)), min (right (ext v)) (right ((space ts v' ) c)))
          \<in> {r::(real*real) . fst r \<le> snd r}" by auto
      have len_v'_in_type:"(max (left (ext v')) (left ((space ts v' ) c)), min (right (ext v')) (right ((space ts v' ) c)))
          \<in> {r::(real*real) . fst r \<le> snd r}" using max min real_int.left_leq_right inside_left inside_right 
        by auto
      show ?thesis using min max inside_left inside_left' inside_right inside_right' len_def sp 
          real_int.left_leq_right len_v_in_type Abs_real_int_inverse  len_v'_in_type less_eq_real_int_def
        by auto
    qed
  qed
qed
  
  
lemma create_reservation_length_stable:"(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c"   by (simp add: create_reservation_def sensors_def space_def)
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
  hence eq:"space ts v c = space ts' v c" by (simp add: withdraw_reservation_def sensors_def space_def)
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
      case True
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from True and outside_left' show ?thesis 
        by (simp add: len_def eq)
    next
      case False
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from False inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: len_def)
    qed
  qed
qed
  
end
end