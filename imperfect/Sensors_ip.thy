(*  Title:      imperfect/Sensors_ip.thy
    Author:     Sven Linker

Defines imperfect sensors for cars. Cars can  perceive 
the physical size and braking distance of themselves, but
only the physical size of all other cars.
*)

section\<open>Imperfect Sensors for Cars\<close>
theory Sensors_ip
imports "../Traffic" "../Views"
begin 

    
locale imperfect_sensors = traffic + view
begin
print_locale! imperfect_sensors
definition sensors::"cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
where "sensors e ts c \<equiv> if (e = c) then physical_size ts c + braking_distance ts c 
                                    else physical_size ts c " 

definition space ::" traffic \<Rightarrow> view \<Rightarrow> cars \<Rightarrow> real_int"
where "space ts v c \<equiv> Abs_real_int (pos ts c, pos ts c + sensors (own v) ts c)"

lemma space_nonempty:"left (space ts v c ) < right (space ts v c)" 
  proof -
  have 1:"pos ts c < pos ts c + sensors (own v) ts c" using sensors_def psGeZero sdGeZero 
    by (metis (no_types, hide_lams) le_less_trans less_add_same_cancel1 not_less order.asym)
  have 2:"left (space ts v c ) = pos ts c" using space_def Abs_real_int_inverse 1 by simp 
  have 3:"right(space ts v c ) = pos ts c + sensors (own v) ts c" using space_def Abs_real_int_inverse 1 by simp
  from 2 and 3 show ?thesis using 1 by auto
qed


lemma sensors_ge_zero:"sensors e ts c > 0"
proof (cases "e=c")
  case False
  then show ?thesis using sensors_def psGeZero by auto
next
  case True  
  have ps:"physical_size ts c > 0" using psGeZero by auto
  have sd:"braking_distance ts c > 0" using sdGeZero by auto
  have "physical_size ts c + braking_distance ts c > 0" using ps sd by auto
  then show ?thesis using sensors_def 
    by (simp add: ps)
qed      
      
lemma sensors_le:"e \<noteq> c \<longrightarrow> sensors e ts c < sensors c ts c"
using sensors_def by (simp add: sdGeZero)

  
lemma sensors_leq:" sensors e ts c \<le> sensors c ts c"
using sensors_def using sensors_le sdGeZero psGeZero 
by smt

lemma left_space:"left (space ts v c) =  pos ts c"  
proof -
  have cond:"\<And>l r. Rep_real_int (Abs_real_int (l, r)) = (l, r) \<or> r < l"
    using Abs_real_int_inverse by force
  have "pos ts c < pos ts c + sensors (own v) ts c" 
    using imperfect_sensors.sensors_ge_zero by auto
  then show ?thesis 
    by (metis (no_types) cond add.right_neutral add_less_cancel_left  left.rep_eq fst_conv  imperfect_sensors.space_def order.asym )
qed

lemma right_space:"right (space ts v c) =  pos ts c + sensors (own v) ts c"  
proof -
  have cond:"\<And>l r. Rep_real_int (Abs_real_int (l, r)) = (l, r) \<or> r < l"
    using Abs_real_int_inverse by force
  have non_e:"pos ts c < pos ts c + sensors (own v) ts c" 
    using imperfect_sensors.sensors_ge_zero by auto
  then show ?thesis using non_e cond space_def 
  proof -
    have "Rep_real_int (Abs_real_int (pos ts c, pos ts c + sensors (own v) ts c)) = (pos ts c, pos ts c + sensors (own v) ts c)"
      using non_e cond by fastforce
    then show ?thesis
      by (simp add: imperfect_sensors.space_def)
  qed
qed
  
  
lemma space_eq: "own v = own v' \<longrightarrow> space ts v c = space ts v' c" using space_def sensors_def by auto
  
lemma switch_space_le:"(own v) \<noteq> c \<and> (v=c>v') \<longrightarrow> space ts v c < space ts v' c" 
proof
  assume assm:"(own v) \<noteq> c \<and> (v=c>v')"
  hence sens:"sensors (own v) ts c < sensors (own v') ts c" using sensors_le switch_def by auto
  then have le:"pos ts c + sensors (own v) ts c < pos ts c + sensors (own v') ts c" by auto     
  have left_eq:"left (space ts v c) = left (space ts v' c)" using left_space by auto 
  have r1:"right (space ts v c ) = pos ts c + sensors (own v) ts c" 
    using imperfect_sensors.right_space by auto      
  have r2:"right (space ts v' c ) = pos ts c + sensors (own v') ts c" 
    using imperfect_sensors.right_space by auto      
  then have "right (space ts v c) < right( space ts v' c)" using r1 r2 le by auto 
      
  then have "((left (space ts v' c)) \<ge> left (space ts v c) ) \<and> ((right (space ts v c) \<le> right( space ts v' c))) 
                                  \<and>  \<not>((left (space ts v c) \<ge> left (space ts v' c) ) \<and> (right (space ts v' c) \<le> right (space ts v c)))" 
  using imperfect_sensors.left_space left_eq by auto
  then show "space ts v c < space ts v' c" using less_real_int_def 
    using left_eq by auto    
qed

lemma switch_space_leq:"(v=c>v') \<longrightarrow> space ts v c \<le> space ts v' c"
by (metis less_imp_le order_refl switch_space_le switch_refl switch_unique)
end
  
end