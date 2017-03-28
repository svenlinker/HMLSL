theory Sensors_p
  imports "../Abstract_Model" "../Views"
begin 
  
locale perfect_sensors = traffic + view
begin
  
definition sensors::"cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
  where "sensors e ts c \<equiv> physical_size ts c + braking_distance ts c " 
    
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
  
lemma space_eq: "space ts v c = space ts v' c" using space_def sensors_def by auto

end
end