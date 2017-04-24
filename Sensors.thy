(*  Title:     Sensors.thy
    Author:     Sven Linker

Defines perfect sensors for cars. Cars can perceive both
the physical size and braking distance of all other cars.
*)

section\<open> Sensors for Cars\<close>
  
theory Sensors
  imports "Traffic" "Views"
begin 
locale sensors = traffic + view +
  fixes sensors::"(cars) \<Rightarrow> traffic \<Rightarrow> (cars) \<Rightarrow> real" 
  assumes sensors_ge:"(sensors e ts c) > 0"
begin
  
definition space ::" traffic \<Rightarrow> view \<Rightarrow> cars \<Rightarrow> real_int"
  where "space ts v c \<equiv> Abs_real_int (pos ts c, pos ts c + sensors (own v) ts c)"
    
lemma left_space: "left (space ts v c) = pos ts c" 
proof -
  have 1:"pos ts c < pos ts c + sensors (own v) ts c" using sensors_ge  
    by (metis (no_types, hide_lams)  less_add_same_cancel1  )
  show "left (space ts v c ) = pos ts c" using space_def Abs_real_int_inverse 1 by simp 
qed
  
lemma right_space: "right (space ts v c) =   pos ts c + sensors (own v) ts c"
proof - 
  have 1:"pos ts c < pos ts c + sensors (own v) ts c" using sensors_ge  
    by (metis (no_types, hide_lams)  less_add_same_cancel1  )
  show 3:"right(space ts v c ) = pos ts c + sensors (own v) ts c" using space_def Abs_real_int_inverse 1 by simp
qed
  
lemma space_nonempty:"left (space ts v c ) < right (space ts v c)" 
  using left_space right_space sensors_ge by simp
    
    
end
end