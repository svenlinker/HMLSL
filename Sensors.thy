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
  fixes sensors::"cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
  assumes sensors_ge:"sensors e ts c > 0"
begin
  print_theorems
    
definition space ::" traffic \<Rightarrow> view \<Rightarrow> cars \<Rightarrow> real_int"
  where "space ts v c \<equiv> Abs_real_int (pos ts c, pos ts c + sensors (own v) ts c)"
    
    
lemma space_nonempty:"left (space ts v c ) < right (space ts v c)" 
proof -
  have 1:"pos ts c < pos ts c + sensors (own v) ts c" using sensors_ge  
    by (metis (no_types, hide_lams)  less_add_same_cancel1  )
  have 2:"left (space ts v c ) = pos ts c" using space_def Abs_real_int_inverse 1 by simp 
  have 3:"right(space ts v c ) = pos ts c + sensors (own v) ts c" using space_def Abs_real_int_inverse 1 by simp
  from 2 and 3 show ?thesis using 1 by auto
qed
end
  end