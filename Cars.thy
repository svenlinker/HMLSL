(*  Title:      Cars.thy
    Author:     Sven Linker

A countably infinite type to denote cars in the model of HMLSL.
Also defines type synonyms for lanes and extension of views and traffic snapshots.
*)

section\<open>Cars\<close>

theory Cars
imports RealInt NatInt
begin

type_synonym lanes = nat_int
type_synonym extension = real_int

axiomatization car_constructor::"nat \<Rightarrow> nat"
where car_constructor_inject:" car_constructor x = car_constructor y \<Longrightarrow> x = y" 
and car_constructor_zero:" car_constructor (Suc x) \<noteq> car_constructor 0"

typedef cars = "{c . \<exists>n. (car_constructor n) = c}"
by auto

lemma at_least_two_cars_exists:"\<exists>c d ::cars . c \<noteq>d" 
proof -
  have "car_constructor 0 \<noteq> car_constructor 1" using car_constructor_inject by auto
  hence "Abs_cars (car_constructor 0) \<noteq> Abs_cars (car_constructor 1)" 
    by (metis (mono_tags, lifting) Abs_cars_inverse mem_Collect_eq)
  thus ?thesis by blast
qed

notation inf (infix "\<sqinter>" 70)
(*notation nat_int.empty ("\<emptyset>")
notation nat_int.subseteq  (infix "\<sqsubseteq>" 30)
notation nat_int.union (infix "\<squnion>" 65)
notation nat_int.maximum ("maximum _")
notation nat_int.minimum  ("minimum _")
notation nat_int.consec ("consec _ _") 
notation nat_int.el (infix " \<^bold>\<in> " 40)
notation nat_int.not_in (infix "\<^bold>\<notin>" 40) *)
  
notation RealInt.real_int.shift (" shift _ _")
  
(*notation nat_int.card' ("|_|" 70)*)
notation RealInt.real_int.length ("\<parallel>_\<parallel>" 70)
  
(*notation NatInt.nat_int.N_Chop ("N'_Chop'(_,_,_')")*)
notation RealInt.real_int.R_Chop ("R'_Chop'(_,_,_')")  

  
  
  
end