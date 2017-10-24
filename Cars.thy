(*  Title:      Cars.thy
    Author:     Sven Linker

A countably infinite type to denote cars in the model of HMLSL.
Also defines type synonyms for lanes and extension of views and traffic snapshots.
*)

section\<open>Cars\<close>

theory Cars
  imports Main
begin


typedef cars = "{n. (is_nat n)} " 
  using Nat_Transfer.transfer_int_nat_function_closures(9) by auto

locale cars 
begin

lemma at_least_two_cars_exists:"\<exists>c d ::cars . c \<noteq>d" 
proof -
  have "(0::int) \<noteq> 1" by simp
  then have "Abs_cars (0::int) \<noteq> Abs_cars(1) " 
    by (metis Abs_cars_inverse Nat_Transfer.transfer_int_nat_function_closures(9) Nat_Transfer.transfer_nat_int_function_closures(6) int_nat_eq mem_Collect_eq)
  thus ?thesis by blast
qed
  
end
end