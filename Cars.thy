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
end