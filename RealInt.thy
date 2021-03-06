(*  Title:      RealInt.thy
    Author:     Sven Linker

Closed, non-empty intervals based on real numbers. Defines functions left, right
to refer to the left (resp. right) border of an interval. 

Defines a length function as the difference between left and right border
and a function to shift an interval by a real value (i.e., the value is added
to both borders).

Instantiates "order", as a notion of sub-intervals.

Also contains a "chopping" predicate R_Chop(r,s,t): r can be divided into
sub-intervals s and t.
*)

section \<open>Closed Real-valued Intervals\<close>

text\<open>We define a type for real-valued intervals. It consists of pairs of real numbers, where
the first is lesser or equal to the second. Both endpoints are understood to be part of
the interval, i.e., the intervals are closed. This also implies that we do not
consider empty intervals. 

We define a measure on these intervals as the difference between the left and
right endpoint. In addition, we introduce a notion of shifting an interval by
a real value \(x\). Finally, an interval \(r\) can be chopped into \(s\) and
\(t\), if the left endpoint of \(r\) and \(s\) as well as the right endpoint
of \(r\) and \(t\) coincides, and if the right endpoint of \(s\) is 
the left endpoint of \(t\).
\<close>

theory RealInt
  imports HOL.Real
begin
  
typedef real_int = "{r::(real*real) . fst r \<le> snd r}"
  by auto
print_theorems
setup_lifting type_definition_real_int
print_theorems
print_quot_maps
  
lift_definition left::"real_int \<Rightarrow> real" is fst proof - qed
lift_definition right::"real_int \<Rightarrow> real" is snd proof - qed
  
lemmas[simp] = left.rep_eq right.rep_eq  
  
locale real_int
interpretation real_int_class?: real_int .

context real_int
begin
  
definition length :: "real_int \<Rightarrow> real" ("\<parallel>_\<parallel>" 70)
  where "\<parallel>r\<parallel> = right r - left r"
print_theorems

definition shift::"real_int \<Rightarrow> real \<Rightarrow> real_int" (" shift _ _")
  where "(shift r x) = Abs_real_int(left r +x, right r +x)"

definition R_Chop :: "real_int \<Rightarrow> real_int \<Rightarrow> real_int \<Rightarrow> bool" ("R'_Chop'(_,_,_')" 51)
  where rchop_def :
    "R_Chop(r,s,t) ==  left r  = left s \<and> right s = left t \<and> right r =  right t"

definition combine :: "real_int \<Rightarrow> real_int \<Rightarrow> real_int" 
  where "combine r s == Abs_real_int (left r, right s)" 

text{*Create an interval of length x starting at r  *}

definition stretch :: "real \<Rightarrow> real \<Rightarrow> real_int "
  where "stretch r x == Abs_real_int(r, r+x)" 

definition mk_empty:: "real \<Rightarrow> real_int"
  where "mk_empty x == Abs_real_int(x,x)"

(* TODO: prove properties of this definition  and use it to define length *)
definition intersect :: "real_int \<Rightarrow> real_int \<Rightarrow> real_int" 
  where "intersect r s == 
    if (left s > right r)  
      then   mk_empty (right r) 
    else
      if (right (s) < left r) 
        then  mk_empty (left r )
      else  
       Abs_real_int (max (left (r)) (left (s)), 
                      min (right (r)) (right (s)))"

end

text \<open>The intervals defined in this way allow for the definition of an order: 
the subinterval relation.\<close>
  
instantiation real_int :: order
begin
definition "less_eq_real_int r s \<equiv> (left r \<ge> left s) \<and> (right r \<le> right s)"
definition "less_real_int r s \<equiv> (left r \<ge> left s) \<and> (right r \<le> right s) 
                                  \<and>  \<not>((left s \<ge> left r) \<and> (right s \<le> right r))"
instance   
proof 
  fix r s t :: real_int
  show "(r < s) = (r \<le> s \<and> \<not> s \<le> r)" using less_eq_real_int_def less_real_int_def by auto
  show "r \<le> r" using less_eq_real_int_def by auto
  show "r \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> r \<le> t" using less_eq_real_int_def by auto
  show "r \<le> s \<Longrightarrow> s \<le> r \<Longrightarrow> r = s"
    by (metis Rep_real_int_inject left.rep_eq less_le less_eq_real_int_def 
        not_le prod.collapse right.rep_eq)
qed
end
  
context real_int
begin
  
lemma left_leq_right: "left r \<le> right r" 
  using Rep_real_int left.rep_eq right.rep_eq by auto

lemma left_right_eq: "r = s \<longleftrightarrow> left r = left s \<and> right r = right s" 
  by (metis Rep_real_int_inject left.rep_eq prod.expand right.rep_eq)

    
lemma length_ge_zero :" \<parallel>r\<parallel> \<ge> 0" using left_leq_right 
  by (simp add: length_def)

lemma length_leq: "t \<le> r \<longrightarrow> \<parallel>t\<parallel> \<le> \<parallel>r\<parallel> " 
  by (simp add: length_def less_eq_real_int_def)

lemma consec_add:
  "left r = left s \<and> right r = right t \<and> right s = left t \<Longrightarrow> \<parallel>r\<parallel> = \<parallel>s\<parallel> + \<parallel>t\<parallel>"
  by (simp add:length_def)
    
lemma length_zero_iff_borders_eq:"\<parallel>r\<parallel> = 0 \<longleftrightarrow> left r = right r"
  using length_def by auto



lemma shift_left_eq_right:"left (shift r x) \<le> right (shift r x)"
  using left_leq_right .
    
lemma shift_keeps_length:"\<parallel>r\<parallel> = \<parallel> shift r x\<parallel>" 
  using Abs_real_int_inverse left.rep_eq real_int.length_def length_ge_zero shift_def 
    right.rep_eq by auto
    
lemma shift_zero:"(shift r 0) = r"
  by (simp add: Rep_real_int_inverse shift_def )

lemma shift_inj: "(shift r x) = (shift s x) \<longrightarrow> r = s"  
proof
  assume 1:"(shift r x) = (shift s x)" 
  have 2:"left r + x = left s + x" 
    using "1" Abs_real_int_inject left_leq_right real_int_class.shift_def by auto
  have 3: "right r + x = right s + x" 
    using "1" Abs_real_int_inject left_leq_right real_int_class.shift_def by auto
  show "r = s" using 2 3 
    by (metis Rep_real_int_inverse add_diff_cancel_left' left.rep_eq linordered_field_class.sign_simps(27) prod.collapse right.rep_eq)
qed

lemma shift_inj_amount: "(shift r x) = (shift r y) \<longrightarrow> x = y" 
  using Abs_real_int_inject left_leq_right real_int_class.shift_def by auto


lemma shift_additivity:"(shift r (x+y)) = shift (shift r x) y" 
proof -
  have 1:"(shift r (x+y)) = Abs_real_int ((left r) +(x+y), (right r)+(x+y))"
    using shift_def by auto
  have 2:"(left r) +(x+y) \<le> (right r)+(x+y)" using left_leq_right by auto
  hence left:"left (shift r (x+y)) = (left r) +(x+y)" 
    by (simp add: Abs_real_int_inverse 1)
  from 2 have right:"right (shift r (x+y)) = (right r) +(x+y)" 
    by (simp add: Abs_real_int_inverse 1)
  have 3:"(shift (shift r x) y) = Abs_real_int(left (shift r x) +y, right(shift r x)+y)"
    using shift_def by auto
  have l1:"left (shift r x) = left r + x"
    using shift_def  Abs_real_int_inverse "2" fstI mem_Collect_eq prod.sel(2) left.rep_eq
    by auto
  have r1:"right (shift r x) = right r + x" 
    using shift_def Abs_real_int_inverse "2" fstI mem_Collect_eq prod.sel(2) right.rep_eq
    by auto
  from 3 and l1 and r1 have 
    "(shift (shift r x) y) = Abs_real_int(left  r+x+y, right  r+x+y)"
    by auto
  with 1 show ?thesis by (simp add: add.assoc)
qed

lemma stretch_left_leq_right : "left (stretch r x) \<le> right (stretch r x)" 
  using left_leq_right by auto

lemma stretch_left : "x \<ge> 0 \<longrightarrow> left (stretch r x) = r " 
  by (simp add: Abs_real_int_inverse local.stretch_def)

lemma stretch_right: "x\<ge> 0 \<longrightarrow> right (stretch r x) = r+x"
  by (simp add: Abs_real_int_inverse local.stretch_def)

lemma stretch_length: "x \<ge> 0 \<longrightarrow> \<parallel>stretch r x\<parallel> = x" 
  using stretch_left stretch_right length_def
  by (simp)

lemma empty_stretch: "mk_empty r = stretch r 0" 
  by (simp add: mk_empty_def stretch_def)

lemma empty_length: "\<parallel>mk_empty r\<parallel> = 0" 
  by (simp add: empty_stretch stretch_length)

lemma empty_left: "left (mk_empty r) = r" 
  using empty_stretch stretch_left by auto

lemma empty_right: "right (mk_empty r) = r" 
  using empty_stretch stretch_right by auto


lemma chop_combine: "R_Chop(r,s,t) \<longrightarrow> r = combine s t" 
  by (metis Rep_real_int_inverse combine_def left.rep_eq prod.collapse rchop_def right.rep_eq)

lemma combine_leq_left: "right s = left t \<longrightarrow> s \<le> combine s t"  
proof
  assume 1:"right s = left t" 
  have 2: "left s \<ge> left (combine s t)" using 1
    by (metis Rep_real_int_cases Rep_real_int_inverse left.rep_eq left_leq_right local.combine_def mem_Collect_eq order_refl order_trans prod.sel(1) prod.sel(2))
  have 3: "right s \<le> right (combine s t)" using 1 left_leq_right 
    by (metis (no_types, lifting) CollectI Rep_real_int_cases Rep_real_int_inverse combine_def  dual_order.trans left.rep_eq   prod.sel(1) prod.sel(2) right.rep_eq)
  show "s \<le> combine s t"  using 2 3 
    by (simp add: less_eq_real_int_def)
qed

lemma combine_leq_right: "right s = left t \<longrightarrow> t \<le> combine s t"  
proof
  assume 1:"right s = left t" 
  have 2: "left t \<ge> left (combine s t)" using 1
    by (metis Rep_real_int_cases Rep_real_int_inverse left.rep_eq left_leq_right local.combine_def mem_Collect_eq  order_trans prod.sel(1) prod.sel(2))
  have 3: "right t \<le> right (combine s t)" using 1 left_leq_right 
    by (metis Abs_real_int_inverse CollectI combine_def dual_order.refl order_trans prod.sel(1) prod.sel(2) right.rep_eq)
  show "t \<le> combine s t"  using 2 3 
    by (simp add: less_eq_real_int_def)
qed

lemma shift_combine_comm: "(right r = left s) \<longrightarrow> combine (shift r x) (shift s x) = shift (combine r s) x" 
proof 
  assume assm: "right r = left s" 
  have 0:"combine (shift r x) (shift s x) = Abs_real_int (left (shift r x), right (shift s x))" 
    by (simp add: combine_def)
  have 1:"left (shift r x) = left r + x" 
    using Abs_real_int_inverse left_leq_right real_int_class.shift_def by auto
  have 2:"right (shift s x) = right s + x" 
    using Abs_real_int_inverse length_def length_ge_zero real_int_class.shift_def by auto
  have 3: "left (combine r s) = left r" using combine_def assm Abs_real_int_inverse  
    by (metis fst_conv left.rep_eq left_leq_right mem_Collect_eq order_trans snd_conv)
  have 4: "right (combine r s) = right s"  using combine_def assm Abs_real_int_inverse 
    by (metis fst_conv right.rep_eq left_leq_right mem_Collect_eq order_trans snd_conv)
  have "(shift (combine r s) x) = Abs_real_int ((left (combine r s)) + x ,( right (combine r s)) + x)" 
    by (simp add: real_int_class.shift_def)
  then have "(shift (combine r s) x) = Abs_real_int ((left r + x), (right s + x))" using 3 4 
    by auto
  then have "(shift (combine r s) x) = Abs_real_int ((left (shift r x)), (right (shift s  x)))" using 1 2 
    by simp
  then show "combine (shift r x) (shift s x) = shift (combine r s) x" using 0 
    by simp
qed

lemma shift_combine:"(left t = right s) \<longrightarrow> (r = combine s t) \<longleftrightarrow> (shift r x) = combine (shift s x) (shift t x)" 
proof
  assume 1:"(left t = right s)"
   show " (r = combine s t) \<longleftrightarrow> (shift r x) = combine (shift s x)  (shift t x)"
  proof
    assume 2:"(r = combine s t)" 
    have 3:"left r = left s" using combine_def Abs_real_int_inverse Rep_real_int 2 
      by (metis "1" fst_conv left.rep_eq left_leq_right mem_Collect_eq order_trans snd_conv)
    have 4: "right r = right t" 
      by (metis "1" "2" Rep_real_int_cases Rep_real_int_inverse left_leq_right local.combine_def mem_Collect_eq order_trans prod.sel(1) prod.sel(2) right.rep_eq)
    show  "(shift r x) = combine (shift s x) (shift t x)" using 3 4 
      using Abs_real_int_inverse combine_def length_def length_ge_zero real_int_class.shift_def by auto
  next
    assume 2:"(shift r x) = combine (shift s x) (shift t x)"
    have "combine (shift s x) (shift t x) = shift (combine s t) x" using shift_combine_comm 1 by auto
    then show "r=combine s t" 
      using "2" shift_inj by auto
  qed
qed

lemma chop_always_possible: 
  obtains s and t where "R_Chop(r,s,t)" 
proof -
  obtain s where l:"left r \<le> s  \<and> s \<le> right r" 
    using left_leq_right by auto
  obtain x1  where x1_def:"x1 = Abs_real_int(left r,s)"  by simp
  obtain x2 where x2_def:"x2 = Abs_real_int(s, right r)" by simp
  have x1_in_type:"(left r, s) \<in> {r :: real*real . fst r \<le> snd r }" using l by auto 
  have x2_in_type:"(s, right r) \<in> {r :: real*real . fst r \<le> snd r }" using l by auto 
  have 1:"left r = left x1" using x1_in_type l Abs_real_int_inverse 
    by (simp add:  x1_def)
  have 2:"right x1 = s" 
    using Abs_real_int_inverse x1_def x1_in_type right.rep_eq by auto
  have 3:"right x1 = left x2" 
    using Abs_real_int_inverse x1_def x1_in_type x2_def x2_in_type left.rep_eq by auto
  from 1 and 2 and 3 have "R_Chop(r,x1,x2)" 
    using Abs_real_int_inverse rchop_def snd_conv x2_def x2_in_type by auto 
  then show ?thesis using that by blast
qed

lemma chop_always_possible': "\<exists> s t. R_Chop(r,s,t)" 
  using chop_always_possible by blast 
(*proof -
  fix x
  obtain s where l:"left x \<le> s  \<and> s \<le> right x" 
    using left_leq_right by auto
  obtain x1  where x1_def:"x1 = Abs_real_int(left x,s)"  by simp
  obtain x2 where x2_def:"x2 = Abs_real_int(s, right x)" by simp
  have x1_in_type:"(left x, s) \<in> {r :: real*real . fst r \<le> snd r }" using l by auto 
  have x2_in_type:"(s, right x) \<in> {r :: real*real . fst r \<le> snd r }" using l by auto 
  have 1:"left x = left x1" using x1_in_type l Abs_real_int_inverse 
    by (simp add:  x1_def)
  have 2:"right x1 = s" 
    using Abs_real_int_inverse x1_def x1_in_type right.rep_eq by auto
  have 3:"right x1 = left x2" 
    using Abs_real_int_inverse x1_def x1_in_type x2_def x2_in_type left.rep_eq by auto
  from 1 and 2 and 3 have "R_Chop(x,x1,x2)" 
    using Abs_real_int_inverse rchop_def snd_conv x2_def x2_in_type by auto 
  then show "\<exists>x1 x2. R_Chop(x,x1,x2)" by blast
qed
*)

lemma chop_singleton_right:
  obtains s where "R_Chop(r,r,s)"
proof -
  obtain y where  "y =  Abs_real_int(right r, right r)" by simp
  then have "R_Chop(r,r,y)" 
    by (simp add: Abs_real_int_inverse real_int.rchop_def)
  then show ?thesis using that by blast
qed

lemma chop_singleton_right': "\<exists> s. R_Chop(r,r,s)" 
  using chop_singleton_right by blast
(*proof -
  fix x 
  obtain y where  "y =  Abs_real_int(right x, right x)" by simp
  then have "R_Chop(x,x,y)" 
    by (simp add: Abs_real_int_inverse real_int.rchop_def)
  then show "\<exists>y. R_Chop(x,x,y)" by blast
qed
*)

lemma chop_singleton_left: 
  obtains s where "R_Chop(r,s,r)"  
proof  -
  obtain y where  "y =  Abs_real_int(left r, left r)" by simp
  then have "R_Chop(r,y,r)" 
    by (simp add: Abs_real_int_inverse real_int.rchop_def)
  then show ?thesis using that by blast
qed

lemma chop_singleton_left': "\<exists> s. R_Chop(r,s,r)"  
  using chop_singleton_left by blast
(*proof -
  fix x 
  obtain y where  "y =  Abs_real_int(left x, left x)" by simp
  then have "R_Chop(x,y,x)" 
    by (simp add: Abs_real_int_inverse real_int.rchop_def)
  then show "\<exists>y. R_Chop(x,y,x)" by blast
qed
*)
  
lemma chop_add_length:"R_Chop(r,s,t) \<Longrightarrow> \<parallel>r\<parallel> = \<parallel>s\<parallel> + \<parallel>t\<parallel>"
  using consec_add by (simp add: rchop_def)
    
lemma chop_add_length_ge_0:"R_Chop(r,s,t) \<and> \<parallel>s\<parallel> > 0 \<and> \<parallel>t\<parallel>>0 \<longrightarrow> \<parallel>r\<parallel>>0"
  using chop_add_length by auto

lemma chop_dense:
  assumes r:"\<parallel>r\<parallel> > 0" 
  obtains s and t where "R_Chop(r,s,t)" and "\<parallel>s\<parallel>> 0" and "\<parallel>t\<parallel> > 0" 
proof -
  have ff1: " left r < right r"
    using Rep_real_int \<open>0 < \<parallel>r\<parallel>\<close> length_def by auto
  have l_in_type:"(left r, right r) \<in> {r :: real*real . fst r \<le> snd r }" 
    using Rep_real_int by auto      
  obtain x where  x_def:" x  = (left r + right r) / 2" 
    by blast
  have x_gr:"x > left r" using ff1 field_less_half_sum x_def by blast
  have x_le:"x < right r" using ff1 x_def by (simp add: field_sum_of_halves)
  obtain s where s_def:"s = Abs_real_int(left r, x)"  by simp
  obtain t where t_def:"t = Abs_real_int(x, right r)"  by simp
  have s_in_type:"(left r, x) \<in> {r :: real*real . fst r \<le> snd r }" 
    using x_def x_le by auto
  have t_in_type:"(x, right r) \<in> {r :: real*real . fst r \<le> snd r }" 
    using x_def x_gr by auto
  have s_gr_0:"\<parallel>s\<parallel> > 0" 
    using Abs_real_int_inverse s_def length_def x_gr by auto
  have t_gr_0:"\<parallel>t\<parallel> > 0" 
    using Abs_real_int_inverse t_def length_def x_le by auto
  have "R_Chop(r,s,t)" 
    using Abs_real_int_inverse s_def s_in_type t_def t_in_type rchop_def by auto
  hence "R_Chop(r,s,t) \<and> \<parallel>s\<parallel>>0 \<and> \<parallel>t\<parallel>>0" 
    using s_gr_0 t_gr_0 by blast
  then show ?thesis using that by blast
qed

(*lemma chop_dense' : "\<parallel>r\<parallel> > 0 \<longrightarrow> (\<exists> s t. R_Chop(r,s,t) \<and> \<parallel>s\<parallel>>0 \<and> \<parallel>t\<parallel>>0)"
  using chop_dense by blast
*)
(*
proof
  assume "\<parallel>r\<parallel> > 0"
  have ff1: " left r < right r"
    using Rep_real_int \<open>0 < \<parallel>r\<parallel>\<close> length_def by auto
  have l_in_type:"(left r, right r) \<in> {r :: real*real . fst r \<le> snd r }" 
    using Rep_real_int by auto      
  obtain x where  x_def:" x  = (left r + right r) / 2" 
    by blast
  have x_gr:"x > left r" using ff1 field_less_half_sum x_def by blast
  have x_le:"x < right r" using ff1 x_def by (simp add: field_sum_of_halves)
  obtain s where s_def:"s = Abs_real_int(left r, x)"  by simp
  obtain t where t_def:"t = Abs_real_int(x, right r)"  by simp
  have s_in_type:"(left r, x) \<in> {r :: real*real . fst r \<le> snd r }" 
    using x_def x_le by auto
  have t_in_type:"(x, right r) \<in> {r :: real*real . fst r \<le> snd r }" 
    using x_def x_gr by auto
  have s_gr_0:"\<parallel>s\<parallel> > 0" 
    using Abs_real_int_inverse s_def length_def x_gr by auto
  have t_gr_0:"\<parallel>t\<parallel> > 0" 
    using Abs_real_int_inverse t_def length_def x_le by auto
  have "R_Chop(r,s,t)" 
    using Abs_real_int_inverse s_def s_in_type t_def t_in_type rchop_def by auto
  hence "R_Chop(r,s,t) \<and> \<parallel>s\<parallel>>0 \<and> \<parallel>t\<parallel>>0" 
    using s_gr_0 t_gr_0 by blast
  thus "\<exists> s t. R_Chop(r,s,t) \<and> \<parallel>s\<parallel>>0 \<and> \<parallel>t\<parallel>>0" by blast
qed  
*)

lemma chop_assoc1:
  "R_Chop(r,r1,r2) \<and> R_Chop(r2,r3,r4) 
     \<longrightarrow> R_Chop(r, combine r1 r3, r4) 
        \<and> R_Chop(combine r1 r3, r1,r3)"
proof
  assume assm: "R_Chop(r,r1,r2) \<and> R_Chop(r2,r3,r4)"
  have 1:"R_Chop(combine r1 r3, r1,r3)" 
    by (metis (no_types, lifting) assm  combine_def eq_onp_same_args left.abs_eq left.rep_eq left_leq_right order_trans prod.sel(1) prod.sel(2) rchop_def right.abs_eq right.rep_eq)
  have 2:" R_Chop(r, combine r1 r3, r4)" 
    using "1" assm rchop_def by fastforce
  show " R_Chop(r, combine r1 r3, r4) 
        \<and> R_Chop(combine r1 r3, r1,r3)" using 1 2 by blast
qed

(*
lemma chop_assoc1':
  "R_Chop(r,r1,r2) \<and> R_Chop(r2,r3,r4) 
     \<longrightarrow> R_Chop(r, Abs_real_int(left r1, right r3), r4) 
        \<and> R_Chop(Abs_real_int(left r1, right r3), r1,r3)"
proof 
  assume assm: "R_Chop(r,r1,r2) \<and> R_Chop(r2,r3,r4)"
  let ?y1 = " Abs_real_int(left r1, right r3)" 
  have l1:"left r1 = left ?y1" 
    by (metis  Abs_real_int_inverse assm fst_conv left.rep_eq mem_Collect_eq
        order_trans real_int.left_leq_right real_int.rchop_def snd_conv)
  have r1:"right ?y1 = right r3" 
    by (metis  Rep_real_int_cases Rep_real_int_inverse assm fst_conv mem_Collect_eq
        order_trans real_int.left_leq_right real_int.rchop_def right.rep_eq snd_conv)    
  have g1:"R_Chop(r, ?y1, r4)" using assm  rchop_def r1 l1 by simp
  have g2:"R_Chop(?y1, r1,r3)" using assm  rchop_def r1 l1 by simp
  show "R_Chop(r, ?y1, r4) \<and> R_Chop(?y1, r1,r3)" using g1 g2 by simp
qed
*)

lemma chop_assoc2: 
  "R_Chop(r,r1,r2) \<and> R_Chop(r1,r3,r4) 
    \<longrightarrow> R_Chop(r,r3,  combine  r4 r2) 
      \<and> R_Chop(combine r4 r2, r4,r2)"
proof
  assume 0:"R_Chop(r,r1,r2) \<and> R_Chop(r1,r3,r4)"
  then have 1:"R_Chop(combine r4 r2, r4,r2)" 
    by (metis (no_types, lifting) Abs_real_int_inverse left.rep_eq left_leq_right local.combine_def mem_Collect_eq order_trans prod.sel(1) prod.sel(2) rchop_def right.rep_eq)
  then have 2:"R_Chop(r,r3,  combine  r4 r2)" using 0 
    by (simp add: rchop_def)
  from 1 and 2 show " R_Chop(r,r3,  combine  r4 r2) 
      \<and> R_Chop(combine r4 r2, r4,r2)" by blast
qed

(*
lemma chop_assoc2': 
  "R_Chop(r,r1,r2) \<and> R_Chop(r1,r3,r4) 
    \<longrightarrow> R_Chop(r,r3, Abs_real_int(left r4, right r2)) 
      \<and> R_Chop(Abs_real_int(left r4, right r2), r4,r2)"
proof 
  assume assm: "R_Chop(r,r1,r2) \<and> R_Chop(r1,r3,r4)"
  let ?y1 = " Abs_real_int(left r4, right r2)" 
  have "left ?y1 \<le> right ?y1"
    using real_int.left_leq_right by blast
  have f1: "left r4 = right r3"
    using assm real_int.rchop_def by force
  then have right:"right r3 \<le> right r2"
    by (metis (no_types) assm order_trans real_int.left_leq_right real_int.rchop_def)
  then have l1:"left ?y1 = left r4" using f1 by (simp add: Abs_real_int_inverse)
  have r1:"right ?y1 = right r2" 
    using Abs_real_int_inverse right f1 by auto
  have g1:"R_Chop(r, r3, ?y1)" using assm  rchop_def r1 l1 by simp
  have g2:"R_Chop(?y1, r4,r2)" using assm  rchop_def r1 l1 by simp
  show "R_Chop(r, r3, ?y1) \<and> R_Chop(?y1, r4,r2)" using g1 g2 by simp
qed
*)

lemma chop_leq1:"R_Chop(r,s,t) \<longrightarrow> s \<le> r" 
  by (metis (full_types) less_eq_real_int_def order_refl real_int.left_leq_right real_int.rchop_def)
    
lemma chop_leq2:"R_Chop(r,s,t) \<longrightarrow> t \<le> r"
  by (metis (full_types) less_eq_real_int_def order_refl real_int.left_leq_right real_int.rchop_def)
    
lemma chop_empty1:"R_Chop(r,s,t) \<and> \<parallel>s\<parallel> = 0 \<longrightarrow> r = t " 
  by (metis (no_types, hide_lams) Rep_real_int_inject left.rep_eq prod.collapse
      real_int.length_zero_iff_borders_eq real_int.rchop_def right.rep_eq)

lemma chop_empty2:"R_Chop(r,s,t) \<and> \<parallel>t\<parallel> = 0 \<longrightarrow> r = s " 
  by (metis (no_types, hide_lams) Rep_real_int_inject left.rep_eq prod.collapse
      real_int.length_zero_iff_borders_eq real_int.rchop_def right.rep_eq)

lemma intersect_left : "left (intersect r s) \<ge> left r" using Abs_real_int_inverse 
  using empty_left left_leq_right local.intersect_def by auto

lemma intersect_right : "right (intersect r s) \<le> right r" using Abs_real_int_inverse 
  using empty_right left_leq_right local.intersect_def by auto

lemma intersect_leq : "intersect r s \<le> r" 
  using intersect_left intersect_right less_eq_real_int_def by auto

lemma intersect_left': "left (s) \<le> right (r) \<longrightarrow> left (intersect r s) \<ge> left (s)" 
proof
  assume assm:"left (s) \<le> right (r)"
  then show "left (intersect r s) \<ge> left (s)" 
  proof (cases "right (s) < left (r)" )
    case True
    then show ?thesis using   real_int.left_leq_right  
      by (meson intersect_left less_imp_triv not_le order_trans)
  next
    case False
    then have "intersect r s = 
    Abs_real_int (max (left r) (left s), 
                   min (right r) (right s))"
      using intersect_def assm 
      by simp
    then have "left (intersect r s) = max (left (r)) (left (s))" 
      using Abs_real_int_inverse False assm real_int.left_leq_right 
      by auto
    then show ?thesis  by linarith
  qed
qed

lemma intersect_right': 
  "right s \<ge> left r \<longrightarrow> right (intersect r s) \<le> right s" 
proof
  assume assm:"right (s) \<ge> left (r)"
  then show "right (intersect r s) \<le> right (s)" 
  proof (cases "left (s) > right (r)" )
    case True
    then show ?thesis using  intersect_right real_int.left_leq_right 
      by (meson le_less_trans not_less order.asym)
  next
    case False
    then have "intersect r s = 
      Abs_real_int (max (left (r)) (left (s)), 
                     min (right (r)) (right (s)))"
      using intersect_def assm by auto
    then have "right (intersect r s) = min (right (r)) (right (s))" 
      using Abs_real_int_inverse False assm real_int.left_leq_right
      by auto
    then show ?thesis  by linarith
  qed
qed    

lemma intersect_with_zero: "\<parallel>s\<parallel> = 0 \<longrightarrow> \<parallel>intersect r s\<parallel> = 0" 
proof
  assume "\<parallel>s\<parallel> = 0"
  then obtain x where "s = mk_empty x" 
    using empty_left empty_right left_right_eq length_zero_iff_borders_eq by auto
  consider (1) "x < left r" | (2) "x > right r" | (3) "left r \<le> x \<and> x \<le> right r" 
    using not_less by blast
  then show "\<parallel>intersect r s \<parallel> = 0" 
  proof (cases)
    case 1 
    show ?thesis 
      using "1" \<open>s = mk_empty x\<close> empty_left empty_length length_def local.intersect_def by auto
  next
    case 2
    show ?thesis 
      using "2" \<open>s = mk_empty x\<close> empty_length empty_right length_zero_iff_borders_eq local.intersect_def by auto
  next
    case 3
    have a:"max (left r) x = x" using 3
      by (simp add: max.commute max.order_iff)
    have b:"min (right r) x = x" using 3 
      by (simp add: min.commute min.order_iff)
    show ?thesis using 3 a b 
      using \<open>\<parallel>s\<parallel> = 0\<close> \<open>s = mk_empty x\<close> empty_left empty_stretch intersect_def length_def stretch_def by auto
  qed
qed

lemma rchop_intersect_leq_left : "intersect r s = r \<and> t \<le> r \<longrightarrow> left (intersect t s) = left t" 
proof
  assume a:"intersect r s = r \<and> t \<le> r"
  consider (1) "(left s > right r)" | (2) "(right s < left r)" | (3) "(left s \<le> right r) \<and> (right s\<ge> left r)"    
    using not_less by blast
  then show "left (intersect t s) = left t"
  proof (cases)
    case 1
    have "intersect r s = mk_empty (right r)" using 1 intersect_def 
      by simp
    then have "left r = right r" 
      by (metis a empty_left)
    then show ?thesis
      by (metis a chop_leq1 chop_singleton_left' dual_order.order_iff_strict less_real_int_def order_trans rchop_def)   
  next
    case 2
    then have "left s \<le> right r " using left_leq_right 
      by (meson left_leq_right less_eq_real_def order_trans)
    then have "intersect r s = mk_empty (left r)" using 2 intersect_def 
      by simp
    then show ?thesis 
      by (metis  a chop_leq1 chop_singleton_left dual_order.antisym empty_right less_eq_real_int_def order_trans rchop_def) 
  next 
    case 3
    then have 4:"(left s \<le> right t) \<and> (right s\<ge> left t)" 
      by (metis a intersect_left' intersect_right' left_leq_right less_eq_real_int_def order_trans)
    have "max (left t) (left s) = left t" 
      using "3" a intersect_left' less_eq_real_int_def by fastforce 
    then show ?thesis using 4 intersect_right' 
      by (metis a add_0_right less_eq_real_int_def local.intersect_def min_def not_le order_trans real_int_class.shift_def shift_zero)
  qed
qed

lemma rchop_intersect_leq_right : "intersect r s = r \<and> t \<le> r \<longrightarrow> right (intersect t s) = right t" 
proof
  assume a:"intersect r s = r \<and> t \<le> r"
  consider (1) "(left s > right r)" | (2) "(right s < left r)" | (3) "(left s \<le> right r) \<and> (right s\<ge> left r)"    
    using not_less by blast
  then show "right (intersect t s) = right t"
  proof (cases)
    case 1
    have "intersect r s = mk_empty (right r)" using 1 intersect_def 
      by simp
    then have "left r = right r" 
      by (metis a empty_left)
    then show ?thesis
      by (metis a chop_leq1 chop_singleton_left' dual_order.order_iff_strict less_real_int_def order_trans rchop_def)   
  next
    case 2
    then have "left s \<le> right r " using left_leq_right 
      by (meson left_leq_right less_eq_real_def order_trans)
    then have "intersect r s = mk_empty (left r)" using 2 intersect_def 
      by simp
    then show ?thesis 
      by (metis  a chop_leq1 chop_singleton_left dual_order.antisym empty_right less_eq_real_int_def order_trans rchop_def) 
  next 
    case 3
    then have 4:"(left s \<le> right t) \<and> (right s\<ge> left t)" 
      by (metis a intersect_left' intersect_right' left_leq_right less_eq_real_int_def order_trans)
    have "max (left t) (left s) = left t" 
      using "3" a intersect_left' less_eq_real_int_def by fastforce 
    then show ?thesis using 4 intersect_right' 
      by (metis a add_0_right less_eq_real_int_def local.intersect_def min_def not_le order_trans real_int_class.shift_def shift_zero)
  qed
qed

lemma rchop_intersect_left:" (intersect r s) = r \<and> R_Chop(r, r1, r2) \<longrightarrow> intersect r1 s = r1"   
  using chop_leq1 left_right_eq rchop_intersect_leq_left rchop_intersect_leq_right by blast

lemma rchop_intersect_right:" (intersect r s) = r \<and> R_Chop(r, r1, r2) \<longrightarrow> intersect r2 s = r2"   
  using chop_leq2 left_right_eq rchop_intersect_leq_left rchop_intersect_leq_right by blast

lemma rchop_intersect_compose:
  "R_Chop(r,r1,r2) \<and> ( intersect r1 s = r1) \<and> (intersect r2 s = r2)
     \<longrightarrow> (intersect r s = r)" 
proof
  assume a:"R_Chop(r,r1,r2) \<and> ( intersect r1 s = r1) \<and> (intersect r2 s = r2)"
  consider (1) "\<parallel>r1\<parallel> = 0 \<and> \<parallel>r2\<parallel> = 0 " | (2) "\<parallel>r1\<parallel> \<noteq> 0 \<and> \<parallel>r2\<parallel> = 0"  | (3) "\<parallel>r1\<parallel> = 0 \<and> \<parallel>r2\<parallel> \<noteq> 0 " | (4) "\<parallel>r1\<parallel> \<noteq> 0 \<and> \<parallel>r2\<parallel> \<noteq> 0 "  
    by blast
  then show "(intersect r s = r)" 
  proof (cases)
    case 1
    then show ?thesis 
      using a chop_empty1 by blast
  next
    case 2
    then show ?thesis 
      using a chop_empty2 by blast
  next
    case 3
    then show ?thesis 
      using a chop_empty1 by blast
  next
    case 4
    have "right (intersect r2 s ) \<le> right s" 
      by (metis "4" a empty_length intersect_right' leI local.intersect_def)
    then have 5:"left (r) \<le> right s" 
      by (metis a left_leq_right order_trans rchop_def)
    have "left (intersect r1 s) \<ge> left s" 
      by (metis "4" a empty_length intersect_left' leI local.intersect_def)
    then have 6: "left (s) \<le> right r" 
      by (metis a left_leq_right order_trans rchop_def)
    have 7:"max (left s) (left r) = left r" 
      using \<open>left s \<le> left (intersect r1 s)\<close> a rchop_def by auto
    have 8:"min (right s) (right r) = right r" 
      using \<open>right (intersect r2 s) \<le> right s\<close> a rchop_def by auto
    have 9:"left (intersect r s) = left r" 
      by (metis "8" \<open>left s \<le> left (intersect r1 s)\<close> a add.right_neutral intersect_def left_leq_right less_eq_real_int_def linear max.idem min_def not_le rchop_def rchop_intersect_leq_left real_int_class.shift_def shift_zero)
    have 10:"right (intersect r s) = right r" 
      by (metis \<open>left s \<le> left (intersect r1 s)\<close> \<open>right (intersect r2 s) \<le> right s\<close> a add.right_neutral intersect_def left_leq_right less_eq_real_int_def max.idem min.idem not_le rchop_def rchop_intersect_leq_right real_int_class.shift_def shift_zero)
    then show ?thesis using 9 10 
      by (simp add: left_right_eq)
  qed
qed    

lemma leq_intersect_leq: "t \<le> r \<longrightarrow> \<parallel>intersect t s\<parallel> = 0 \<or>  intersect t s \<le> intersect r s" 
proof
  assume a:"t \<le> r" 
  consider  (1) "(left s > right r)" | (2) "(right s < left r)" | (3) "(left s \<le> right r) \<and> (right s\<ge> left r)" 
    using not_le by blast
  then show " \<parallel>intersect t s\<parallel> = 0 \<or>  intersect t s \<le> intersect r s" 
  proof (cases)
    case 1
    then show ?thesis 
      using a empty_length less_eq_real_int_def local.intersect_def by auto  
  next
    case 2
    then show ?thesis 
      using a empty_length less_eq_real_int_def local.intersect_def by auto  
  next
    case 3
    consider (4) "(left s > right t \<or> right s < left t)" | (5) "(left s \<le> right t) \<and> (right s\<ge> left t)" using not_le by blast
    then show ?thesis 
    proof (cases)
      case 4
      then show ?thesis 
        using empty_length local.intersect_def by auto
    next
      case 5
      then show ?thesis using less_eq_real_int_def 
        using Abs_real_int_inverse a left_leq_right local.intersect_def by auto
    qed
  qed
qed  

lemma leq_intersect_length: "t \<le> r \<longrightarrow> \<parallel>intersect t s\<parallel> \<le> \<parallel>intersect r s\<parallel>" 
  by (metis length_ge_zero length_leq leq_intersect_leq)

lemma rchop_intersect_empty_left: "\<parallel>intersect r s\<parallel> = 0 \<and> R_Chop(r,r1,r2) \<longrightarrow> \<parallel>intersect r1 s\<parallel> = 0" 
  by (metis chop_leq1 length_ge_zero leq_intersect_length order_class.order.antisym)

lemma rchop_intersect_empty_right: "\<parallel>intersect r s\<parallel> = 0 \<and> R_Chop(r,r1,r2) \<longrightarrow> \<parallel>intersect r2 s\<parallel> = 0" 
  by (metis chop_leq2 dual_order.antisym length_ge_zero leq_intersect_length)

lemma rchop_intersect_add: "R_Chop(r,r1,r2) \<longrightarrow> \<parallel>intersect r s\<parallel> = \<parallel>intersect r1 s\<parallel>  + \<parallel>intersect r2 s\<parallel>" 
proof
  assume a:"R_Chop(r,r1,r2)" 
  consider (1) "(left s > right r \<or> right s < left r)" | (2) "(left s \<le> right r) \<and> (right s\<ge> left r)" using not_le by blast
  then show "\<parallel>intersect r s\<parallel> = \<parallel>intersect r1 s\<parallel>  + \<parallel>intersect r2 s\<parallel>"
  proof (cases)
    case 1
    then have "\<parallel>intersect r s\<parallel> = 0" 
      using empty_length local.intersect_def by auto
    then show ?thesis 
      by (metis a add.right_neutral rchop_intersect_empty_left rchop_intersect_empty_right)
  next
    case 2
    consider (z) "\<parallel>r\<parallel> = 0 \<or> \<parallel>s\<parallel> = 0 " | (nz) "\<parallel>r\<parallel> \<noteq> 0 \<and> \<parallel>s\<parallel> \<noteq> 0" by blast
    then show ?thesis 
    proof (cases)
      case z
      then show ?thesis 
      proof 
        assume "\<parallel>r\<parallel> = 0"
        then have "\<parallel>intersect r s\<parallel> = 0 " using length_leq 
          by (metis chop_leq1 dual_order.antisym empty_left empty_length empty_right intersect_leq rchop_def)
        then show ?thesis 
          by (metis a add.left_neutral  rchop_intersect_empty_left rchop_intersect_empty_right)
      next
        assume "\<parallel>s\<parallel> = 0" 
        then show ?thesis 
          by (simp add: intersect_with_zero)
      qed
    next
      case nz
      then have "(left s < right r) \<or> (right s > left r)" 
        by (metis "2" dual_order.order_iff_strict left_leq_right length_zero_iff_borders_eq not_le)
      have 3:"left (intersect r s) = max (left r) (left s) " 
        using "2" Abs_real_int_inverse Rep_real_int local.intersect_def by auto
      have 4:"right (intersect r s) = min (right r) (right s)" 
        using "2" Abs_real_int_inverse Rep_real_int local.intersect_def by auto
      show ?thesis
      proof (cases "left s \<le> right r1")
        case False
        then have empty:"\<parallel>intersect r1 s\<parallel> = 0" 
          by (simp add: empty_length local.intersect_def)
        have 5:"left s \<le> right r2 \<and> right s \<ge> left r2" 
          by (metis "2" False a dual_order.order_iff_strict leI left_leq_right less_trans rchop_def)
        have 6:"left (intersect r2 s) = max (left r2) (left s) " 
           using "5" Abs_real_int_inverse Rep_real_int local.intersect_def by auto
        have 7:"right (intersect r2 s) = min (right r2) (right s) " 
           using "5" Abs_real_int_inverse Rep_real_int local.intersect_def by auto
        have 8:"left (intersect r2 s) = left (intersect r s)" 
          by (metis "3" "6" False a left_leq_right max.order_iff max_def max_less_iff_conj not_le rchop_def)
        have 9:"right (intersect r2 s) = right (intersect r s)" 
          using "4" "7" a rchop_def by auto
        show ?thesis using 8 9 empty 
          by (simp add: length_def)
      next  
        case True
        have 5:"left s \<le> right r1 \<and> right s \<ge> left r1" 
          by (metis "2" True a rchop_def)
        then have 6:"left (intersect r1 s) = max (left r1) (left s) " 
          using Abs_real_int_inverse Rep_real_int local.intersect_def by auto        
        then have 7:"left (intersect r1 s) = left (intersect r s)"  
          using "3" a rchop_def by auto
        have 8:"right (intersect r1 s) = min (right r1) (right s) " 
           using "5" Abs_real_int_inverse Rep_real_int local.intersect_def by auto
        show ?thesis 
        proof (cases "right s \<ge> left r2")
          case False
          then have "\<parallel>intersect r2 s\<parallel> = 0" 
            by (simp add: empty_length intersect_def)
          then have "right (intersect r1 s) = right (intersect r s)" 
            by (metis "4" "8" False a chop_leq1 dual_order.order_iff_strict less_real_int_def min_def order_trans rchop_def) 
          then show ?thesis 
            using "7" \<open>\<parallel>intersect r2 s\<parallel> = 0\<close> length_def by auto
        next
          case True
          have 9:"left s \<le> right r2 \<and> right s \<ge> left r2" 
            using "2" True a rchop_def by auto 
          then have 10:"right (intersect r1 s) = right r1" 
            using "8" a rchop_def by auto
          have 11:"left (intersect r2 s) = max (left r2) (left s) " 
           using "9" Abs_real_int_inverse Rep_real_int local.intersect_def by auto
          have 12:"right (intersect r2 s) = min (right r2) (right s) " 
            using "9" Abs_real_int_inverse Rep_real_int local.intersect_def by auto
          then show ?thesis 
            using "10" "11" "4" "5" "7" a length_def rchop_def by auto
        qed
      qed
    qed
  qed
qed

lemma intersect_length_not_empty:"\<parallel>intersect r s\<parallel> > 0 \<longrightarrow> (left s < right r) \<and> (right s > left r)" 
proof
  assume a:"\<parallel>intersect r s\<parallel> > 0"
  then have 1:"left s \<le> right r \<and> right s \<ge> left r" 
    by (metis empty_length leI less_irrefl local.intersect_def)
  have 2:"left s < right r" 
    by (metis "1" a diff_gt_0_iff_gt intersect_left' intersect_right le_less_trans length_def not_le)
  have 3: "right s > left r"
    by (metis "1" a diff_gt_0_iff_gt intersect_right' intersect_left le_less_trans length_def not_le)
  show "(left s < right r) \<and> (right s > left r)" using 2 3 by blast
qed

lemma intersect_fills_leq:
  assumes a:"\<parallel>intersect r s\<parallel> > 0"
  obtains t where " t \<le> r \<and> intersect t s = t \<and> \<parallel>intersect r s\<parallel> = \<parallel>intersect t s\<parallel>" 
proof -
  obtain y where y:"y =  \<parallel>intersect r s\<parallel>" by blast
  obtain x where x:"intersect r s = stretch x y" 
    by (metis Groups.add_ac(2) Rep_real_int_inverse \<open>y = \<parallel>intersect r s\<parallel>\<close> diff_add_cancel left.rep_eq length_def prod.collapse real_int.stretch_def right.rep_eq)
  let ?t = "stretch x y" 
  have 1:"?t \<le> r" using x
    by (metis intersect_leq)
  have h1:"(left s < right r) \<and> (right s > left r)" using intersect_length_not_empty a by blast
  then have h2:"(left s < right ?t) \<and> (right s > left ?t)" using 1 
    by (metis assms diff_gt_0_iff_gt  dual_order.strict_trans1 dual_order.strict_trans2 intersect_left' intersect_right' le_less_trans length_def less_eq_real_def linear not_le x)
  have lr:"left (intersect r s) = max (left r) (left s)" using h1 
    using Abs_real_int_inverse Rep_real_int local.intersect_def by auto
  have rr:"right (intersect r s) = min (right r) (right s)"  
    using h1 Abs_real_int_inverse Rep_real_int local.intersect_def by auto
  have lt:"left (intersect ?t s) = max (left ?t) (left s)"  
    using h2 Abs_real_int_inverse Rep_real_int local.intersect_def by auto
  have rt:"right (intersect ?t s) = min (right ?t) (right s)"  
    using h2 Abs_real_int_inverse Rep_real_int local.intersect_def by auto
  have 2:"intersect (stretch x y) s =  stretch x y" using lt rt 
    using left_right_eq lr rr x by auto
  show ?thesis using 1 2 x 
    using that by fastforce 
qed

lemma intersect_fills_chop:" \<parallel>intersect r s\<parallel> > 0 \<longrightarrow> ( \<exists>r1 r2 r3 t. R_Chop(r,r1,r2) \<and> R_Chop(r2,t,r3)  \<and> intersect t s = t \<and> \<parallel>intersect r s\<parallel> = \<parallel>intersect t s\<parallel>)"
proof
  assume a:"\<parallel>intersect r s\<parallel> > 0"
  then obtain t where t:"t \<le> r \<and> intersect t s = t \<and> \<parallel>intersect r s\<parallel> = \<parallel>intersect t s\<parallel>" using intersect_fills_leq by blast
  obtain r1 where r1:"left r1 = left r \<and> right r1 = left t" 
    by (metis add.commute diff_add_cancel diff_ge_0_iff_ge less_eq_real_int_def stretch_left stretch_right t) 
  obtain r2 where r2:"left r2 = right r1 \<and> right r2 = right r" using Abs_real_int_inverse 
    by (metis diff_add_cancel diff_ge_0_iff_ge left_leq_right less_eq_real_int_def linordered_field_class.sign_simps(27) min.bounded_iff min_def  r1 stretch_left stretch_right t)
  obtain r3 where r3:"left r3 = right t \<and> right r3 = right r" 
    by (metis add_minus_cancel add_uminus_conv_diff diff_ge_0_iff_ge less_eq_real_int_def linordered_field_class.sign_simps(27) stretch_left stretch_right t)  
  then have "R_Chop(r,r1,r2) \<and> R_Chop(r2,t,r3)" using r1 r2 r3 
    by (simp add: rchop_def)
  then show  "\<exists>r1 r2 r3 t. R_Chop(r,r1,r2) \<and> R_Chop(r2,t,r3)  \<and> intersect t s = t \<and> \<parallel>intersect r s\<parallel> = \<parallel>intersect t s\<parallel>" 
    using t by blast
qed
end
(*lemmas[simp] = length_dict *)
  
end
