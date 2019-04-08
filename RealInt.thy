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
    
    
lemma length_ge_zero :" \<parallel>r\<parallel> \<ge> 0" using left_leq_right 
  by (simp add: length_def)

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
    
end
(*lemmas[simp] = length_dict *)
  
end
