(*  Title:      Views.thy
    Author:     Sven Linker, University of Liverpool

Defines a type for views on traffic. Consists of closed real valued interval
denoting "extension" (length on the road visible", the visible interval of lanes,
and the owner of the view.

Contains chopping relations on extension and lanes and switching to
different owners.
*)

section\<open>Views on Traffic\<close>
text\<open>
In this section, we define a notion of locality for each car. These
local parts of a road are called \emph{views} and define the part of 
the model currently under consideration by a car. In particular, a 
view consists of 
\begin{itemize}
\item the \emph{extension}, a real-valued interval denoting the distance perceived,  
\item the \emph{lanes}, a discrete interval, denoting which lanes are perceived,
\item the \emph{owner}, the car associated with this view.
\end{itemize} 
\<close>

theory Views
  imports NatInt RealInt Cars
begin


type_synonym lanes = nat_int
type_synonym extension = real_int
  
  
record basic_view = 
  ext::extension 
  lan ::lanes  
  own ::cars

print_record basic_view
print_theorems
typedef view = "{v::basic_view. continuous (lan v) \<and> more v = ()}" 
proof -
  obtain e where "e = Abs_real_int (1,1)" by simp
  obtain l where "l = \<emptyset>" by simp
  obtain c where "c = Abs_cars 0" by simp
  obtain v where "v = \<lparr> ext = e, lan = l, own = c\<rparr>" by simp
  have "continuous l"   
    by (simp add: \<open>l = bot\<close> empty_continuous) 
  then show ?thesis 
    by (metis (mono_tags, lifting) all_not_in_conv  cases mem_Collect_eq   select_convs(2) select_convs(4) )
qed

setup_lifting type_definition_view 

lift_definition lan::"view \<Rightarrow> lanes" is basic_view.lan .
lift_definition ext::"view \<Rightarrow> extension" is basic_view.ext .
lift_definition own::"view \<Rightarrow> cars" is basic_view.own .


text \<open>
The orders on discrete and continuous intervals induce an order on views. 
For two views \(v\) and \(v^\prime\) with \(v \leq v^\prime\), we call \(v\)
a \emph{subview} of \(v^\prime\).\<close>

instantiation  view::  order
begin  
definition "less_eq_view (V:: view)  (V'::  view)  \<equiv>
     (ext V \<le> ext V') \<and> (lan V \<sqsubseteq>  lan V') \<and> own V = own V'"
definition "less_view (V :: view) (V'::  view)  \<equiv> 
     (ext V \<le> ext V') \<and> (lan V \<sqsubseteq>  lan V') \<and> own V' = own V
 \<and>
     \<not>((ext V' \<le> ext V) \<and> (lan V' \<sqsubseteq>  lan V) \<and> own V' = own V)"
instance   
proof
  fix v v' v''::  "view" 
  show "v \<le> v" 
    by (simp add: less_eq_view_def) 
  show " (v < v') = (v \<le> v' \<and> \<not> v' \<le> v)" 
    using less_eq_view_def less_view_def by auto
  show "v \<le> v' \<Longrightarrow> v' \<le> v'' \<Longrightarrow> v \<le> v''" 
    using less_eq_view_def less_eq_nat_int.rep_eq order_trans by auto
  show "v \<le> v' \<Longrightarrow> v' \<le> v \<Longrightarrow> v = v'" 
  proof -
    assume "v \<le> v'" and "v' \<le> v" 
    have "lan v = lan v'" 
      using \<open>v \<le> v'\<close> \<open>v' \<le> v\<close> less_eq_view_def by auto
    have "ext v = ext v'" 
      using \<open>v \<le> v'\<close> \<open>v' \<le> v\<close> less_eq_view_def by auto
    then show "v = v'" 
      using Rep_view_inject \<open>Views.lan v = Views.lan v'\<close> \<open>v' \<le> v\<close> ext.rep_eq lan.rep_eq less_eq_view_def own.rep_eq by fastforce
  qed
qed  
end 
  
  
locale view
begin

notation nat_int.maximum ("maximum")
notation nat_int.minimum ("minimum")
notation nat_int.consec ("consec")

text\<open>We lift the chopping relations from discrete and continuous intervals
to views, and introduce new notation for these relations.\<close> 

definition       hchop :: "view \<Rightarrow> view \<Rightarrow>  view \<Rightarrow> bool" ("_=_\<parallel>_")
  where "(v=u\<parallel>w) == real_int.R_Chop(ext v)(ext u)(ext w) \<and> 
                    lan v=lan u \<and> 
                    lan v=lan w \<and> 
                    own v = own u \<and> 
                    own v = own w "
definition   vchop :: "view \<Rightarrow> view \<Rightarrow>  view \<Rightarrow> bool" ("_=_--_")
  where "(v=u--w) == nat_int.N_Chop(lan v)(lan u)( lan w) \<and> 
                     ext v = ext u \<and> 
                     ext v = ext w \<and> 
                     own v = own u \<and> 
                     own  v = own w"

text\<open>We can also switch the perspective of a view to the car \(c\). That is,
we substitute \(c\) for the original owner of the view.\<close>

definition switch :: "view \<Rightarrow> cars \<Rightarrow> view \<Rightarrow> bool" ("_ = _ > _")
  where   "  (v=c>w) == ext v = ext w \<and> 
                        lan v = lan w \<and>  
                        own w = c "

text\<open>Most of the lemmas in this theory are direct transfers of the corresponding
lemmas on discrete and continuous intervals, which implies rather simple proofs.
The only exception is 
the connection between subviews and the chopping operations. This proof is rather lengthy,
since we need to distinguish several cases, and within each case, we need to
 explicitly construct six different views for the chopping relations.\<close>

lemma h_chop_middle1:"(v=u\<parallel>w) \<longrightarrow> left (ext v) \<le> right (ext u)" 
  by (metis hchop_def real_int.rchop_def real_int.left_leq_right)
    
lemma h_chop_middle2:"(v=u\<parallel>w) \<longrightarrow> right (ext v) \<ge> left (ext w)" 
  using real_int.left_leq_right real_int.rchop_def view.hchop_def by auto
    
    
lemma horizontal_chop1: " \<exists> u w. (v=u\<parallel>w)" 
proof -
  have real_chop:"\<exists>x1 x2.  R_Chop(ext v, x1,x2)" 
    using real_int.chop_singleton_left by force
  obtain x1 and x2 where x1_x2_def:" R_Chop(ext v, x1,x2)" 
    using real_chop by force
  obtain V1 and V2 
    where v1:"V1 = \<lparr> basic_view.ext = x1, lan = lan v, own = own v\<rparr>" 
    and v2:"V2 = \<lparr> basic_view.ext = x2,lan= lan v, own = own v\<rparr> "  by blast
  from v1 and v2 have "v= (Abs_view V1)\<parallel> (Abs_view V2)" 
    using hchop_def x1_x2_def 
    using Abs_view_inverse Rep_view ext.rep_eq lan.rep_eq own.rep_eq by auto 
  thus ?thesis by blast
qed
  
lemma horizontal_chop_empty_right :" \<exists> u. (v=v\<parallel>u)" 
proof -
  obtain u where 1:"u = Abs_view (\<lparr>basic_view.ext = (Abs_real_int (right( ext v),right (ext v))), lan = lan v, own = own v\<rparr>)" by simp
  then have "R_Chop(ext v, ext v, ext u)" 
    using Abs_real_int_inverse Abs_view_inverse Rep_view ext.rep_eq lan.rep_eq rchop_def by auto
  then have "v = v\<parallel>u" 
    using "1" Abs_view_inverse Rep_view lan.rep_eq own.rep_eq view.hchop_def by auto 
  then show ?thesis by blast  
qed

lemma horizontal_chop_empty_left :"\<exists>u. (v=u\<parallel>v)" 
proof -
  obtain u where 1:"u = Abs_view (\<lparr>basic_view.ext = (Abs_real_int (left( ext v),left (ext v))), lan = lan v, own = own v\<rparr>)" by simp
  then have "R_Chop(ext v, ext u, ext v)" 
    using Abs_real_int_inverse Abs_view_inverse Rep_view ext.rep_eq lan.rep_eq rchop_def by auto
  then have "v = u\<parallel>v" 
    using "1" Abs_view_inverse Rep_view lan.rep_eq own.rep_eq view.hchop_def by auto 
  then show ?thesis by blast  
qed
    
lemma horizontal_chop_non_empty:
  "\<parallel>ext v\<parallel> > 0 \<longrightarrow> (\<exists>u w. (v=u\<parallel>w) \<and> \<parallel>ext u\<parallel> > 0 \<and> \<parallel>ext w\<parallel>>0)"
proof
  assume "\<parallel>ext v\<parallel> > 0" 
  then obtain l1 and l2 
    where chop:" R_Chop(ext v, l1,l2) \<and> \<parallel>l1\<parallel> > 0 \<and> \<parallel>l2\<parallel> > 0" 
    using real_int.chop_dense by force
  obtain v1 where v1_def:"v1 = \<lparr> basic_view.ext = l1, lan = lan v, own = own v \<rparr>" 
    by simp
  obtain v2 where v2_def:"v2 = \<lparr> basic_view.ext = l2, lan = lan v, own = own v \<rparr>" 
    by simp
  then obtain V1 and V2 where "V1 = Abs_view v1" and "V2 = Abs_view v2" by simp 
  then have  "(v=(V1)\<parallel>( V2)) \<and> \<parallel>ext V1\<parallel> > 0 \<and> \<parallel>ext V2\<parallel>>0" 
   using  chop hchop_def v1_def  
   using Abs_view_inverse Rep_view ext.rep_eq lan.rep_eq own.rep_eq v2_def by auto
  then show " (\<exists>V1 V2. (v=V1\<parallel>V2) \<and> \<parallel>ext V1\<parallel> > 0 \<and> \<parallel>ext V2\<parallel>>0)"
    by blast
qed
  
  
lemma horizontal_chop_split_add:
  "x \<ge> 0 \<and> y \<ge> 0 \<longrightarrow> \<parallel>ext v\<parallel> = x+y \<longrightarrow> (\<exists>u w. (v=u\<parallel>w) \<and> \<parallel>ext u\<parallel> = x \<and> \<parallel>ext w\<parallel> = y)"
proof (rule impI)+
  assume geq_0:"x \<ge> 0 \<and> y \<ge> 0" and len_v:"\<parallel>ext v\<parallel> = x+y"
  obtain v1 
    where v1_def: 
      "v1 = \<lparr> basic_view.ext = Abs_real_int (left (ext v), left (ext v) + x), lan = lan v, own = (own v) \<rparr>"
    by simp
  have v1_in_type:"(left (ext v), left (ext v) + x) \<in> {r::(real*real) . fst r \<le> snd r}" 
    by (simp add: geq_0)
  obtain v2 
    where v2_def:
      "v2 = \<lparr> basic_view.ext = Abs_real_int (left (ext v)+x, left (ext v) + (x+y)), 
             lan = (lan v), own = (own v) \<rparr>" by simp
  have v2_in_type:
    "(left (ext v)+x, left (ext v) + (x+y)) \<in> {r::(real*real) . fst r \<le> snd r}" 
    by (simp add: geq_0)
  obtain u and w where "u = Abs_view v1" and "w = Abs_view v2" by simp
  from v1_def and geq_0 have len_v1:"\<parallel>ext u\<parallel> = x" using v1_in_type 
    using Abs_real_int_inverse Abs_view_inverse Rep_view \<open>u = Abs_view v1\<close> ext.rep_eq lan.rep_eq real_int.length_def by auto
  from v2_def and geq_0 have len_v2:"\<parallel>ext w\<parallel>= y" using v2_in_type 
    using Abs_real_int_inverse Abs_view_inverse Rep_view \<open>w = Abs_view v2\<close> ext.rep_eq lan.rep_eq real_int.length_def by auto
  from v1_def and v2_def have "(v=u\<parallel>w)" 
    using Abs_real_int_inverse Abs_view_inverse Rep_view \<open>u = Abs_view v1\<close> \<open>w = Abs_view v2\<close> ext.rep_eq lan.rep_eq len_v own.rep_eq rchop_def real_int.length_def v1_in_type v2_in_type view.hchop_def by auto
  with len_v1 and len_v2 have "(v=u\<parallel>w) \<and> \<parallel>ext u\<parallel> = x \<and> \<parallel>ext w\<parallel> = y" by simp
  thus "(\<exists>u w. (v=u\<parallel>w) \<and> \<parallel>ext u\<parallel> = x \<and> \<parallel>ext w\<parallel> = y)" by blast
qed
  
lemma horizontal_chop_assoc1:
  "(v=v1\<parallel>v2) \<and> (v2=v3\<parallel>v4) \<longrightarrow> (\<exists>v'. (v=v'\<parallel>v4) \<and> (v'=v1\<parallel>v3))"
proof
  assume assm:"(v=v1\<parallel>v2) \<and> (v2=v3\<parallel>v4)"
  obtain u' 
    where v'_def:
      "u' =\<lparr> basic_view.ext = Abs_real_int(left (ext v1), right (ext v3)),
             lan = (lan v), own = (own v) \<rparr>"
    by simp
  then obtain "v'" where "v' = Abs_view u'" by simp
  hence 1:"v=v'\<parallel>v4" 
    using assm real_int.chop_assoc1 hchop_def v'_def 
    using Abs_view_inverse Rep_view ext.rep_eq lan.rep_eq own.rep_eq by auto
  have 2:"v'=v1\<parallel>v3" using v'_def assm real_int.chop_assoc1 hchop_def 
    using "1" rchop_def by auto
  from 1 and 2 have "(v=v'\<parallel>v4) \<and>  (v'=v1\<parallel>v3)" by best
  thus "(\<exists>v'. (v=v'\<parallel>v4)  \<and> (v'=v1\<parallel>v3))" ..
qed
  
lemma horizontal_chop_assoc2:
  "(v=v1\<parallel>v2) \<and> (v1=v3\<parallel>v4) \<longrightarrow> (\<exists>v'. (v=v3\<parallel>v') \<and> (v'=v4\<parallel>v2))"
proof
  assume assm:"(v=v1\<parallel>v2) \<and> (v1=v3\<parallel>v4)"
  obtain u 
    where v'_def:
      "u=\<lparr> basic_view.ext = Abs_real_int(left (ext v4),right (ext v2)),
            lan = (lan v), own = (own v) \<rparr>"  
    by simp
  then obtain v' where "v' = Abs_view u" by simp
  hence 1:"v=v3\<parallel>v'" 
    using assm fst_conv real_int.chop_assoc2 snd_conv hchop_def 
    using Abs_view_inverse Rep_view ext.rep_eq lan.rep_eq own.rep_eq v'_def by auto
  have 2: "v'=v4\<parallel>v2" 
    using assm real_int.chop_assoc2 v'_def hchop_def 
    using "1" rchop_def by auto
  from 1 and 2 have "(v=v3\<parallel>v') \<and> (v'=v4\<parallel>v2)" by best
  thus "(\<exists>v'. (v=v3\<parallel>v') \<and> (v'=v4\<parallel>v2))" ..
qed
  
lemma horizontal_chop_lanes_continuous:"(v=u\<parallel>w) \<longrightarrow> continuous (lan u) \<and> continuous (lan w)" 
  using Rep_view lan.rep_eq by auto   

lemma horizontal_chop_lanes_stable:"(v=u\<parallel>w) \<longrightarrow> lan v = lan u \<and> lan v = lan w" 
  using view.hchop_def by blast
  
lemma horizontal_chop_width_stable:"(v=u\<parallel>w)\<longrightarrow>|lan v|=|lan u|\<and>|lan v|=|lan w|"
  using hchop_def by auto
    
lemma horizontal_chop_own_trans:"(v=u\<parallel>w) \<longrightarrow> own u = own w" 
  using hchop_def by auto    
    
lemma vertical_chop1:" \<exists> u w. (v=u--w)"
proof -
  have nat_chop:"\<exists>x1 x2.  N_Chop(lan v, x1,x2)" 
    using Rep_view chop_empty_right lan.rep_eq by auto
  then obtain x1 and x2 where x1_x2_def:" N_Chop(lan v, x1,x2)" 
    by force
  obtain V1 and V2 
    where v1:"V1 = \<lparr> basic_view.ext = ext v, lan = x1, own = own v\<rparr>" 
    and v2:"V2 = \<lparr> basic_view.ext = ext v,lan= x2, own = own v\<rparr> "  by blast
  from v1 and v2 have "v= (Abs_view V1)-- (Abs_view V2)" 
    using vchop_def x1_x2_def 
    using Abs_view_inverse Rep_view ext.rep_eq lan.rep_eq own.rep_eq 
    by (simp add: nat_int.nchop_def) 
  thus ?thesis by blast
qed
      
lemma vertical_chop_empty_down:"\<exists> u.(v=v--u)" 
proof -
  obtain u where "u = Abs_view \<lparr>basic_view.ext = ext v, lan = \<emptyset>, own = own v\<rparr>" by simp
  then have "v=v--u" 
    using Abs_view_inverse Rep_view chop_empty_right empty_continuous ext.rep_eq lan.rep_eq own.rep_eq view.vchop_def by auto
  then show ?thesis by blast
qed
    
lemma vertical_chop_empty_up:"\<exists>u.(v=u--v)"
proof -
  obtain u where "u = Abs_view \<lparr>basic_view.ext = ext v, lan = \<emptyset>, own = own v\<rparr>" by simp
  then have "v=u--v" 
    using Abs_view_inverse Rep_view chop_empty_left empty_continuous ext.rep_eq lan.rep_eq own.rep_eq view.vchop_def by auto
  then show ?thesis by blast
qed
    
    
lemma vertical_chop_assoc1:
  "(v=v1--v2) \<and> (v2=v3--v4) \<longrightarrow> (\<exists>v'. (v=v'--v4) \<and> (v'=v1--v3))"
proof
  assume assm:"(v=v1--v2) \<and> (v2=v3--v4)"
  obtain u' 
    where v'_def:"u' = \<lparr> basic_view.ext = ext v, lan=(lan v1) \<squnion> (lan v3), own = (own v) \<rparr>"
    by simp
  then obtain v' where "v' = Abs_view u'" by simp
  have "continuous (lan v')" 
    using nchop_def view.vchop_def view.vertical_chop_empty_down by auto
  then have "N_Chop(basic_view.lan u',lan v1,lan v3)" 
        using v'_def assm nat_int.chop_assoc1 nchop_def Abs_view_inverse  
        by (meson select_convs(2) view.vchop_def view.vertical_chop_empty_down)
  then have 2:"v'=v1--v3" 
    using v'_def assm nat_int.chop_assoc1 vchop_def 
    using Abs_view_inverse \<open>v' = Abs_view u'\<close> ext.rep_eq lan.rep_eq nchop_cont own.rep_eq by auto
  have "N_Chop(lan v, basic_view.lan u', lan v4)" 
    using assm nat_int_class.chop_assoc1 v'_def view.vchop_def by auto
  then have 1:"v=v'--v4" 
    using assm nat_int.chop_assoc1 vchop_def Abs_view_inverse 
    by (metis (mono_tags, lifting) "2" Quotient_to_Domainp Quotient_view \<open>N_Chop(basic_view.lan u',Views.lan v1,Views.lan v3)\<close> \<open>v' = Abs_view u'\<close> lan.abs_eq nchop_cont select_convs(4) v'_def view.domain)
  from 1 and 2 have "(v=v'--v4) \<and>  (v'=v1--v3)" by best
  then show "(\<exists>v'. (v=v'--v4)  \<and> (v'=v1--v3))" ..
qed
  
lemma vertical_chop_assoc2:
  "(v=v1--v2) \<and> (v1=v3--v4) \<longrightarrow> (\<exists>v'. (v=v3--v') \<and> (v'=v4--v2))" 
proof
  assume assm:"(v=v1--v2) \<and> (v1=v3--v4)"
  obtain u' 
    where v'_def:"u'=\<lparr> basic_view.ext = ext v, lan =(lan v4) \<squnion> (lan v2), own = (own v) \<rparr>"  
    by simp
  then obtain v' where "v' = Abs_view u'" by simp
  have "N_Chop(lan v, lan v3, basic_view.lan u')" 
    using assm nat_int_class.chop_assoc2 v'_def view.vchop_def by auto 
  then have 1:"v=v3--v'"  
    using Abs_view_inverse \<open>v' = Abs_view u'\<close> assm ext.rep_eq lan.rep_eq nchop_def own.rep_eq v'_def view.vchop_def by auto
  have "continuous (basic_view.lan u')" 
    using \<open>N_Chop(Views.lan v,Views.lan v3,basic_view.lan u')\<close> nchop_def by blast
  have "N_Chop(basic_view.lan u', lan v4, lan v2)" 
    using assm nat_int_class.chop_assoc2 v'_def view.vchop_def by auto
  then have 2: "v'=v4--v2"
    using assm nat_int.chop_assoc2 v'_def vchop_def 
    using "1" Abs_view_inverse \<open>continuous (basic_view.lan u')\<close> \<open>v' = Abs_view u'\<close> lan.rep_eq by auto
  from 1 and 2 have "(v=v3--v') \<and> (v'=v4--v2)" by best
  then show "(\<exists>v'. (v=v3--v') \<and> (v'=v4--v2))" ..
qed

lemma vertical_chop_singleton:
  "(v=u--w) \<and> |lan v| = 1 \<longrightarrow> ( |lan u| = 0 \<or> |lan w| = 0)" 
  using nat_int.chop_single vchop_def Rep_nat_int_inverse 
  by fastforce
    
lemma vertical_chop_add1:"(v=u--w) \<longrightarrow> |lan v| = |lan u| + |lan w|"
  using nat_int.chop_add1 vchop_def by fastforce

    
lemma vertical_chop_add2:
  "|lan v| = x+y \<longrightarrow> (\<exists> u w.  (v=u--w) \<and> |lan u| = x \<and> |lan w| = y)" 
proof
  assume assm:"|lan v| = x+y"
  hence add:"\<exists>i j. N_Chop(lan v, i,j) \<and> |i| = x \<and> |j| = y"
    using chop_add2 
    using nat_int.nchop_def view.vchop_def view.vertical_chop_empty_down by auto
  obtain i and j where l1_l2_def:"N_Chop(lan v, i,j) \<and> |i| = x \<and> |j| = y"
    using add by blast
  obtain u and w where "u=Abs_view \<lparr>basic_view.ext =  ext v, lan = i, own = (own v) \<rparr>"
    and "w = Abs_view \<lparr> basic_view.ext = ext v, lan = j, own = (own v) \<rparr> " by blast
  hence "(v=u--w) \<and> |lan u|=x \<and> |lan w|=y" 
    using l1_l2_def view.vchop_def 
    by (simp add: Abs_view_inverse ext.rep_eq lan.rep_eq nat_int.nchop_def own.rep_eq)
  thus "(\<exists> u w.  (v=u--w) \<and> |lan u| = x \<and> |lan w| = y)" by blast
qed
  
lemma vertical_chop_length_stable:
  "(v=u--w) \<longrightarrow> \<parallel>ext v\<parallel> = \<parallel>ext u\<parallel> \<and> \<parallel>ext v\<parallel> = \<parallel>ext w\<parallel>"
  using vchop_def by auto
    
lemma vertical_chop_own_trans:"(v=u--w) \<longrightarrow> own u = own w" 
  using vchop_def by auto    
    
lemma vertical_chop_width_mon:
  "(v=v1--v2) \<and> (v2=v3--v4) \<and> |lan v3| = x \<longrightarrow> |lan v| \<ge> x"
  by (metis le_add1 trans_le_add2 vertical_chop_add1)
    
lemma horizontal_chop_leq1:"(v=u\<parallel>w) \<longrightarrow> u \<le> v"
  using real_int.chop_leq1 hchop_def less_eq_view_def order_refl by fastforce
    
lemma horizontal_chop_leq2:"(v=u\<parallel>w) \<longrightarrow> w \<le> v"
  using real_int.chop_leq2 hchop_def less_eq_view_def order_refl by fastforce
    
lemma vertical_chop_leq1:"(v=u--w) \<longrightarrow> u \<le> v"
  using nat_int.chop_subset1 vchop_def less_eq_view_def order_refl by fastforce
    
lemma vertical_chop_leq2:"(v=u--w) \<longrightarrow> w \<le> v"
  using nat_int.chop_subset2 vchop_def less_eq_view_def order_refl by fastforce

lemma horizontal_intermed:"v \<le> v' \<longrightarrow> (\<exists>v''. (ext v'' \<le> ext v') \<and> (lan v'' = lan v') \<and> (own v'' = own v') \<and> (ext v = ext v'') \<and> (lan v \<sqsubseteq> lan v'') \<and> (own v = own v''))"  
proof
  assume "v \<le> v'" 
  obtain v'' where "v'' = Abs_view \<lparr> basic_view.ext = ext v, lan = lan v', own = own v'\<rparr>" by blast
  then have " (ext v'' \<le> ext v') \<and> (lan v'' = lan v') \<and> (own v'' = own v') \<and> (ext v = ext v'') \<and> (lan v \<sqsubseteq> lan v'') \<and> (own v = own v'')" 
    using Abs_view_inverse Rep_view \<open>v \<le> v'\<close> ext.rep_eq lan.rep_eq less_eq_view_def own.rep_eq by auto
  then show "(\<exists>v''. (ext v'' \<le> ext v') \<and> (lan v'' = lan v') \<and> (own v'' = own v') \<and> (ext v = ext v'') \<and> (lan v \<sqsubseteq> lan v'') \<and> (own v = own v''))" by blast
qed

lemma vertical_intermed:"v \<le> v' \<longrightarrow> (\<exists>v''. (ext v'' = ext v') \<and> (lan v'' \<sqsubseteq> lan v') \<and> (own v'' = own v') \<and> (ext v \<le>  ext v'') \<and> (lan v = lan v'') \<and> (own v = own v''))"  
proof
  assume "v \<le> v'" 
  obtain v'' where "v'' = Abs_view \<lparr> basic_view.ext = ext v', lan = lan v, own = own v'\<rparr>" by blast
  then have " (ext v'' = ext v') \<and> (lan v'' \<sqsubseteq> lan v') \<and> (own v'' = own v') \<and> (ext v \<le> ext v'') \<and> (lan v = lan v'') \<and> (own v = own v'')" 
    using Abs_view_inverse Rep_view \<open>v \<le> v'\<close> ext.rep_eq lan.rep_eq less_eq_view_def own.rep_eq by auto
  then show "(\<exists>v''. (ext v'' = ext v') \<and> (lan v'' \<sqsubseteq> lan v') \<and> (own v'' = own v') \<and> (ext v \<le> ext v'') \<and> (lan v = lan v'') \<and> (own v = own v''))" by blast
qed

lemma horizontal_leq:"ext v \<le> ext v' \<and> lan v = lan v' \<and> own v = own v' \<longrightarrow> (\<exists>v1 vl vr. (v'=vl\<parallel>v1) \<and> (v1=v\<parallel>vr))"
proof
  assume assm_exp:"(ext v \<le> ext v') \<and> (lan v = lan v') \<and> (own v = own v')" 
  obtain vl v1  vr 
    where 
      vl:"vl=Abs_view \<lparr>basic_view.ext=Abs_real_int(left(ext v'),left(ext v)), lan=lan v', own=own v'\<rparr>"
    and 
      v1:"v1=Abs_view \<lparr>basic_view.ext=Abs_real_int(left(ext v),right(ext v')), lan=lan v', own=own v'\<rparr>"
    and 
      vr:"vr=Abs_view \<lparr>basic_view.ext=Abs_real_int(right(ext v),right(ext v')), lan=lan v', own=own v'\<rparr>"
    by blast
  have vl_in_type:"(left (ext v'), left (ext v)) \<in> {r::(real*real) . fst r \<le> snd r}" 
    using less_eq_real_int_def assm_exp real_int.left_leq_right snd_conv 
      fst_conv mem_Collect_eq by simp
  have v1_in_type:"(left (ext v), right (ext v')) \<in> {r::(real*real) . fst r \<le> snd r}" 
    using less_eq_real_int_def assm_exp real_int.left_leq_right snd_conv fst_conv
      mem_Collect_eq order_trans by fastforce
  have vr_in_type:"(right (ext v), right (ext v')) \<in> {r::(real*real) . fst r \<le> snd r}" 
    using less_eq_real_int_def assm_exp real_int.left_leq_right snd_conv fst_conv
      mem_Collect_eq order_trans by fastforce
  have "R_Chop(ext v', ext vl, ext v1)" using Abs_view_inverse vl v1 
    by (metis (mono_tags, lifting) Quotient_real_int Quotient_to_Domainp Rep_view eq_onp_to_Domainp ext.rep_eq fst_conv lan.rep_eq left.abs_eq mem_Collect_eq rchop_def right.abs_eq select_convs(1) select_convs(2) select_convs(4) snd_conv v1_in_type vl_in_type)
  then have hchop1: "v'=vl\<parallel>v1" 
    using Abs_view_inverse Rep_view lan.rep_eq own.rep_eq v1 view.hchop_def vl by auto 
  have "R_Chop(ext v1, ext v, ext vr)" using Abs_view_inverse v1  vr 
    by (metis (mono_tags, lifting) Quotient_real_int Quotient_to_Domainp Rep_view eq_onp_to_Domainp ext.rep_eq fst_conv lan.rep_eq left.abs_eq mem_Collect_eq rchop_def right.abs_eq select_convs(1) select_convs(2) select_convs(4) snd_conv  vr_in_type v1_in_type)
  then have hchop2: "v1=v\<parallel>vr" 
    using Abs_view_inverse Rep_view lan.rep_eq own.rep_eq v1  vr view.hchop_def  
    using assm_exp by auto 
  from hchop1 and hchop2 have hchops:"(v'=vl\<parallel>v1)\<and> (v1=v\<parallel>vr)" by simp
  then show "(\<exists>v1 vl vr. (v'=vl\<parallel>v1) \<and> (v1=v\<parallel>vr))" by blast
qed

lemma vertical_leq:"ext v = ext v' \<and> (lan v \<sqsubseteq> lan v') \<and> own v = own v' \<longrightarrow> (\<exists>v1 vu vd. (v'=vd--v1) \<and> (v1=v--vu))"
proof
  assume assm:"ext v = ext v' \<and> (lan v \<sqsubseteq> lan v') \<and> own v = own v'"
  show " \<exists>v1 vu vd. (v'=vd--v1) \<and> (v1=v--vu)"
  proof (cases "lan v = \<emptyset>")
    case True
    then have "(v'=v'--v) \<and> (v=v--v)" 
      using assm chop_empty chop_empty_right horizontal_chop_empty_right horizontal_chop_lanes_continuous view.vchop_def by fastforce
    then show ?thesis by blast
  next
    case False
    let ?lanv = "lan v" 
    let ?lanv' = "lan v'"
    have v'_notE:"?lanv' \<noteq> \<emptyset>" 
      using False assm bot.extremum_unique by fastforce
    have 1:"minimum ?lanv \<ge> minimum ?lanv'" 
      by (simp add: False assm subset_min v'_notE)
    have 2:"maximum ?lanv \<le> maximum ?lanv'" 
      by (simp add: False assm subset_max v'_notE)
    let ?diff_min = "minimum ?lanv - minimum ?lanv'" 
    let ?diff_max = "maximum ?lanv' - maximum ?lanv" 
    have max_rel:"maximum ?lanv' = maximum ?lanv + ?diff_max" 
      by (simp add: "2")
    have min_rel:"minimum ?lanv'= minimum ?lanv - ?diff_min" by (simp add:1) 
    obtain m and n where atLAM_v':"\<forall>l. l \<^bold>\<in> ?lanv' \<longleftrightarrow> l \<in> {m..n}" 
      using continuos_atLeastAtMost view.horizontal_chop_empty_left view.horizontal_chop_lanes_continuous by blast
    from min_rel have min:"m = minimum ?lanv - ?diff_min" 
      using atLAM_v' nat_int_atLeastAtMost_min v'_notE by blast
    from max_rel have max:"n = maximum ?lanv + ?diff_max"
      using atLAM_v' nat_int_atLeastAtMost_max v'_notE by blast
    have v'_rep:"\<forall>l. l \<^bold>\<in> ?lanv' \<longleftrightarrow> l \<in> { minimum ?lanv - ?diff_min .. maximum ?lanv + ?diff_max}" using min max atLAM_v' by blast 
    obtain lan1 where lan1_rep:"\<forall>l. l\<in>{minimum ?lanv  .. maximum ?lanv + ?diff_max} \<longleftrightarrow> l \<^bold>\<in> lan1" using atLeastAtMost_rep
      by blast
    obtain lanu where lanu_rep:"\<forall>l. l\<in>{maximum ?lanv+1 .. maximum ?lanv + ?diff_max} \<longleftrightarrow> l \<^bold>\<in> lanu" using  atLeastAtMost_rep 
      by blast
    obtain land where land_rep:"\<forall>l. l\<in>{minimum ?lanv' .. minimum ?lanv' + ?diff_min - 1} \<longleftrightarrow> l \<^bold>\<in> land" using atLeastAtMost_rep 
      by blast
      have cont1: "continuous (lan1)" using   lan1_rep continuos_atLeastAtMost by blast
      have contu: "continuous lanu" using lanu_rep  continuos_atLeastAtMost by blast
      have contd: "continuous land" using land_rep  continuos_atLeastAtMost by blast
      have contv: "continuous ?lanv" 
        using Rep_view lan.rep_eq by auto
    consider (a) "?diff_min = 0 \<and> ?diff_max = 0" | (b) "?diff_min \<noteq> 0 \<and> ?diff_max = 0" | (c) "?diff_min = 0 \<and> ?diff_max \<noteq> 0" | (d) "?diff_min \<noteq> 0 \<and> ?diff_max \<noteq> 0"
      by blast
    then show ?thesis
    proof (cases)
      case a  
      then have "?lanv = ?lanv'" 
        by (meson "1" False assm diff_is_0_eq leD less_max order.not_eq_order_implies_strict v'_notE view.horizontal_chop_empty_left view.horizontal_chop_lanes_continuous)
      then have "\<exists>vu vd. (v'=vd--v) \<and> (v=v--vu)" 
        by (metis assm less_eq_view_def less_view_def order.order_iff_strict order_refl  view.vertical_chop_empty_down view.vertical_chop_empty_up)
      then show ?thesis by blast
    next
      case b
      then have ge:\<open>?diff_min > 0\<close> using 2 by blast
      have min_less:"minimum ?lanv' + ?diff_min > minimum ?lanv' " 
        using ge by linarith
      have land_notE:"land \<noteq> \<emptyset>" using min_less land_rep 
        by (metis "1"  Suc_diff_1  all_not_in_conv b  card_atLeastAtMost card_empty diff_is_0_eq' le_add_diff_inverse less_imp_diff_less min min_rel non_empty_elem_in  )
      then have 3:"minimum land = minimum ?lanv'" using land_rep nat_int_atLeastAtMost_min 
        by (metis One_nat_def )
      have "maximum land = minimum ?lanv' + ?diff_min -1" using land_rep land_notE nat_int_atLeastAtMost_max 
        by blast
      then have 4:"maximum land + 1= minimum ?lanv" using ge by linarith
      have consec:"consec land ?lanv" using 4 
        by (simp add: False consec_def land_notE)
      have cont1: "continuous land" using land_notE land_rep 
        by (simp add: "3" \<open>maximum land = minimum (Views.lan v') + (minimum (Views.lan v) - minimum (Views.lan v')) - 1\<close> continuous_nonE_atLeastAtMost)
      have "?lanv' = land \<squnion> ?lanv" using consec cont1 False land_notE 
        by (metis (mono_tags, lifting) "3" Rep_view add.right_neutral b consec_un_max consec_un_min lan.rep_eq max_rel mem_Collect_eq nat_int.consec_un_equality v'_notE)
      then have "N_Chop(?lanv', land, ?lanv)" 
        using consec cont1 nchop_def view.horizontal_chop_empty_left view.horizontal_chop_lanes_continuous by blast
      obtain vd where "vd =  \<lparr> basic_view.ext = ext v, lan = land, own =own v\<rparr>"
        by blast
      then have "v'=(Abs_view vd)--v" 
        using Abs_view_inverse \<open>N_Chop(Views.lan v',land,Views.lan v)\<close> assm cont1 ext.rep_eq lan.rep_eq own.rep_eq view.vchop_def by auto
      show ?thesis 
        using \<open>v'=Abs_view vd--v\<close> view.vertical_chop_empty_down by blast
    next
      case c
      then have ge:\<open>?diff_max > 0\<close> using 2 by blast
      have max_less:"maximum ?lanv < maximum ?lanv + ?diff_max" 
        using ge by linarith
      have 3: "minimum ?lanv = minimum lan1" using lan1_rep nat_int_atLeastAtMost_min 
        by (metis "1" c diff_is_0_eq in_eq le_antisym  max min v'_rep)
      have 4:"maximum ?lanv + 1 = minimum lanu" using lanu_rep  nat_int_atLeastAtMost_max nat_int_atLeastAtMost_min 
        by (metis  Suc_eq_plus1 Suc_leI    atLeastAtMost_iff     le_eq_less_or_eq max_less max_rel  non_empty_elem_in  order_trans  )
      have "maximum lan1 = maximum ?lanv + ?diff_max" using lan1_rep nat_int_atLeastAtMost_max  
        by (metis "3" c max  min min_rel minus_nat.diff_0 non_empty_elem_in v'_notE v'_rep)
      have "maximum lanu = maximum ?lanv + ?diff_max" using lanu_rep nat_int_atLeastAtMost_max
        by (metis "4" Max_in Suc_eq_plus1 add_diff_cancel_right card_atLeastAtMost card_empty finite_atLeastAtMost ge max max_rel non_empty_elem_in not_gr_zero)
      have 5:"maximum lan1 = maximum lanu" 
        by (simp add: \<open>maximum lan1 = maximum (Views.lan v) + (maximum (Views.lan v') - maximum (Views.lan v))\<close> \<open>maximum lanu = maximum (Views.lan v) + (maximum (Views.lan v') - maximum (Views.lan v))\<close>) 
      have "lanu \<noteq> \<emptyset>" using lanu_rep max_less 
        using bot_nat_int.rep_eq  by auto
      have "consec ?lanv lanu" 
        using "4" False \<open>lanu \<noteq> bot\<close> consec_def by blast
      have "lan1 = lan v \<squnion> lanu" using lan1_rep lanu_rep v'_rep 3 4 5 
        by (metis \<open>consec (Views.lan v) lanu\<close> \<open>continuous (Views.lan v)\<close> \<open>continuous lan1\<close> \<open>continuous lanu\<close> bot_nat_int.rep_eq c consec_un_equality consec_un_max consec_un_min  el.rep_eq emptyE maximum_in minus_nat.diff_0 v'_notE) 
      have "N_Chop(lan1, ?lanv, lanu)" 
        by (simp add: \<open>consec (Views.lan v) lanu\<close> \<open>continuous (Views.lan v)\<close> \<open>continuous lanu\<close> \<open>lan1 = Views.lan v \<squnion> lanu\<close> nchop_def)
      obtain vu where vu:"vu= \<lparr> basic_view.ext = ext v, lan = lanu, own =own v\<rparr>"
        by blast
      obtain v1 where v1:"v1 = \<lparr> basic_view.ext = ext v, lan = lan1, own = own v\<rparr>"
        by blast
      have chop1:"(Abs_view v1)=v--(Abs_view vu)" 
        using Abs_view_inverse \<open>N_Chop(lan1,Views.lan v,lanu)\<close> \<open>continuous lan1\<close> \<open>continuous lanu\<close> ext.rep_eq lan.rep_eq own.rep_eq v1 view.vchop_def vu by auto
      have "minimum lan1 = minimum ?lanv'" using lan1_rep 
        using "1" "3" c by linarith
      have chop2:"N_Chop(?lanv', \<emptyset>, lan1)" 
        by (metis \<open>\<And>thesis. (\<And>m n. \<forall>l. (l \<^bold>\<in> Views.lan v') = (l \<in> {m..n}) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>consec (Views.lan v) lanu\<close> \<open>continuous (Views.lan v)\<close> \<open>continuous lanu\<close> \<open>lan1 = Views.lan v \<squnion> lanu\<close> \<open>maximum lan1 = maximum (Views.lan v) + (maximum (Views.lan v') - maximum (Views.lan v))\<close> \<open>minimum lan1 = minimum (Views.lan v')\<close> consec_un_equality continuos_atLeastAtMost empty_continuous max_rel nchop_def sup_bot.left_neutral v'_notE) 
      then show ?thesis using chop1 chop2 
        by (metis (mono_tags, hide_lams) Rep_view_inverse assm equality ext.rep_eq lan.rep_eq nat_int.nchop_def old.unit.exhaust own.rep_eq select_convs(1) select_convs(2) select_convs(3) sup_bot.left_neutral v1 vertical_chop_empty_up)
    next
      case d
      then have ge:\<open>?diff_min > 0\<close> using 2 by blast
      have min_less:"minimum ?lanv' + ?diff_min > minimum ?lanv' " 
        using ge by linarith
      have ge2:\<open>?diff_max > 0\<close> using 2 d by blast
      have max_less:"maximum ?lanv < maximum ?lanv + ?diff_max" 
        using ge2 by linarith
      have land_notE:"land \<noteq> \<emptyset>" using min_less land_rep 
        by (metis "1"  Suc_diff_1  all_not_in_conv d  card_atLeastAtMost card_empty diff_is_0_eq' le_add_diff_inverse less_imp_diff_less min min_rel non_empty_elem_in  )
      then have 3:"minimum land = minimum ?lanv'" using land_rep nat_int_atLeastAtMost_min 
        by (metis One_nat_def )
      have lan1_notE: "lan1 \<noteq> \<emptyset>" using lan1_rep False  
        using False assm bot_nat_int.rep_eq lan1_rep less_eq_nat_int.rep_eq nat_int.minimum_in v'_rep by fastforce 
      have lanu_notE: "lanu \<noteq> \<emptyset>" using lanu_rep max_less 
        using bot_nat_int.rep_eq  by auto
      have "maximum land = minimum ?lanv' + ?diff_min -1" using land_rep land_notE nat_int_atLeastAtMost_max 
        by blast
      then have 4:"maximum land + 1= minimum ?lanv" using ge by linarith
      have consec:"consec land ?lanv" using 4 
        by (simp add: False consec_def land_notE)
      have 3: "minimum ?lanv = minimum lan1" using lan1_rep nat_int_atLeastAtMost_min lan1_notE   
        by simp
      have 4:"maximum ?lanv + 1 = minimum lanu" using lanu_rep  nat_int_atLeastAtMost_max nat_int_atLeastAtMost_min 
        by (metis  Suc_eq_plus1 Suc_leI    atLeastAtMost_iff     le_eq_less_or_eq max_less max_rel  non_empty_elem_in  order_trans  )
      have "maximum lan1 = maximum ?lanv + ?diff_max" using lan1_rep nat_int_atLeastAtMost_max  
        by (metis "3" "4" False atLeastAtMost_iff       consec_def consec_lesser     lanu_rep  less_imp_le_nat less_not_refl max  minimum_in non_empty_elem_in    order_refl order_trans  )
      have "maximum lanu = maximum ?lanv' " using lanu_rep nat_int_atLeastAtMost_max 
        using lanu_notE max_rel by auto
      have 5:"maximum lan1 = maximum lanu" 
        using \<open>maximum lan1 = maximum (Views.lan v) + (maximum (Views.lan v') - maximum (Views.lan v))\<close> \<open>maximum lanu = maximum (Views.lan v')\<close> max_rel by auto
      have 6:"maximum lan1 = maximum ?lanv'" 
        using \<open>maximum lan1 = maximum (Views.lan v) + (maximum (Views.lan v') - maximum (Views.lan v))\<close> max_rel by auto
     
      have "consec ?lanv lanu" 
        using "4" False \<open>lanu \<noteq> bot\<close> consec_def by blast
      have "lan1 = lan v \<squnion> lanu" using lan1_rep lanu_rep v'_rep 3 4 5 
        by (metis \<open>consec (Views.lan v) lanu\<close>  cont1 contu contv consec_un_equality consec_un_max consec_un_min lan1_notE)
      have cont_un1:"continuous (lan v \<squnion> lanu)" 
        using \<open>lan1 = Views.lan v \<squnion> lanu\<close> cont1 by auto
      have chop1:"N_Chop(lan1, ?lanv, lanu)" 
        using \<open>consec (Views.lan v) lanu\<close> \<open>continuous (Views.lan v)\<close> \<open>continuous lanu\<close> \<open>lan1 = Views.lan v \<squnion> lanu\<close> nchop_def by blast
      have consec2:"consec land lan1" 
        using "3" \<open>lan1 = Views.lan v \<squnion> lanu\<close> consec consec_def by auto 
      then have "continuous (land \<squnion> lan1)" 
        using  cont1 contd nchop_cont nchop_def by blast
      then have "?lanv' = land \<squnion> lan1" using consec2 cont1 v'_rep 3 5 6 v'_notE continuous_min_max
         by (metis (no_types, hide_lams) \<open>maximum lan1 = maximum (Views.lan v) + (maximum (Views.lan v') - maximum (Views.lan v))\<close> bot_eq_sup_iff consec_un_max consec_un_min continuous_nonE_atLeastAtMost land_notE land_rep nat_int_atLeastAtMost_min)
      then have chop2:"N_Chop(?lanv', land, lan1)" 
        using  cont1 contd nchop_def view.horizontal_chop_empty_left view.horizontal_chop_lanes_continuous 
        consec2 by blast
      obtain vu where vu:"vu= \<lparr> basic_view.ext = ext v, lan = lanu, own =own v\<rparr>"
        by blast
      obtain v1 where v1:"v1 = \<lparr> basic_view.ext = ext v, lan = lan1, own = own v\<rparr>"
        by blast
      obtain vd where vd:"vd =  \<lparr> basic_view.ext = ext v, lan = land, own =own v\<rparr>"
        by blast
      have 7:"(Abs_view v1)=v--(Abs_view vu)" using chop1 vu v1 Abs_view_inverse vchop_def ext.rep_eq own.rep_eq 
        by (simp add: cont1 contu lan.rep_eq)
      have 8:"v'=(Abs_view vd)-- (Abs_view v1)" using chop2 v1 vd 
        by (simp add: Abs_view_inverse assm eq_onp_same_args ext.abs_eq lan.rep_eq nchop_def own.abs_eq view.vchop_def) 
      then have "(v'=(Abs_view vd)--(Abs_view v1)) \<and> ((Abs_view v1)=v--(Abs_view vu))" 
        using "7" by blast
      then show ?thesis by blast
    qed
  qed
qed

lemma somewhere_leq:
  "v \<le> v' \<longleftrightarrow> (\<exists>v1 v2 v3 vl vr vu vd. 
                (v'=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu))" 
proof
  assume "v \<le> v'"
  then obtain v'' where v'':" (ext v'' \<le> ext v') \<and> (lan v'' = lan v') \<and> (own v'' = own v') \<and> (ext v = ext v'') \<and> (lan v \<sqsubseteq> lan v'') \<and> (own v = own v'')" using
      horizontal_intermed by blast
  then have 1:"(\<exists>v1 vl vr. (v'=vl\<parallel>v1) \<and> (v1=v''\<parallel>vr))"  using horizontal_leq  by blast
  from v'' have 2:"\<exists>v2 vd vu. (v''=vd--v2) \<and> (v2=v--vu)"  using vertical_leq by blast
  from 1 and 2 show "(\<exists>v1 v2 v3 vl vr vu vd. 
                (v'=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu))" by blast
next
  assume 
    "\<exists>v1 v2 v3 vl vr vu vd. (v'=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu)"
  then obtain v1 v2 v3 vl vr vu vd 
    where " (v'=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v--vu)" by blast
  then show "v \<le> v'" 
    by (meson horizontal_chop_leq1 horizontal_chop_leq2 order_trans vertical_chop_leq1
        vertical_chop_leq2)
qed
  

text\<open>The switch relation is compatible with the chopping relations, in the 
following sense. If we can chop a view \(v\) into two subviews \(u\) and
\(w\), and we can reach \(v^\prime\) via the switch relation, then
there also exist two subviews \(u^\prime\), \(w^\prime\) of \(v^\prime\),
such that \(u^\prime\) is reachable from \(u\) (and respectively for \(w^\prime\), \(w\)).
\<close>
  (* switch lemmas *)
lemma switch_unique:"(v =c> u) \<and> (v =c> w) \<longrightarrow>u = w"
  using switch_def 
  using Rep_view_inject ext.rep_eq lan.rep_eq own.rep_eq by fastforce
    
lemma switch_exists:"\<exists>c u.( v=c>u)"
  using switch_def by auto
    
lemma switch_always_exists:" \<exists>u. (v=c>u)" 
proof - 
  obtain u where "u = Abs_view \<lparr> basic_view.ext = ext v, lan = lan v, own = c\<rparr>" by simp
  then have "v=c>u" 
    using Abs_view_inverse Rep_view ext.rep_eq lan.rep_eq own.rep_eq view.switch_def by auto
  then show ?thesis by blast
qed

lemma switch_origin:" \<exists>u. (u=(own v)>v)" 
  using switch_def  by auto
    
lemma switch_refl:"(v=(own v)>v)"
  by (simp add:switch_def)
    
lemma switch_symm:"(v=c>u) \<longrightarrow> (u=(own v)>v)" 
  by (simp add:switch_def)
    
lemma switch_trans:"(v=c>u) \<and> (u=d>w) \<longrightarrow> (v=d>w)"
  by (simp add: switch_def)
    
lemma switch_triangle:"(v=c>u) \<and> (v=d>w) \<longrightarrow> (u=d>w)"
  using switch_def by auto
    
lemma switch_hchop1:
  "(v=v1\<parallel>v2) \<and> (v=c>v') \<longrightarrow>
     (\<exists> v1' v2'. (v1 =c> v1') \<and> (v2 =c> v2') \<and> (v'=v1'\<parallel>v2'))"  
  by (metis (no_types, hide_lams) select_convs view.hchop_def view.switch_def)
    
lemma switch_hchop2:
  "(v'=v1'\<parallel>v2') \<and> (v=c>v') \<longrightarrow> 
      (\<exists> v1 v2. (v1 =c> v1') \<and> (v2 =c> v2') \<and> (v=v1\<parallel>v2))"
  by (metis (no_types, hide_lams) select_convs view.hchop_def view.switch_def)
    
lemma switch_vchop1:
  "(v=v1--v2) \<and> (v=c>v') \<longrightarrow> 
      (\<exists> v1' v2'. (v1 =c> v1') \<and> (v2 =c> v2') \<and> (v'=v1'--v2'))"
  by (metis (no_types, hide_lams) select_convs view.vchop_def view.switch_def)
    
lemma switch_vchop2:
  "(v'=v1'--v2') \<and> (v=c>v') \<longrightarrow>
       (\<exists> v1 v2. (v1 =c> v1') \<and> (v2 =c> v2') \<and> (v=v1--v2))"
  by (metis (no_types, hide_lams) select_convs view.vchop_def view.switch_def)
    
lemma switch_leq:"u' \<le> u \<and> (v=c>u) \<longrightarrow> (\<exists>v'. (v'=c>u') \<and> v' \<le> v)" 
proof 
  assume assm: "u' \<le> u \<and> (v=c>u)"
(*  then have more_eq:"more v = more u" 
    using view.switch_def by blast*)
  then obtain v' where v'_def:"v'= Abs_view \<lparr> basic_view.ext =ext u', lan = lan u', own = own v\<rparr>"
    by blast
  have ext:"ext v' \<le> ext v" using assm switch_def 
    using Abs_view_inverse Rep_view ext.rep_eq lan.rep_eq less_eq_view_def v'_def by auto 
  have lan:"lan v' \<le> lan v" using assm switch_def 
    using Abs_view_inverse Rep_view ext.rep_eq lan.rep_eq less_eq_view_def v'_def by auto 
  have less: "v' \<le> v" using less_eq_view_def ext lan  v'_def 
    using Abs_view_inverse Rep_view lan.rep_eq own.rep_eq by auto 
  have switch:"v' =c> u'" using v'_def switch_def assm 
    using Abs_view_inverse Rep_view lan.rep_eq own.rep_eq 
    by (simp add: ext.rep_eq less_eq_view_def)
    show  "(\<exists>v'. ( v' = c > u') \<and> v' \<le> v)" using switch less by blast
qed
end
end
