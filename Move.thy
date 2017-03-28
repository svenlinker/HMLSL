theory Move
  imports Abstract_Model Views
begin
  (*
  The move function shifts a view by the difference in position of the owner of the view.
  The lanes and owner itself are kept.
*)
context traffic 
begin  
definition move::"traffic \<Rightarrow> traffic \<Rightarrow> view \<Rightarrow> view"
where "move ts ts' v = \<lparr> ext = shift (ext v) ((pos ts' (own v)) - pos ts (own v)), lan = lan v, own =own v \<rparr>"

lemma move_keeps_length:"\<parallel>ext v\<parallel> = \<parallel>ext (move ts ts' v)\<parallel>"
using real_int.shift_keeps_length by (simp add: move_def)

lemma move_keeps_lanes:"lan v = lan (move ts ts' v)" using move_def by simp

lemma move_keeps_owner:"own v = own (move ts ts' v)" using move_def by simp

lemma move_nothing :"move ts ts v = v" using real_int.shift_zero move_def by simp

lemma move_trans:"(ts \<^bold>\<Rightarrow> ts') \<and> (ts' \<^bold>\<Rightarrow>ts'') \<longrightarrow> move ts' ts'' (move ts ts' v) = move ts ts'' v"
proof
  assume assm:"(ts \<^bold>\<Rightarrow> ts') \<and> (ts' \<^bold>\<Rightarrow>ts'')"
  have "(pos ts'' (own v)) - pos ts (own v) = (pos ts'' (own v) + pos ts' (own v)) - ( pos ts (own v) + pos ts' (own v))"
    by simp
  have "move ts' ts'' (move ts ts' v) =
 \<lparr> ext = shift (ext (move ts ts' v)) (pos ts'' (own (move ts ts' v)) - pos ts' (own (move ts ts' v))),
  lan = lan (move ts ts' v), own = own (move ts ts' v) \<rparr> " using move_def by blast
  hence "move ts' ts'' (move ts ts' v) = 
 \<lparr> ext = shift (ext (move ts ts' v)) (pos ts'' (own v) - pos ts' (own  v)),
  lan = lan  v, own = own  v \<rparr> " using move_def by simp
  thus "move ts' ts'' (move ts ts' v) = move ts ts'' v" using real_int.shift_additivity 
    by (smt  move_def select_convs(1))
qed

lemma move_stability_res:"(ts\<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v" 
  and move_stability_clm: "(ts\<^bold>\<midarrow>c(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v"
  and move_stability_wdr:"(ts\<^bold>\<midarrow>wdr(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v"
  and move_stability_wdc:"(ts\<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v"
using create_reservation_def create_claim_def withdraw_reservation_def
  withdraw_claim_def move_def move_nothing 
by (auto)+

(*  
lemma switch_move: "(V=c>V') \<longrightarrow> (\<exists> V'' . ((move ts ts' V)=c>V''))"
proof
  assume assm:" (V=c>V')"
  obtain V'' where v''_def:"V'' = \<lparr> ext = shift (ext V) ((pos ts' (own V)) - pos ts (own V)), 
                                    lan = lan V,
                                    own = c \<rparr>" by blast
  have c1:"((move ts ts' V)=c>V'')" using assm v''_def by (simp add: move_def switch_def)
  thus "\<exists> V'' . ((move ts ts' V)=c>V'')" by rule
qed
*)
end
  end