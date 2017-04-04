(*  Title:      Move.thy
    Author:     Sven Linker

  The move function shifts a view by the difference in position of the owner of the view.
  The lanes and owner itself are not changed.

*)

section\<open>Move a View according to Difference between Traffic Snapshots\<close>
theory Move
  imports Traffic Views
begin
  
context traffic 
begin  
lemmas[simp] = shift_dict
  
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
  then show "move ts' ts'' (move ts ts' v) = move ts ts'' v" using real_int.shift_additivity move_dict shift_dict 
    by (smt  move_def  select_convs(1))
qed
  
lemma move_stability_res:"(ts\<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v" 
  and move_stability_clm: "(ts\<^bold>\<midarrow>c(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v"
  and move_stability_wdr:"(ts\<^bold>\<midarrow>wdr(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v"
  and move_stability_wdc:"(ts\<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v"
  using create_reservation_def create_claim_def withdraw_reservation_def
    withdraw_claim_def move_def move_nothing 
  by (auto)+

end
  
lemmas[simp] = move_dict
  
end