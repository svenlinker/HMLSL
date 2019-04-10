(*  Title:      Move.thy
    Author:     Sven Linker

  The move function shifts a view by the difference in position of the owner of the view.
  The lanes and owner itself are not changed.

*)

section\<open>Move a View according to Difference between Traffic Snapshots\<close>
text \<open>
In this section, we define a function to move a view according
to the changes between two traffic snapshots. The intuition is
that the view moves with the same speed as its owner. That is,
if we move a view \(v\) from \(ts\) to \(ts^\prime\), we 
shift the extension of the view by the difference in the
position of the owner of \(v\).
\<close>


theory Move
  imports Traffic Views
begin

context view 
begin  

notation traffic.abstract ("_ \<^bold>\<Rightarrow> _") 
notation traffic.pos ("pos")
notation traffic.create_claim ("_ \<^bold>\<midarrow>c'( _, _ ') \<^bold>\<rightarrow> _" 27)
notation traffic.withdraw_claim ("_ \<^bold>\<midarrow>wdc'(  _ ') \<^bold>\<rightarrow> _" 27)
notation traffic.create_reservation ("_ \<^bold>\<midarrow>r'(  _ ') \<^bold>\<rightarrow> _" 27)
notation traffic.withdraw_reservation ("_ \<^bold>\<midarrow>wdr'( _, _ ') \<^bold>\<rightarrow> _" 27)



definition move::"traffic \<Rightarrow> traffic \<Rightarrow> view \<Rightarrow> view"
  where 
    "move ts ts' v = vshift v ((traffic.pos ts' (own v)) - traffic.pos ts (own v))"

lemma move_keeps_length:"\<parallel>ext v\<parallel> = \<parallel>ext (move ts ts' v)\<parallel>" 
  by (simp add: view.move_def view.vshift_ext_len_stab)

lemma move_keeps_lanes:"lan v = lan (move ts ts' v)" by (simp add: move_def view.vshift_lan_stab)  

lemma move_keeps_owner:"own v = own (move ts ts' v)" by (simp add: move_def view.vshift_own_stab)

lemma move_nothing :"move ts ts v = v" using real_int.shift_zero move_def by (simp add: vshift_zero)

lemma move_trans:
  "(ts \<^bold>\<Rightarrow> ts') \<and> (ts' \<^bold>\<Rightarrow>ts'') \<longrightarrow> (move ts' ts'' (move ts ts' v) = move ts ts'' v)" 
proof
  assume assm:"(ts \<^bold>\<Rightarrow> ts') \<and> (ts' \<^bold>\<Rightarrow>ts'')"
  have 
    "(pos ts'' (own v)) - pos ts (own v) 
      = (pos ts'' (own v) + pos ts' (own v)) - ( pos ts (own v) + pos ts' (own v))"
    by simp
  then show "(move ts' ts'' (move ts ts' v) = move ts ts'' v)" using vshift_additivity 
    using own.rep_eq view.move_def view.vshift_own_stab by auto
qed

lemma move_stability_res:"(ts\<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v" 
  and move_stability_clm: "(ts\<^bold>\<midarrow>c(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v"
  and move_stability_wdr:"(ts\<^bold>\<midarrow>wdr(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v"
  and move_stability_wdc:"(ts\<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow>ts') \<longrightarrow> move ts ts' v = v"
  using traffic.create_reservation_def traffic.create_claim_def traffic.withdraw_reservation_def
    traffic.withdraw_claim_def move_def move_nothing 
  by (auto)+

end
end
