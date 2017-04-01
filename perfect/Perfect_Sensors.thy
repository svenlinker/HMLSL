theory Perfect_Sensors
  imports  "../HMLSL"
    begin

  definition perfect::"cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
  where "perfect e ts c \<equiv> traffic.physical_size ts c + traffic.braking_distance ts c " 

locale perfect_sensors = traffic+view
  begin
interpretation sensors : sensors "perfect :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
proof unfold_locales
  fix e ts c
  show " 0 < perfect e ts c" 
    by (metis less_add_same_cancel2 less_trans perfect_def traffic.psGeZero traffic.sdGeZero)

qed
  print_facts
print_locale!perfect_sensors
  
notation local.sensors.space ("space")
notation local.sensors.len ("len")
(*notation traffic.move ("move")
notation restriction.restrict ("restrict")
notation traffic.res ("res")  
notation traffic.clm ("clm")  
notation traffic.pos ("pos")  
notation traffic.dyn ("dyn")  
notation traffic.braking_distance ("braking'_distance")  
notation traffic.physical_size ("physical'_size")  
  *)
  
lemma "pos ts = pos ts' \<and> braking_distance ts = braking_distance ts' \<and> physical_size ts= physical_size ts' 
        \<longrightarrow> space ts v c = space ts' v c"  
proof
  assume assm:"pos ts = pos ts' \<and> braking_distance ts = braking_distance ts' \<and> physical_size ts= physical_size ts'"  
  then have left:"left (space ts v c) = left (space ts' v c)" using local.sensors.space_nonempty Abs_real_int_inverse 
    by (smt CollectI fst_conv left.rep_eq local.sensors.sensors_ge snd_conv local.sensors.space_def)
  from assm have "\<forall>e. perfect e ts c = perfect e ts' c" using perfect_def 
    by simp
  hence " perfect (own v) ts c = perfect (own v) ts' c" by simp
  then have "pos ts c  + perfect (own v) ts c = pos ts' c + perfect (own v) ts' c" using assm by simp
  with assm have right:"right (space ts v c) = right (space ts' v c)" using Abs_real_int_inverse fst_conv snd_conv local.sensors.space_def  right.rep_eq
  by simp
  from left and right show "space ts v c = space ts' v c" 
    by (simp add: dual_order.antisym less_eq_real_int_def)
qed
    
lemma create_reservation_length_stable:"(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts') \<longrightarrow> (len v ts c) = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c" 
    using traffic.create_reservation_def local.sensors.space_def braking_distance_def physical_size_def perfect_def 
      by simp
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: local.sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: local.sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: local.sensors.len_def)
    qed
  qed
qed
  
lemma create_claim_length_stable:"(ts\<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c"
    using traffic.create_claim_def sensors.space_def perfect_def 
    by (simp )
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: local.sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: local.sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: local.sensors.len_def)
    qed
  qed
qed
  
lemma withdraw_reservation_length_stable:"(ts\<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c"
    using traffic.withdraw_reservation_def sensors.space_def perfect_def 
    by (simp)

  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: local.sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: sensors.len_def)
    qed
  qed
qed
  
lemma withdraw_claim_length_stable:"(ts\<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c" 
        using traffic.withdraw_claim_def sensors.space_def perfect_def 
    by simp
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: sensors.len_def)
    qed
  qed
qed
  
  lemma all_own_ext_eq_len_eq:"ext v = ext v'  \<longrightarrow> len v ( ts) c = len v' ( ts) c"
proof
  assume assm:"ext v = ext v'"
  hence sp:"space ts v c = space ts v' c" 
    by (simp add: perfect_def  sensors.space_def)
  have left_eq:"left (ext v) = left (ext v')" using assm by simp
  have right_eq:"right (ext v) = right (ext v')" using assm by simp
  show "len v ( ts) c = len v' ( ts) c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts v) c) > right (ext v')" using right_eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: sensors.len_def right_eq assm sp)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts v) c) > right (ext v')" using right_eq by simp
    show "len v ( ts) c = len v' ( ts) c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v') > right ((space ts v) c) "using left_eq by simp
      from outside_left and outside_left' show ?thesis using sensors.len_def left_eq sp 
          right_eq by auto
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v') > right ((space ts v) c) " using left_eq by simp
      from inside_left inside_right inside_left' inside_right' left_eq right_eq
      show ?thesis by (simp add:sensors.len_def sp)
    qed
  qed
qed
  (* switch lemmas *)
lemma switch_length_stable:"(v=c>v') \<longrightarrow> len v ts c = len v' ts c"
  using all_own_ext_eq_len_eq view.switch_def by blast
     

lemma arbitrary_switch_length_stable:"(v=d>v') \<longrightarrow> len v ts c = len v' ts c"
  using all_own_ext_eq_len_eq view.switch_def by blast
  
end
  end