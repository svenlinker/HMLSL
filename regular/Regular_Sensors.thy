theory Regular_Sensors
  imports  "../HMLSL"
    begin

definition regular::"cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
  where "regular e ts c \<equiv> if (e = c) then traffic.physical_size ts c + traffic.braking_distance ts c 
                                    else traffic.physical_size ts c "  

locale regular_sensors = traffic + view
begin
  
  
interpretation regular_sensors: sensors "regular :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real " 
proof unfold_locales
  fix e ts c
    show " 0 < regular e ts c" 
      by (metis (no_types, hide_lams) less_add_same_cancel2 less_trans regular_def traffic.psGeZero traffic.sdGeZero)
qed        
  

notation regular_sensors.space ("space")
notation regular_sensors.len ("len")
(*notation regular_sensors.move ("move")
notation restriction.restrict ("restrict") *)
(*notation traffic.res ("res")  
notation traffic.clm ("clm")  
notation traffic.pos ("pos")  
notation traffic.dyn ("dyn")  
notation traffic.braking_distance ("braking_distance")  
notation traffic.physical_size ("physical_size")  
  *)
lemma create_reservation_length_stable:"(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c" 
    using traffic.create_reservation_def sensors.space_def regular_def 
    by (simp add:  regular_sensors.sensors_axioms)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: regular_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: regular_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: regular_sensors.len_def)
    qed
  qed
qed
  
lemma create_claim_length_stable:"(ts\<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c"
    using traffic.create_claim_def sensors.space_def regular_def  
    by (simp add: regular_sensors.sensors_axioms)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: regular_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: regular_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: regular_sensors.len_def)
    qed
  qed
qed
  
lemma withdraw_reservation_length_stable:"(ts\<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c"
    using traffic.withdraw_reservation_def sensors.space_def regular_def
    by (simp add: regular_sensors.sensors_axioms)

  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: regular_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: regular_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: regular_sensors.len_def)
    qed
  qed
qed
  
lemma withdraw_claim_length_stable:"(ts\<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c" 
        using traffic.withdraw_claim_def sensors.space_def regular_def  
    by (simp add: regular_sensors.sensors_axioms)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: regular_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: regular_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: regular_sensors.len_def)
    qed
  qed
qed
  
lemma sensors_le:"e \<noteq> c \<longrightarrow> regular e ts c < regular c ts c"
using  traffic.sdGeZero by (simp add: regular_def) 

  
lemma sensors_leq:" regular e ts c \<le> regular c ts c"
using regular_def using sensors_le traffic.sdGeZero traffic.psGeZero 
by smt

  
lemma space_eq: "own v = own v' \<longrightarrow> space ts v c = space ts v' c" using regular_sensors.space_def sensors_def by auto
  
lemma switch_space_le:"(own v) \<noteq> c \<and> (v=c>v') \<longrightarrow> space ts v c < space ts v' c" 
proof
  assume assm:"(own v) \<noteq> c \<and> (v=c>v')"
  hence sens:"regular (own v) ts c < regular (own v') ts c" using sensors_le view.switch_def  by auto
  then have le:"pos ts c + regular (own v) ts c < pos ts c + regular (own v') ts c" by auto     
  have left_eq:"left (space ts v c) = left (space ts v' c)" using regular_sensors.left_space by auto 
  have r1:"right (space ts v c ) = pos ts c + regular (own v) ts c" 
    using regular_sensors.right_space  by auto      
  have r2:"right (space ts v' c ) = pos ts c + regular (own v') ts c" 
    using regular_sensors.right_space  by auto      
  then have "right (space ts v c) < right( space ts v' c)" using r1 r2 le by auto 
      
  then have "((left (space ts v' c)) \<ge> left (space ts v c) ) \<and> ((right (space ts v c) \<le> right( space ts v' c))) 
                                  \<and>  \<not>((left (space ts v c) \<ge> left (space ts v' c) ) \<and> (right (space ts v' c) \<le> right (space ts v c)))" 
  using regular_sensors.left_space left_eq by auto
  then show "space ts v c < space ts v' c" using less_real_int_def 
    using left_eq by auto    
qed

lemma switch_space_leq:"(v=c>v') \<longrightarrow> space ts v c \<le> space ts v' c"
by (metis less_imp_le order_refl switch_space_le view.switch_refl view.switch_unique)

  
end
end  