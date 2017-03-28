(*  Title:      MLSL/Safety_p.thy
    Author:     Sven Linker, University of Liverpool
    Copyright   2016

    Safety for MLSL with perfect knowledge of cars.
*)

theory Safety_p
imports MLSL_p
begin
  
context mlsl_perfect
  begin

abbreviation safe::"cars\<Rightarrow>\<sigma>" 
where "safe e \<equiv> \<^bold>\<not>( \<^bold>\<exists> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle>re(c) \<^bold>\<and> re(e) \<^bold>\<rangle>)" 

abbreviation DC::"\<sigma>"
where "DC \<equiv> \<^bold>G ( \<^bold>\<forall> c d. \<^bold>\<not>(c \<^bold>= d) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<tau> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>)"

abbreviation pcc::"cars \<Rightarrow> cars \<Rightarrow> \<sigma>" 
where "pcc c d \<equiv> \<^bold>\<not> (c \<^bold>= d) \<^bold>\<and> \<^bold>\<langle> cl(d) \<^bold>\<and> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<rangle>"

abbreviation LC::"\<sigma>"
where "LC \<equiv> \<^bold>G ( \<^bold>\<forall>d.( \<^bold>\<exists> c. pcc c d) \<^bold>\<rightarrow> \<^bold>\<box>r(d) \<^bold>\<bottom>)  "



theorem safety:"\<Turnstile>( \<^bold>\<forall>e. safe e ) \<^bold>\<and> DC \<^bold>\<and> LC \<^bold>\<rightarrow> \<^bold>G (\<^bold>\<forall> e. safe e)"
proof (rule allI)+
  fix ts v
    show "ts,v \<Turnstile>( \<^bold>\<forall>e. safe e ) \<^bold>\<and> DC \<^bold>\<and> LC \<^bold>\<rightarrow> \<^bold>G (\<^bold>\<forall> e. safe e)"
    proof
      assume assm:"ts,v \<Turnstile> ( \<^bold>\<forall>e. safe e ) \<^bold>\<and> DC \<^bold>\<and> LC"
      from assm have init:"ts,v \<Turnstile> ( \<^bold>\<forall>e. safe e )" by simp
      from assm have DC :"ts,v \<Turnstile> DC" by simp
      from assm have LC: "ts,v \<Turnstile> LC" by simp
      show "ts,v \<Turnstile>  \<^bold>G (\<^bold>\<forall> e. safe e)"
      proof  
        fix ts'
        show "(ts \<^bold>\<Rightarrow> ts') \<longrightarrow> (ts',move ts ts' v \<Turnstile> (\<^bold>\<forall> e. safe e))"
        proof 
          assume abs:"(ts \<^bold>\<Rightarrow> ts')"
          show "ts',move ts ts' v \<Turnstile> (\<^bold>\<forall> e. safe e)" using abs
          proof (induct ts\<equiv>"ts" ts'\<equiv>ts' arbitrary:ts'  rule:abstract.induct )
          print_cases
          case (refl ) 
            have "move ts ts v = v" using move_nothing by simp
            thus ?case using init move_nothing by simp
          next
          case (evolve ts' ts'' )
            have local_DC:"ts',move ts ts' v \<Turnstile> \<^bold>\<forall> c d. \<^bold>\<not>(c \<^bold>= d) \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<tau> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(d)\<^bold>\<rangle>"
              using evolve.hyps DC by simp
           show ?case 
           proof (rule ccontr)
            assume "\<not> (ts'',move ts ts'' v \<Turnstile> \<^bold>\<forall>e. safe(e))"
            hence contra:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<exists> e. \<^bold>\<not> safe(e)" by blast
            from this obtain e where e_def:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<not> safe(e)" by blast
            hence unsafe:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<exists> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
            from this obtain c where c_def:"ts'',move ts ts'' v \<Turnstile>  \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
            from evolve.hyps  and c_def have 
              ts'_safe:"ts',move ts ts' v \<Turnstile> \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
            hence no_coll_after_evol:"ts',move ts ts' v \<Turnstile> \<^bold>\<box>\<^bold>\<tau> \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" using local_DC by blast
            have move_eq:"move ts' ts'' (move ts ts' v) = move ts ts'' v" using "evolve.hyps" 
              abstract.evolve abstract.refl move_trans by blast
            from no_coll_after_evol and evolve.hyps have "ts'',move ts' ts'' (move ts ts' v) \<Turnstile>  \<^bold>\<not>\<^bold>\<langle>re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"  
              by blast
            thus False using c_def using  move_eq by fastforce
          qed
        next
        case (cr_res ts' ts'')
          have local_LC: "ts',move ts ts' v \<Turnstile>( \<^bold>\<forall>d.( \<^bold>\<exists> c. pcc c d) \<^bold>\<rightarrow> \<^bold>\<box>r(d) \<^bold>\<bottom>)  " 
            using LC cr_res.hyps by blast
          have "move ts ts' v = move ts' ts'' (move ts ts' v)" using move_stability_res cr_res.hyps move_trans 
            by auto
          hence move_stab: "move ts ts' v = move ts ts'' v" by (metis abstract.simps cr_res.hyps(1) cr_res.hyps(3) move_trans)
          show ?case 
          proof (rule ccontr)
            assume "\<not> (ts'',move ts ts'' v \<Turnstile> \<^bold>\<forall>e. safe(e))"
            hence contra:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<exists> e. \<^bold>\<not> safe(e)" by blast
            from this obtain e where e_def:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<not> safe(e)" by blast
            hence unsafe:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<exists> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
            from this obtain c where c_def:"ts'',move ts ts'' v \<Turnstile>  \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
            obtain d where d_def: "ts' \<^bold>\<midarrow>r(d) \<^bold>\<rightarrow> ts''" using cr_res.hyps by blast
            have c_neq_e:"c \<noteq>e" 
            proof (rule ccontr)
              assume "\<not> c \<noteq> e"
              hence "c = e" by blast
              then have "ts'',v \<Turnstile> c \<^bold>= e" by simp
              thus False using c_def by blast
            qed
            have "d = e \<or> d \<noteq> e" by simp
            thus False
            proof
              assume eq:"d = e"
              hence e_trans:"ts' \<^bold>\<midarrow>r(e) \<^bold>\<rightarrow> ts''" using d_def by simp
              from c_def have "ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by auto
              hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" using somewhere_leq   
                by meson
              from this obtain v' where v'_def:"(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" by blast
              with backwards_res_act have "ts',v' \<Turnstile>   re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e))"
                using c_def  backwards_res_stab c_neq_e 
                by (metis (no_types, lifting) d_def eq)
              hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts',v' \<Turnstile> re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e)))"  
                using  v'_def by blast
              hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<langle> re(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e)) \<^bold>\<rangle>" using somewhere_leq by meson
              hence "ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle> " 
                using somewhere_and_or_distr by blast 
              thus False 
              proof
                assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
                have "ts',move ts ts' v \<Turnstile> \<^bold>\<not> (c \<^bold>= e)" using c_def by blast
                thus False using assm' cr_res.hyps c_def move_stab by force
              next
                assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle>"
                hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> cl(e)\<^bold>\<rangle>" using c_def by force
                hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> cl(e) \<^bold>\<and> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<rangle>" by blast
                hence pcc:"ts',move ts ts'' v \<Turnstile> pcc c e" by blast
                have "ts',move ts ts'' v \<Turnstile>( \<^bold>\<exists> c. pcc c e) \<^bold>\<rightarrow> \<^bold>\<box>r(e) \<^bold>\<bottom>  " 
                using local_LC move_stab by fastforce
                hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<box>r(e) \<^bold>\<bottom>" using pcc by blast
                thus "ts'',move ts ts'' v \<Turnstile> \<^bold>\<bottom>" using e_trans by blast
              qed
            next 
              assume neq:"d \<noteq> e"
              have "c=d \<or> c \<noteq> d" by simp
              thus False 
              proof
                assume neq2:"c \<noteq> d" 
                from c_def have "ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by auto
                hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" using somewhere_leq   
                  by meson
                from this obtain v' where v'_def:"(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" by blast
                with backwards_res_stab have overlap: "ts',v' \<Turnstile>   re(c) \<^bold>\<and> (re(e))"
                  using c_def  backwards_res_stab c_neq_e neq2 
                  by (metis (no_types, lifting) d_def neq)
                hence unsafe2:"ts',move ts ts'' v \<Turnstile>\<^bold>\<not> safe(e)" 
                  using  c_neq_e somewhere_leq v'_def by blast
                from cr_res.hyps have "ts',move ts ts'' v \<Turnstile> safe(e)" using move_stab by force
                thus False using unsafe2 by auto
              next
                assume eq2:"c = d"
                hence e_trans:"ts' \<^bold>\<midarrow>r(c) \<^bold>\<rightarrow> ts''" using d_def by simp
                from c_def have "ts'',move ts ts'' v \<Turnstile> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by auto
                hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" using somewhere_leq   
                  by meson
                from this obtain v' where v'_def:"(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" by blast
                with backwards_res_act have "ts',v' \<Turnstile>   (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> (re(e) )"
                  using c_def  backwards_res_stab c_neq_e 
                  by (metis (no_types, lifting) d_def eq2)
                hence "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts',v' \<Turnstile> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> (re(e)))"  using v'_def by blast
                hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<langle> (re(c) \<^bold>\<or> cl(c)) \<^bold>\<and> (re(e) ) \<^bold>\<rangle>" using somewhere_leq by meson
                hence "ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle> " 
                  using somewhere_and_or_distr  by blast 
                thus False 
                proof
                  assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
                  have "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> (c \<^bold>= e)" using c_def by blast
                  thus False using assm' cr_res.hyps c_def move_stab by fastforce
                next
                 assume assm':"ts',move ts ts'' v \<Turnstile>  \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle>"
                 hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> cl(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" using c_def by blast
                 hence "ts',move ts ts'' v \<Turnstile>\<^bold>\<not> (c \<^bold>=e) \<^bold>\<and> \<^bold>\<langle> cl(c) \<^bold>\<and> (re(e) \<^bold>\<or> cl(e)) \<^bold>\<rangle>" by blast
                 hence pcc:"ts',move ts ts'' v \<Turnstile> pcc e c" by blast
                 have "ts',move ts ts'' v \<Turnstile>( \<^bold>\<exists> d. pcc d c) \<^bold>\<rightarrow> \<^bold>\<box>r(c) \<^bold>\<bottom>  " using local_LC move_stab by fastforce
                 hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<box>r(c) \<^bold>\<bottom>" using pcc by blast
                 thus "ts'',move ts ts'' v \<Turnstile> \<^bold>\<bottom>" using e_trans by blast
               qed
             qed
           qed
         qed
         next 
           case (cr_clm ts' ts'')
           have "move ts ts' v = move ts' ts'' (move ts ts' v)" using move_stability_clm cr_clm.hyps move_trans 
           by auto
          hence move_stab: "move ts ts' v = move ts ts'' v" by (metis abstract.simps cr_clm.hyps(1) cr_clm.hyps(3) move_trans)
           show ?case 
            proof (rule ccontr)
              assume "\<not> (ts'',move ts ts'' v \<Turnstile> \<^bold>\<forall>e. safe(e))"
              hence contra:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<exists> e. \<^bold>\<not> safe(e)" by blast
              from this obtain e where e_def:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<not> safe(e)" by blast
              hence unsafe:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<exists> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
              from this obtain c where c_def:"ts'',move ts ts'' v \<Turnstile>  \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
              hence c_neq_e:"ts',move ts ts'' v \<Turnstile>\<^bold>\<not>(c \<^bold>= e)" by blast 
              obtain d where d_def: "\<exists>n. (ts' \<^bold>\<midarrow>c(d,n) \<^bold>\<rightarrow> ts'')" using cr_clm.hyps by blast
              from this obtain n where n_def:" (ts' \<^bold>\<midarrow>c(d,n) \<^bold>\<rightarrow> ts'')"  by blast
              from c_def have "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
                using somewhere_leq by fastforce
              from this obtain v' where v'_def:"(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" by blast
              from this have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
                using n_def backwards_c_res_stab by blast 
              hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> safe (e)" using c_neq_e c_def v'_def somewhere_leq by meson
              thus False using cr_clm.hyps move_stab by fastforce
            qed 
         next
           case (wd_res ts' ts'')
           have "move ts ts' v = move ts' ts'' (move ts ts' v)" using move_stability_wdr wd_res.hyps move_trans 
           by auto
          hence move_stab: "move ts ts' v = move ts ts'' v" by (metis abstract.simps wd_res.hyps(1) wd_res.hyps(3) move_trans)
           show ?case
            proof (rule ccontr)
              assume "\<not> (ts'',move ts ts'' v \<Turnstile> \<^bold>\<forall>e. safe(e))"
              hence contra:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<exists> e. \<^bold>\<not> safe(e)" by blast
              from this obtain e where e_def:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<not> safe(e)" by blast
              hence unsafe:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<exists> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
              from this obtain c where c_def:"ts'',move ts ts'' v \<Turnstile>  \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
              hence c_neq_e:"ts',move ts ts'' v \<Turnstile>\<^bold>\<not>(c \<^bold>= e)" by blast 
              obtain d where d_def: "\<exists>n. (ts' \<^bold>\<midarrow>wdr(d,n) \<^bold>\<rightarrow> ts'')" using wd_res.hyps by blast
              from this obtain n where n_def:" (ts' \<^bold>\<midarrow>wdr(d,n) \<^bold>\<rightarrow> ts'')"  by blast
              from c_def have "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
                using somewhere_leq by fastforce
              from this obtain v' where v'_def:"(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" by blast
              from this have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
                using n_def backwards_wdr_res_stab by blast 
              hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> safe (e)" using c_neq_e c_def v'_def somewhere_leq by meson
              thus False using wd_res.hyps move_stab by fastforce
            qed 
         next
          case (wd_clm ts' ts'')
          have "move ts ts' v = move ts' ts'' (move ts ts' v)" using move_stability_wdc wd_clm.hyps move_trans 
           by auto
          hence move_stab: "move ts ts' v = move ts ts'' v" by (metis abstract.simps wd_clm.hyps(1) wd_clm.hyps(3) move_trans)
          show ?case
            proof (rule ccontr)
              assume "\<not> (ts'',move ts ts'' v \<Turnstile> \<^bold>\<forall>e. safe(e))"
              hence contra:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<exists> e. \<^bold>\<not> safe(e)" by blast
              from this obtain e where e_def:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<not> safe(e)" by blast
              hence unsafe:"ts'',move ts ts'' v \<Turnstile> \<^bold>\<exists> c. \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
              from this obtain c where c_def:"ts'',move ts ts'' v \<Turnstile>  \<^bold>\<not>(c \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(c) \<^bold>\<and> re(e)\<^bold>\<rangle>" by blast
              hence c_neq_e:"ts',v \<Turnstile>\<^bold>\<not>(c \<^bold>= e)" by blast 
              obtain d where d_def: " (ts' \<^bold>\<midarrow>wdc(d) \<^bold>\<rightarrow> ts'')" using wd_clm.hyps by blast
              from c_def have "\<exists>v'. (v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
                using somewhere_leq by fastforce
              from this obtain v' where v'_def:"(v' \<le> move ts ts'' v) \<and> (ts'',v' \<Turnstile> re(c) \<^bold>\<and> re(e))" by blast
              from this have " (ts',v' \<Turnstile> re(c) \<^bold>\<and> re(e))"
                using d_def backwards_wdc_res_stab by blast 
              hence "ts',move ts ts'' v \<Turnstile> \<^bold>\<not> safe (e)" using c_neq_e c_def v'_def somewhere_leq by meson
              thus False using wd_clm.hyps move_stab by fastforce
            qed 
          qed
        qed
      qed
    qed
  qed

lemma safety_switch_invariant:"\<Turnstile>(\<^bold>\<forall>e. safe(e)) \<^bold>\<rightarrow>  @c (\<^bold>\<forall>e. safe(e))"
proof (rule allI)+
  fix ts v 
  {   
    assume assm: "ts,v \<Turnstile> \<^bold>\<forall>e. safe(e) "
    assume "\<not> ( ts,v \<Turnstile> (@c (\<^bold>\<forall>e. safe(e))))"
    hence "ts,v \<Turnstile> \<^bold>\<not> (@c (\<^bold>\<forall>e. safe(e)))" by blast
    hence "ts,v \<Turnstile>  (@c \<^bold>\<not>(\<^bold>\<forall>e. safe(e)))" using at_neg by (smt switch_unique)
    from this obtain v' where v'_def:"(v=c>v') \<and> (ts,v' \<Turnstile>  \<^bold>\<not>(\<^bold>\<forall>e. safe(e)))" using switch_always_exists
      by metis
    hence "ts,v' \<Turnstile> \<^bold>\<exists> e. \<^bold>\<not> safe(e)" by blast 
    from this obtain e where e_def:"ts,v' \<Turnstile> \<^bold>\<not> safe(e)" by blast
    from e_def obtain d  where c_def:"  (ts,v' \<Turnstile> \<^bold>\<not>(d \<^bold>= e) \<^bold>\<and> \<^bold>\<langle>re(d) \<^bold>\<and> re(e)\<^bold>\<rangle>)" by blast
    from c_def obtain v'sub where v'sub_def:"(v'sub \<le> v') \<and> (ts,v'sub \<Turnstile> re(d) \<^bold>\<and> re(e))" 
      using somewhere_leq by fastforce
    have "own v' = c" using v'_def switch_def by auto
    hence "own v'sub = c" using v'sub_def less_eq_view_ext_def by auto
    obtain vsub where vsub:"(vsub =c> v'sub) \<and> (vsub \<le> v)" using v'_def v'sub_def switch_leq by blast
    from v'sub_def and vsub have "ts,vsub \<Turnstile> @c re(d)" by (metis switch_unique)
    hence vsub_re_d:"ts,vsub \<Turnstile> re(d)" using at_res_inst by blast
        
    from v'sub_def and vsub have "ts,vsub \<Turnstile> @c re(e)" by (metis switch_unique)
    hence vsub_re_e:"ts,vsub \<Turnstile> re(e)" using at_res_inst by blast
    hence "ts,vsub\<Turnstile>re(d) \<^bold>\<and> re(e)" using vsub_re_e vsub_re_d by blast
    hence "ts,v \<Turnstile>\<^bold>\<langle> re(d) \<^bold>\<and> re(e) \<^bold>\<rangle>" using vsub somewhere_leq by fastforce
    hence "ts,v \<Turnstile>\<^bold>\<not> (d \<^bold>= e) \<^bold>\<and> \<^bold>\<langle> re(d) \<^bold>\<and> re(e) \<^bold>\<rangle>" using c_def by blast
    then have False using assm by blast
  } 
  then show "ts,v \<Turnstile>(\<^bold>\<forall>e. safe(e)) \<^bold>\<rightarrow>  @c (\<^bold>\<forall>e. safe(e))" by blast
qed
  
  end
end