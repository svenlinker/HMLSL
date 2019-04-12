(*  Title:      HMLSL.thy
    Author:     Sven Linker

Definition of HMLSL syntax over traffic snapshots and views for cars
with any sensors. Each formula is a function with a traffic snapshot 
and view as parameters, and evaluates to True or False.
*)

section\<open>Basic HMLSL\<close>
text\<open>
In this section, we define the basic formulas of HMLSL. 
All of these basic formulas and theorems are independent 
of the choice of sensor function. However, they show how
the general operators (chop, changes in perspective, 
atomic formulas) work. 
\<close>

theory HMLSL
  imports "Restriction" "Move" Length
begin

subsection\<open>Syntax of Basic HMLSL\<close>

text \<open>
Formulas are functions associating a traffic snapshot
and a view with a Boolean value.
\<close>
type_synonym \<sigma> = " traffic \<Rightarrow> view \<Rightarrow> bool"

locale hmlsl = restriction+
  fixes sensors::"cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real" 
  assumes sensors_ge:"(sensors e ts c) > 0"  begin
end

sublocale hmlsl<sensors 
  by (simp add: sensors.intro sensors_ge)

context hmlsl
begin

text\<open>
All formulas are defined as abbreviations. As a consequence,
proofs will directly refer to the semantics of HMLSL, i.e.,
traffic snapshots and views.
\<close>

text\<open>
The first-order operators are direct translations into HOL operators.
\<close>

definition mtrue  :: "\<sigma>" ("\<^bold>\<top>")
  where "\<^bold>\<top> \<equiv> \<lambda> ts w. True" 
definition mfalse :: "\<sigma>" ("\<^bold>\<bottom>") 
  where "\<^bold>\<bottom> \<equiv> \<lambda> ts w. False"   
definition mnot   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda> ts w. \<not>\<phi>(ts)(w)" 
definition mnegpred :: "(cars\<Rightarrow>\<sigma>)\<Rightarrow>(cars\<Rightarrow>\<sigma>)" ("\<^sup>\<not>_"[52]53) 
  where "\<^sup>\<not>\<Phi> \<equiv> \<lambda>x.\<lambda> ts w. \<not>\<Phi>(x)(ts)(w)"   
definition mand   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51)
  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<and>\<psi>(ts)(w)"   
definition mor    :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infix "\<^bold>\<or>"50 )
  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<or>\<psi>(ts)(w)"   
definition mimp   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) 
  where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<longrightarrow>\<psi>(ts)(w)"  
definition mequ   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48)
  where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda> ts w. \<phi>(ts)(w)\<longleftrightarrow>\<psi>(ts)(w)"  
definition mforall   :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>")      
  where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda> ts w.\<forall>x. \<Phi>(x)(ts)(w)"
definition mforallB  :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9)
  where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"   
definition mexists   :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") 
  where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda> ts w.\<exists>x. \<Phi>(x)(ts)(w)"
definition mexistsB  :: "(('a)\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9)
  where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"   
definition meq    :: "'a\<Rightarrow>'a\<Rightarrow>\<sigma>" (infixr"\<^bold>="60) \<comment> \<open>Equality\<close>  
  where "x\<^bold>=y \<equiv> \<lambda> ts w. x = y"
definition mgeq :: "('a::ord) \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infix "\<^bold>\<ge>" 60)
  where "x \<^bold>\<ge> y \<equiv> \<lambda> ts w. x \<ge> y" 
definition mge ::"('a::ord) \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infix "\<^bold>>" 60)
  where "x \<^bold>> y \<equiv> \<lambda> ts w. x > y"

text\<open>
For the spatial modalities, we use the chopping operations
defined on views. Observe that our chop modalities are existential.
\<close>

definition hchop   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<frown>" 53)
  where "\<phi> \<^bold>\<frown> \<psi> \<equiv> \<lambda> ts w.\<exists>v u. (w=v\<parallel>u) \<and> \<phi>(ts)(v)\<and>\<psi>(ts)(u)"
definition vchop   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<smile>" 53)
  where "\<phi> \<^bold>\<smile> \<psi> \<equiv> \<lambda> ts w.\<exists>v u. (w=v--u) \<and> \<phi>(ts)(v) \<and> \<psi>(ts)(u)"
definition somewhere ::"\<sigma>\<Rightarrow>\<sigma>" ( "\<^bold>\<langle>_\<^bold>\<rangle> " 55)
  where "\<^bold>\<langle>\<phi>\<^bold>\<rangle> \<equiv> \<^bold>\<top> \<^bold>\<frown> (\<^bold>\<top>\<^bold>\<smile>\<phi> \<^bold>\<smile>\<^bold>\<top>)\<^bold>\<frown>\<^bold>\<top>"
definition everywhere::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>[_\<^bold>]" 55)
  where "\<^bold>[\<phi>\<^bold>] \<equiv> \<^bold>\<not>\<^bold>\<langle>\<^bold>\<not>\<phi>\<^bold>\<rangle>"

text\<open>
To change the perspective of a view, we use 
an operator in the fashion of Hybrid Logic.
\<close>
definition at :: "cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma> " ("\<^bold>@ _ _" 56)
  where "\<^bold>@c \<phi> \<equiv> \<lambda>ts w .  \<forall>v'. (w=c>v') \<longrightarrow> \<phi>(ts)(v')"

text\<open>
The behavioural modalities are defined as usual modal
box-like modalities, where the accessibility relations
are given by the different types of transitions between
traffic snapshots.
\<close>

definition res_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>r'(_') _" 55)
  where "\<^bold>\<box>r(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts'. (ts\<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)" 
definition clm_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>c'(_') _" 55)
  where "\<^bold>\<box>c(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts' n. (ts\<^bold>\<midarrow>c(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)"
definition wdres_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>wdr'(_') _" 55)
  where "\<^bold>\<box>wdr(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts' n. (ts\<^bold>\<midarrow>wdr(c,n)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)"
definition wdclm_box::"cars \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>wdc'(_') _" 55)
  where "\<^bold>\<box>wdc(c) \<phi> \<equiv> \<lambda> ts w. \<forall>ts'. (ts\<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow>ts') \<longrightarrow> \<phi>(ts')(w)"
definition time_box::"\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>\<^bold>\<tau> _" 55) 
  where "\<^bold>\<box>\<^bold>\<tau> \<phi> \<equiv> \<lambda>ts w. \<forall>ts'. (ts\<^bold>\<leadsto>ts') \<longrightarrow> \<phi>(ts')(move ts ts' w)" 
definition globally::"\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>G _" 55)
  where "\<^bold>G \<phi> \<equiv> \<lambda>ts w. \<forall>ts'. (ts \<^bold>\<Rightarrow> ts') \<longrightarrow> \<phi>(ts')(move ts ts' w)"


text\<open>
The spatial atoms to refer to reservations, claims
and free space are direct translations of the original
definitions of MLSL \cite{Hilscher2011} into the Isabelle implementation.
\<close>

definition re:: "cars \<Rightarrow> \<sigma>" ("re'(_')" 70)
  where 
    "re(c) \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel>> 0 \<and> len v ts c = ext v \<and> 
                      restrict v (res ts) c = lan v \<and> |lan v|=1" 

definition cl:: "cars \<Rightarrow> \<sigma>" ("cl'(_')" 70)
  where 
    "cl(c) \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel>> 0 \<and> len v ts c = ext v \<and> 
                      restrict v (clm ts) c = lan v \<and> |lan v| = 1" 

abbreviation free:: "\<sigma>" ("free")
  where 
    "free \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel> > 0 \<and> |lan v| = 1 \<and>
                  (\<forall>c.  \<parallel>len v ts c\<parallel> = 0 \<or> 
                    (restrict v (clm ts) c = \<emptyset> \<and> restrict v (res ts) c = \<emptyset>))"  

text\<open>
Even though we do not need them for the subsequent proofs of safety,
we define ways to measure the number of lanes (width) and the
size of the extension (length) of a view. This allows us 
to connect the atomic formulas for reservations and claims
with the atom denoting free space \cite{Linker2015a}.
\<close>

definition width_eq::"nat \<Rightarrow> \<sigma>" ("\<^bold>\<omega> = _ " 60)
  where "\<^bold>\<omega> = n \<equiv> \<lambda>  ts v. |lan v| = n"  

definition width_geq::"nat \<Rightarrow> \<sigma>" ("\<^bold>\<omega> \<ge> _" 60)
  where "\<^bold>\<omega> \<ge> n \<equiv> \<lambda>  ts v. |lan v| \<ge> n" 

definition width_ge::"nat \<Rightarrow> \<sigma>" ("\<^bold>\<omega> > _" 60)
  where "\<^bold>\<omega> > n \<equiv> (\<^bold>\<omega> = n+1) \<^bold>\<smile> \<^bold>\<top>"

definition length_eq::"real \<Rightarrow> \<sigma>" ("\<^bold>\<l> = _ " 60)
  where "\<^bold>\<l> = r \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel> = r"

definition length_ge:: "real \<Rightarrow> \<sigma>" ("\<^bold>\<l> > _" 60)
  where "\<^bold>\<l> > r \<equiv> \<lambda> ts v. \<parallel>ext v\<parallel> > r"

definition length_geq::"real \<Rightarrow> \<sigma>" ("\<^bold>\<l> \<ge> _" 60)
  where "\<^bold>\<l> \<ge> r \<equiv> (\<^bold>\<l> = r) \<^bold>\<or> (\<^bold>\<l> > r)"

text\<open>
For convenience, we use abbreviations for 
the validity and satisfiability of formulas. While
the former gives a nice way to express theorems, 
the latter is useful within proofs.
\<close>


definition satisfies::" traffic \<Rightarrow> view \<Rightarrow> \<sigma> \<Rightarrow> bool" ("_ , _ \<Turnstile> _" 10)
  where "ts,v \<Turnstile> \<phi> \<equiv> \<phi>(ts)(v)"

definition valid :: "\<sigma> \<Rightarrow> bool" ("\<Turnstile> _" 10 )
  where "\<Turnstile> \<phi> \<equiv>  \<forall>ts. \<forall>v. ( ts,v \<Turnstile> \<phi> )"

section \<open>Theorems about Basic HMLSL\<close>

subsection\<open>FOL Fragment\<close>

subsubsection\<open>True and False\<close>

lemma mTrueI:"ts,v \<Turnstile>\<^bold>\<top>" 
  by (simp add: mtrue_def satisfies_def)

lemma mFalseI: "\<not> (ts,v \<Turnstile> \<^bold>\<bottom>)" 
  by (simp add: mfalse_def satisfies_def)  

lemma mFalseE: "ts,v \<Turnstile> \<^bold>\<bottom> \<Longrightarrow> P"
  by (simp add: mFalseI)

text\<open>Disjunction\<close>
lemma mdisjE:
assumes major: "ts,v \<Turnstile> P \<^bold>\<or>  Q"
    and minorP: "ts,v \<Turnstile> P \<Longrightarrow> ts,v \<Turnstile>R"
    and minorQ: "ts,v \<Turnstile> Q \<Longrightarrow> ts,v \<Turnstile> R"
  shows "ts,v \<Turnstile>R" 
  using major minorP minorQ mor_def satisfies_def by auto

lemma mdisjI1: "ts,v \<Turnstile> P \<Longrightarrow> ts,v \<Turnstile>P \<^bold>\<or> Q" 
  using mor_def satisfies_def by auto

lemma mdisjI2: "ts,v \<Turnstile> Q \<Longrightarrow> ts,v \<Turnstile> P \<^bold>\<or> Q"
  using mor_def satisfies_def by auto

text\<open>Conjunction\<close>
lemma mconjI: "\<lbrakk>ts,v \<Turnstile>P; ts,v \<Turnstile> Q\<rbrakk> \<Longrightarrow> ts,v \<Turnstile> P \<^bold>\<and> Q"
  using mand_def satisfies_def by auto

lemma mconjunct1: "\<lbrakk>ts,v \<Turnstile> P \<^bold>\<and> Q\<rbrakk> \<Longrightarrow> ts,v \<Turnstile>P"
  using mand_def satisfies_def by auto

lemma mconjunct2: "\<lbrakk>ts,v \<Turnstile> P \<^bold>\<and> Q\<rbrakk> \<Longrightarrow> ts,v \<Turnstile>Q"
  using mand_def satisfies_def by auto

lemma mconjE:
  assumes major: "ts,v \<Turnstile>P \<^bold>\<and> Q"
    and minor: "\<lbrakk>ts,v \<Turnstile>P; ts,v \<Turnstile> Q\<rbrakk> \<Longrightarrow> R"
  shows R
  using mand_def satisfies_def 
  using major minor by auto

lemma mcontext_conjI:
  assumes "ts,v \<Turnstile>P" "ts,v \<Turnstile> P \<Longrightarrow> ts,v \<Turnstile>Q"
  shows "ts,v \<Turnstile> P \<^bold>\<and> Q"
  using mand_def satisfies_def assms(1) assms(2) by auto


text\<open>Negation\<close>

lemma mnotI:
  assumes "ts,v \<Turnstile> P \<Longrightarrow> ts',v' \<Turnstile> \<^bold>\<bottom>"
  shows "ts,v \<Turnstile> \<^bold>\<not> P"
  using assms mFalseI mnot_def satisfies_def by auto

lemma mnotE: "\<lbrakk>ts,v \<Turnstile>\<^bold>\<not> P; ts,v \<Turnstile> P\<rbrakk> \<Longrightarrow> R" 
  using hmlsl.mnot_def hmlsl_axioms satisfies_def by auto

lemma mnotI2: "(ts,v \<Turnstile>P \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<not> Pa) \<Longrightarrow> (ts,v \<Turnstile> P \<Longrightarrow> ts,v \<Turnstile>Pa) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<not> P"
  using mnot_def satisfies_def by auto

lemma mnotE':
  assumes 1: "ts,v \<Turnstile> \<^bold>\<not> P"
    and 2: "ts,v \<Turnstile> \<^bold>\<not> P \<Longrightarrow> ts,v \<Turnstile>P"
  shows R
proof -
  from 2 and 1 have "ts,v \<Turnstile>P"  .
  with 1 show R by (rule mnotE)
qed


subsubsection\<open>Implication\<close>
lemma  mimpI: "(ts,v \<Turnstile>P \<Longrightarrow> ts,v \<Turnstile>Q) \<Longrightarrow> ts,v \<Turnstile>P \<^bold>\<rightarrow> Q"
  by (simp add: mimp_def satisfies_def)

lemma mimpE:
  assumes "ts,v \<Turnstile> P \<^bold>\<rightarrow> Q" "ts,v \<Turnstile>P" "ts,v \<Turnstile>Q \<Longrightarrow> R"
  shows R
  using assms(1) assms(2) assms(3) mimp_def satisfies_def by auto

lemma mrev_mp: "\<lbrakk>ts,v \<Turnstile>P; ts,v \<Turnstile> P \<^bold>\<rightarrow> Q\<rbrakk> \<Longrightarrow> ts,v \<Turnstile>Q"
  using mimpE by blast

lemma mcontrapos_nn:
  assumes major: "ts,v \<Turnstile> \<^bold>\<not> Q"
    and minor: "ts,v \<Turnstile>P \<Longrightarrow> ts,v \<Turnstile>Q"
  shows "ts,v \<Turnstile>\<^bold>\<not> P"
  using major minor mnotI2 by blast

lemma mimpE':
  assumes 1: "ts,v \<Turnstile> P \<^bold>\<rightarrow> Q"
    and 2: "ts,v \<Turnstile>Q \<Longrightarrow> R"
    and 3: "ts,v \<Turnstile> P \<^bold>\<rightarrow> Q \<Longrightarrow> ts,v \<Turnstile>P"
  shows R
proof -
  from 3 and 1 have "ts,v \<Turnstile>P" .
  with 1 have "ts,v \<Turnstile>Q" by (rule mimpE)
  with 2 show R .
qed


subsubsection\<open>Bi-Implication\<close>
lemma miffI:
  assumes "ts,v \<Turnstile>P \<Longrightarrow> ts,v \<Turnstile>Q" and "ts,v \<Turnstile> Q \<Longrightarrow> ts,v \<Turnstile>P"
  shows "ts,v  \<Turnstile>P \<^bold>\<leftrightarrow>  Q"
  using assms(1) assms(2) mequ_def satisfies_def by auto

lemma miffD2: "\<lbrakk>ts,v \<Turnstile>P \<^bold>\<leftrightarrow> Q; ts,v \<Turnstile> Q\<rbrakk> \<Longrightarrow> ts,v \<Turnstile>P"
  by (simp add: mequ_def satisfies_def)

(*
lemma rev_iffD2: "\<lbrakk>ts,v \<Turnstile>Q; ts,v \<Turnstile> P \<^bold>\<leftrightarrow> Q\<rbrakk> \<Longrightarrow> ts,v \<Turnstile>P"
  by (simp add: mequ_def satisfies_def)
*)
lemma miffD1: "ts,v \<Turnstile>Q \<^bold>\<leftrightarrow> P \<Longrightarrow> ts,v \<Turnstile>Q \<Longrightarrow> ts,v \<Turnstile>P"
  by (simp add: mequ_def satisfies_def)

(*lemma rev_iffD1: "ts,v \<Turnstile>Q \<Longrightarrow> ts,v \<Turnstile>Q \<^bold>\<leftrightarrow> P \<Longrightarrow> ts,v \<Turnstile>P"
  by (simp add: mequ_def satisfies_def)
*)

lemma miffE:
  assumes major: "ts,v \<Turnstile>P \<^bold>\<leftrightarrow> Q"
    and minor: "\<lbrakk>ts,v \<Turnstile> P \<^bold>\<rightarrow> Q; ts,v \<Turnstile>Q \<^bold>\<rightarrow> P\<rbrakk> \<Longrightarrow> R"
  shows R
  using major mequ_def mimp_def minor satisfies_def by auto

subsubsection \<open>Existential quantifier\<close>

lemma mexI: "ts,v \<Turnstile> P x \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<exists>x::'a. P x"
  by (metis mexistsB_def mexists_def satisfies_def)

lemma mexE:
  assumes major: "ts,v \<Turnstile>\<^bold>\<exists>x::'a. P x"
    and minor: "\<And>x. ts,v \<Turnstile> P x \<Longrightarrow> Q"
  shows "Q"
  by (metis major mexistsB_def mexists_def minor satisfies_def)


text \<open>Universal quantifier\<close>

lemma mallI:
  assumes "\<And>x::'a. ts,v \<Turnstile>P x"
  shows "ts,v \<Turnstile> \<^bold>\<forall>x. P x"
  by (metis assms mforallB_def mforall_def satisfies_def)

lemma mspec: "ts,v \<Turnstile>\<^bold>\<forall>x::'a. P x \<Longrightarrow> ts,v \<Turnstile>P x"
  by (simp add: mforallB_def mforall_def satisfies_def)

lemma mallE:
  assumes major: "ts,v \<Turnstile> \<^bold>\<forall>x. P x"
    and minor: "ts,v \<Turnstile>P x \<Longrightarrow> R"
  shows R
  by (simp add: major minor mspec)

lemma mall_dupE:
  assumes major: "ts,v \<Turnstile>\<^bold>\<forall>x. P x"
    and minor: "\<lbrakk>ts,v \<Turnstile>P x; ts,v \<Turnstile> \<^bold>\<forall>x. P x\<rbrakk> \<Longrightarrow> R"
  shows R
  by (simp add: major minor mspec)

subsubsection\<open>True (2)\<close>

lemma mTrueE: "ts,v \<Turnstile> \<^bold>\<top> \<Longrightarrow> ts',v' \<Turnstile> P \<Longrightarrow> ts',v' \<Turnstile> P" .
lemma mnotFalseE: "ts,v \<Turnstile> \<^bold>\<not> \<^bold>\<bottom> \<Longrightarrow> ts',v' \<Turnstile>P \<Longrightarrow> ts',v' \<Turnstile> P" .

subsubsection\<open>Equational\<close>

lemma mrefl:" ts,v \<Turnstile> x \<^bold>= x" 
  by (simp add: meq_def satisfies_def) 

(*
lemmas [elim!] = mdisjE miffE mFalseE mconjE mexE mTrueE mnotFalseE
  and [intro!] = miffI mconjI mimpI mTrueI mnotI mallI mrefl
  and [elim 2] = mallE  
  and [intro] = mexI mdisjI2 mdisjI1
*)
lemma hchop_weaken1 : "ts,v \<Turnstile> P \<Longrightarrow> ts,v \<Turnstile> P \<^bold>\<frown> \<^bold>\<top>" 
  by (metis hmlsl.hchop_def hmlsl.satisfies_def hmlsl_axioms horizontal_chop_empty_right mtrue_def)

lemma hchop_weaken2 : "ts,v \<Turnstile> P \<Longrightarrow> ts,v \<Turnstile>\<^bold>\<top> \<^bold>\<frown> P" 
  by (metis hmlsl.hchop_def hmlsl.satisfies_def hmlsl_axioms horizontal_chop_empty_left mTrueI)

print_facts

lemma hchop_weaken1': "ts,v \<Turnstile> \<phi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<frown> \<^bold>\<top>) " using hchop_weaken1 
  by (simp add: mimpI)

lemma hchop_weaken2': "ts,v  \<Turnstile> \<phi> \<^bold>\<rightarrow> (\<^bold>\<top> \<^bold>\<frown> \<phi>) " 
  using hchop_weaken2 
  by (simp add:mimpI)

lemma hchop_weaken: " ts,v \<Turnstile> \<phi>  \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<top> \<^bold>\<frown> \<phi> \<^bold>\<frown> \<^bold>\<top>)" 
  using  hchop_weaken1 hchop_weaken2  by simp

lemma hchop_neg1:"ts,v \<Turnstile> \<^bold>\<not> (\<phi> \<^bold>\<frown> \<^bold>\<top>)  \<Longrightarrow> ts,v \<Turnstile> ((\<^bold>\<not> \<phi>) \<^bold>\<frown> \<^bold>\<top>)" 
  by (simp add: hchop_weaken1 mnotI2)

lemma hchop_neg2:"ts,v \<Turnstile> \<^bold>\<not> (\<^bold>\<top>\<^bold>\<frown>\<phi> ) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<top> \<^bold>\<frown> \<^bold>\<not> \<phi>)"
  by (simp add: hchop_weaken2 mnotI2)


lemma hchop_disj_distr_right1:"ts,v \<Turnstile> \<phi> \<^bold>\<frown> (\<psi> \<^bold>\<or> \<chi>) \<Longrightarrow> ts,v \<Turnstile> (\<phi> \<^bold>\<frown> \<psi>)\<^bold>\<or>(\<phi> \<^bold>\<frown> \<chi>)" 
  using hchop_def mor_def satisfies_def by auto

lemma hchop_disj_distr_right2:" ts,v \<Turnstile> (\<phi> \<^bold>\<frown> \<psi>)\<^bold>\<or>(\<phi> \<^bold>\<frown> \<chi>) \<Longrightarrow> ts,v \<Turnstile> \<phi> \<^bold>\<frown> (\<psi> \<^bold>\<or> \<chi>) " 
  using hchop_def mor_def satisfies_def by auto

lemma hchop_disj_distr_left1:"ts,v \<Turnstile> (\<psi> \<^bold>\<or> \<chi>)\<^bold>\<frown>\<phi> \<Longrightarrow> ts,v \<Turnstile> (\<psi> \<^bold>\<frown> \<phi>)\<^bold>\<or>(\<chi> \<^bold>\<frown> \<phi>)" 
  using hchop_def mor_def satisfies_def by auto

lemma hchop_disj_distr_left2:" ts,v \<Turnstile> (\<psi> \<^bold>\<frown> \<phi>)\<^bold>\<or>(\<chi> \<^bold>\<frown> \<phi>) \<Longrightarrow> ts,v \<Turnstile> (\<psi> \<^bold>\<or> \<chi>)\<^bold>\<frown>\<phi> " 
  using hchop_def mor_def satisfies_def by auto

lemma hchop_assoc:"(ts,v \<Turnstile> \<phi> \<^bold>\<frown> (\<psi> \<^bold>\<frown> \<chi>)) = (ts,v \<Turnstile>  (\<phi> \<^bold>\<frown> \<psi>) \<^bold>\<frown> \<chi>)" 
  unfolding valid_def satisfies_def  using horizontal_chop_assoc1' horizontal_chop_assoc2 hchop_def by fastforce

lemma v_chop_weaken1:"ts,v \<Turnstile> \<phi>  \<Longrightarrow> ts,v \<Turnstile> (\<phi> \<^bold>\<smile> \<^bold>\<top>)"  
  by (metis hmlsl.satisfies_def hmlsl.vchop_def hmlsl_axioms mtrue_def vertical_chop_empty_down)

lemma v_chop_weaken2:"ts,v \<Turnstile> \<phi> \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<top> \<^bold>\<smile> \<phi>)" 
  by (metis hmlsl.satisfies_def hmlsl.vchop_def hmlsl_axioms mtrue_def vertical_chop_empty_up)

lemma v_chop_assoc:"(ts,v \<Turnstile>\<phi> \<^bold>\<smile> (\<psi> \<^bold>\<smile> \<chi>)) =  (ts,v \<Turnstile>(\<phi> \<^bold>\<smile> \<psi>) \<^bold>\<smile> \<chi>)"
  unfolding valid_def satisfies_def  using vertical_chop_assoc1 vertical_chop_assoc2 vchop_def by fastforce

lemma vchop_disj_distr1:"(ts,v \<Turnstile> \<phi> \<^bold>\<smile> (\<psi> \<^bold>\<or> \<chi>)) = (ts,v \<Turnstile> (\<phi> \<^bold>\<smile> \<psi>)\<^bold>\<or>(\<phi> \<^bold>\<smile> \<chi>))" 
  using valid_def satisfies_def  vchop_def mor_def by auto

lemma vchop_disj_distr2:"(ts,v \<Turnstile> (\<psi> \<^bold>\<or> \<chi>) \<^bold>\<smile> \<phi> ) =  (ts,v \<Turnstile>(\<psi> \<^bold>\<smile> \<phi>)\<^bold>\<or>(\<chi> \<^bold>\<smile> \<phi>))" 
  using valid_def satisfies_def  vchop_def mor_def by auto

lemma somewhere_leq:" (ts,v \<Turnstile> \<^bold>\<langle> \<phi> \<^bold>\<rangle>) = (\<exists>v'. v' \<le> v \<and> (ts,v' \<Turnstile> \<phi>))" 
proof
  assume "ts,v \<Turnstile> \<^bold>\<langle> \<phi> \<^bold>\<rangle>" 
  then obtain v1 v2 vl vr where 1: " (v=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (ts,v2 \<Turnstile> \<^bold>\<top> \<^bold>\<smile> \<phi> \<^bold>\<smile> \<^bold>\<top>)" 
    using hchop_def satisfies_def  somewhere_def by auto  
  then obtain v3 vu vd v' where 2:"(v=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v'--vu) \<and> (ts,v' \<Turnstile> \<phi>)" 
    using  satisfies_def vchop_def by auto
  then have "v' \<le> v" using somewhere_leq 1 2 by blast
  then show "(\<exists>v'. v' \<le> v \<and> (ts,v' \<Turnstile> \<phi>))" using 2 by blast
next
  assume "(\<exists>v'. v' \<le> v \<and> (ts,v' \<Turnstile> \<phi>))" 
  then obtain v1 v2 vl vr v3 vu vd v' where 1:"(v=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v'--vu) \<and> (ts,v' \<Turnstile> \<phi>)"
    using somewhere_leq 
    by auto
  then have "ts, v2 \<Turnstile>  \<^bold>\<top> \<^bold>\<smile> \<phi> \<^bold>\<smile> \<^bold>\<top>" 
    using  satisfies_def vchop_def mTrueI by auto
  then show "ts,v \<Turnstile>  \<^bold>\<langle> \<phi> \<^bold>\<rangle>" using  hchop_def satisfies_def 1 mTrueI somewhere_def by auto
qed
    

lemma at_exists :"ts,v \<Turnstile> \<phi>  \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<exists> c. \<^bold>@c \<phi>)"
proof -
  assume a: "ts,v \<Turnstile> \<phi>"
  obtain d where d_def:"d=own v" by blast
  then have "ts,v \<Turnstile> \<^bold>@d \<phi>" 
    using a at_def satisfies_def  view.switch_refl sorry
  then show "ts,v \<Turnstile> (\<^bold>\<exists> c. \<^bold>@c \<phi>)" 
    by (meson mexI)
qed
(*proof
  fix ts v
  assume assm:"ts,v \<Turnstile>\<phi>"
  obtain d where d_def:"d=own v" by blast
  then have "ts,v \<Turnstile> \<^bold>@d \<phi>" using assm switch_refl switch_unique unfolding  satisfies_def   by fastforce
  show "ts,v \<Turnstile> (\<^bold>\<exists> c. \<^bold>@c \<phi>)"
qed
*)

lemma at_conj_distr:"\<Turnstile>(\<^bold>@c ( \<phi> \<^bold>\<and> \<psi>)) \<^bold>\<leftrightarrow> ((\<^bold>@c \<phi>) \<^bold>\<and> (\<^bold>@c \<psi>))"
  unfolding at_def  satisfies_def  using valid_def satisfies_def  switch_unique  by blast

lemma at_disj_dist:"\<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<or> \<psi>)) \<^bold>\<leftrightarrow> ((\<^bold>@c \<phi> )  \<^bold>\<or> ( \<^bold>@c \<psi> ))"
  unfolding at_def satisfies_def  valid_def using valid_def switch_unique satisfies_def   by blast

lemma at_hchop_dist1:"ts,v \<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>)) \<^bold>\<rightarrow> ((\<^bold>@c \<phi>) \<^bold>\<frown> (\<^bold>@c \<psi>))"  
proof -
  { 
  assume assm:"ts, v \<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>))"
  obtain v' where v':"v=c>v'" using switch_always_exists  by fastforce
  with assm obtain v1' and v2'
    where chop:"(v'=v1'\<parallel>v2') \<and> (ts,v1' \<Turnstile> \<phi>) \<and> (ts,v2'\<Turnstile>\<psi>)" 
    unfolding satisfies_def   using hchop_def at_def by auto 
  from chop and v' obtain v1 and v2 
    where origin:"(v1=c>v1') \<and> (v2=c>v2') \<and> (v=v1\<parallel>v2)" 
    using switch_hchop2  by fastforce
  hence v1:"ts,v1 \<Turnstile> (\<^bold>@c \<phi>)" and v2:"ts,v2 \<Turnstile> (\<^bold>@c \<psi>)" 
    unfolding satisfies_def  using switch_unique chop at_def unfolding satisfies_def  by fastforce+   
  from  v1 and v2 and origin have "ts,v \<Turnstile>(\<^bold>@c \<phi>) \<^bold>\<frown> (\<^bold>@c \<psi>)"  unfolding satisfies_def hchop_def by blast
}
  from this show ?thesis unfolding satisfies_def by blast  (* " ( ts,v  \<Turnstile> (\<^bold>@ c \<phi>) \<^bold>\<frown>( \<^bold>@ c \<psi>)) " *)
qed

lemma at_hchop_dist2:"\<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<frown> (\<^bold>@c \<psi>)) \<^bold>\<rightarrow> (\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>))  "
  unfolding valid_def at_def hchop_def using switch_unique switch_hchop1 switch_def unfolding satisfies_def at_def hchop_def  by meson

(*lemma at_hchop_dist:"\<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<frown>  (\<^bold>@c \<psi>)) \<^bold>\<leftrightarrow> (\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>))  "
  unfolding valid_def using at_hchop_dist1 at_hchop_dist2 *)

lemma at_vchop_dist1:"\<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>)) \<^bold>\<rightarrow> ( (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>))"
proof -
  {
  fix ts v
  assume assm:"ts, v \<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>))"
  obtain v' where v':"v=c>v'" using switch_always_exists by fastforce
  with assm obtain v1' and v2' 
    where chop:"(v'=v1'--v2') \<and> (ts,v1' \<Turnstile> \<phi>) \<and> (ts,v2'\<Turnstile>\<psi>)" 
    using at_def satisfies_def vchop_def by auto
  from chop and v' obtain v1 and v2 
    where origin:"(v1=c>v1') \<and> (v2=c>v2') \<and> (v=v1--v2)" 
    using switch_vchop2 by fastforce
  hence v1:"ts,v1 \<Turnstile> (\<^bold>@c \<phi>)" and v2:"ts,v2 \<Turnstile> (\<^bold>@c \<psi>)" 
    using switch_unique chop at_def satisfies_def 
    unfolding at_def unfolding satisfies_def 
    by fastforce+  
  from v1 and v2 and origin have "ts,v \<Turnstile> (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>)" unfolding satisfies_def 
    using vchop_def by auto
}
  from this show ?thesis unfolding satisfies_def valid_def by simp
qed

(*lemma at_vchop_dist2:"\<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>)) \<^bold>\<rightarrow> (\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>))  "
  using valid_def switch_unique switch_vchop1 switch_def   

lemma at_vchop_dist:"\<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>)) \<^bold>\<leftrightarrow> (\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>))  "
  using at_vchop_dist1 at_vchop_dist2 by blast
*)

lemma at_eq:"\<Turnstile>(\<^bold>@e c \<^bold>= d) \<^bold>\<leftrightarrow> (c \<^bold>= d)"
  unfolding valid_def satisfies_def using switch_always_exists  unfolding at_def by blast

lemma at_neg1:"\<Turnstile>(\<^bold>@c \<^bold>\<not> \<phi>) \<^bold>\<rightarrow> \<^bold>\<not> (\<^bold>@c \<phi>)"
  unfolding satisfies_def valid_def using switch_unique unfolding at_def 
  by (simp add: view.switch_always_exists)

lemma at_neg2:"\<Turnstile>\<^bold>\<not> (\<^bold>@c \<phi> ) \<^bold>\<rightarrow> ( (\<^bold>@c \<^bold>\<not> \<phi>))"
  unfolding valid_def satisfies_def at_def using switch_unique  by fastforce

lemma at_neg :"\<Turnstile>(\<^bold>@c( \<^bold>\<not> \<phi>)) \<^bold>\<leftrightarrow> \<^bold>\<not> (\<^bold>@c \<phi>)" 
  unfolding at_def satisfies_def valid_def using valid_def view.switch_always_exists view.switch_unique by fastforce

lemma at_neg':"ts,v \<Turnstile> \<^bold>\<not> (\<^bold>@c \<phi>) \<^bold>\<leftrightarrow> (\<^bold>@c( \<^bold>\<not> \<phi>))" unfolding valid_def at_def satisfies_def using at_neg valid_def satisfies_def 
  by (metis view.switch_always_exists   view.switch_unique)

lemma at_neg_neg1:"\<Turnstile>(\<^bold>@c \<phi>) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>@c \<^bold>\<not> \<phi>)"
  unfolding valid_def satisfies_def at_def using switch_unique switch_def switch_refl 
  using view.switch_always_exists by blast

lemma at_neg_neg2:"\<Turnstile>\<^bold>\<not>(\<^bold>@c \<^bold>\<not> \<phi>) \<^bold>\<rightarrow> (\<^bold>@c  \<phi>)"
 unfolding valid_def at_def satisfies_def using switch_unique switch_def switch_refl  
  by metis

lemma at_neg_neg:"\<Turnstile> (\<^bold>@c \<phi>) \<^bold>\<leftrightarrow> \<^bold>\<not>(\<^bold>@c \<^bold>\<not> \<phi>)" 
  unfolding valid_def at_def satisfies_def using at_neg_neg1 at_neg_neg2 valid_def at_def 
  using at_neg' 
  by (metis view.switch_always_exists  view.switch_unique) 

lemma globally_all_iff:"\<Turnstile> (\<^bold>G(\<^bold>\<forall>c. \<phi>)) \<^bold>\<leftrightarrow> (\<^bold>\<forall>c.( \<^bold>G \<phi>))" unfolding valid_def satisfies_def by simp
lemma globally_all_iff':"ts,v\<Turnstile> (\<^bold>G(\<^bold>\<forall>c. \<phi>)) \<^bold>\<leftrightarrow> (\<^bold>\<forall>c.( \<^bold>G \<phi>))" unfolding valid_def satisfies_def by simp

lemma globally_refl:" \<Turnstile>(\<^bold>G \<phi>) \<^bold>\<rightarrow> \<phi>" 
unfolding valid_def satisfies_def  using traffic.abstract.refl move_nothing  by fastforce

lemma globally_4: "\<Turnstile> (\<^bold>G  \<phi>) \<^bold>\<rightarrow> \<^bold>G \<^bold>G \<phi>"
     using traffic.abs_trans traffic.move_trans valid_def satisfies_def by presburger
(*proof -
  {
  fix ts v ts' ts'' 
  assume 1:"ts \<^bold>\<Rightarrow> ts'" and 2:"ts' \<^bold>\<Rightarrow> ts''" and 3:"ts,v \<Turnstile> \<^bold>G \<phi>" 
  from 2 and 1 have "ts \<^bold>\<Rightarrow> ts''" using traffic.abs_trans by blast  
  moreover from 1 and 2 have "move ts' ts'' (move ts ts' v) = move ts ts'' v"
    using traffic.move_trans by blast
  with 3 have "ts'', move ts' ts'' (move ts ts' v)  \<Turnstile>\<phi>" unfolding satisfies_def using calculation by simp
} 
   show ?thesis 
     using traffic.abs_trans traffic.move_trans valid_def by presburger
qed
*)

lemma spatial_weaken: "\<Turnstile> (\<phi> \<^bold>\<rightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle>)" 
unfolding valid_def satisfies_def
  using horizontal_chop_empty_left horizontal_chop_empty_right vertical_chop_empty_down
    vertical_chop_empty_up   hchop_def vchop_def
  by fastforce

lemma spatial_weaken2:"\<Turnstile> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)"
unfolding valid_def satisfies_def
  using spatial_weaken horizontal_chop_empty_left horizontal_chop_empty_right 
    vertical_chop_empty_down vertical_chop_empty_up unfolding valid_def satisfies_def
  by blast 

lemma somewhere_distr: "\<Turnstile> \<^bold>\<langle>\<phi>\<^bold>\<or>\<psi>\<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle>\<psi>\<^bold>\<rangle>" 
unfolding valid_def hchop_def vchop_def satisfies_def by blast

lemma somewhere_and:"\<Turnstile> \<^bold>\<langle>\<phi> \<^bold>\<and> \<psi>\<^bold>\<rangle> \<^bold>\<rightarrow>  \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<langle>\<psi>\<^bold>\<rangle>"
unfolding valid_def  hchop_def vchop_def satisfies_def by blast

lemma somewhere_and_or_distr :"\<Turnstile>(\<^bold>\<langle> \<chi> \<^bold>\<and> (\<phi> \<^bold>\<or> \<psi>) \<^bold>\<rangle> \<^bold>\<leftrightarrow> \<^bold>\<langle> \<chi> \<^bold>\<and>  \<phi> \<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> \<chi> \<^bold>\<and> \<psi> \<^bold>\<rangle>)" 
unfolding valid_def  hchop_def vchop_def satisfies_def by blast

lemma width_add1:"\<Turnstile>((\<^bold>\<omega> = x) \<^bold>\<smile> (\<^bold>\<omega> = y) \<^bold>\<rightarrow> \<^bold>\<omega> = x+y)"
unfolding valid_def hchop_def vchop_def satisfies_def using vertical_chop_add1  by fastforce

lemma width_add2:"\<Turnstile>((\<^bold>\<omega> = x+y) \<^bold>\<rightarrow>  (\<^bold>\<omega> = x) \<^bold>\<smile> \<^bold>\<omega> = y)"
unfolding valid_def  satisfies_def  vchop_def using vertical_chop_add2  by fastforce

lemma width_hchop_stable: "\<Turnstile>((\<^bold>\<omega> = x) \<^bold>\<leftrightarrow> ((\<^bold>\<omega> = x) \<^bold>\<frown> (\<^bold>\<omega>=x)))"
unfolding valid_def  hchop_def satisfies_def  using  horizontal_chop1 
  by (metis view.horizontal_chop_width_stable)

lemma length_geq_zero:"\<Turnstile> (\<^bold>\<l> \<ge> 0)"
unfolding valid_def satisfies_def   by (metis order.not_eq_order_implies_strict real_int.length_ge_zero)

lemma length_split: "\<Turnstile>((\<^bold>\<l> > 0) \<^bold>\<rightarrow> (\<^bold>\<l> > 0) \<^bold>\<frown> (\<^bold>\<l> > 0))"
unfolding valid_def hchop_def satisfies_def   using horizontal_chop_non_empty  by fastforce

lemma length_meld: "\<Turnstile>((\<^bold>\<l> > 0) \<^bold>\<frown> (\<^bold>\<l> > 0) \<^bold>\<rightarrow> (\<^bold>\<l> > 0))"
unfolding valid_def  hchop_def satisfies_def  using view.hchop_def real_int.chop_add_length_ge_0 
  by (metis (no_types, lifting))

lemma length_dense:"\<Turnstile>((\<^bold>\<l> > 0) \<^bold>\<leftrightarrow> (\<^bold>\<l> > 0) \<^bold>\<frown> (\<^bold>\<l> > 0))"
unfolding valid_def satisfies_def   using length_meld length_split unfolding valid_def satisfies_def  by blast

lemma length_add1:"\<Turnstile>((\<^bold>\<l>=x) \<^bold>\<frown> (\<^bold>\<l>= y)) \<^bold>\<rightarrow> (\<^bold>\<l>= x+y)"
unfolding valid_def satisfies_def  hchop_def using view.hchop_def real_int.rchop_def real_int.length_def   by fastforce

lemma length_add2:"\<Turnstile> (x \<^bold>\<ge> 0 \<^bold>\<and> y \<^bold>\<ge> 0) \<^bold>\<rightarrow> ( (\<^bold>\<l>=x+y) \<^bold>\<rightarrow> ((\<^bold>\<l>=x) \<^bold>\<frown> (\<^bold>\<l>=y)))"
unfolding valid_def hchop_def satisfies_def  using horizontal_chop_split_add  by fastforce

lemma length_add:"\<Turnstile> (x \<^bold>\<ge> 0 \<^bold>\<and> y \<^bold>\<ge> 0) \<^bold>\<rightarrow> ( (\<^bold>\<l>=x+y) \<^bold>\<leftrightarrow> ((\<^bold>\<l>=x) \<^bold>\<frown> (\<^bold>\<l>=y)))"
unfolding valid_def satisfies_def   using length_add1 length_add2 unfolding valid_def satisfies_def  by blast

lemma length_vchop_stable:"\<Turnstile>(\<^bold>\<l> = x) \<^bold>\<leftrightarrow> ((\<^bold>\<l> = x) \<^bold>\<smile> ( \<^bold>\<l> = x))"
unfolding valid_def satisfies_def   vchop_def using view.vchop_def vertical_chop1  by fastforce

lemma res_ge_zero:"\<Turnstile>(re(c) \<^bold>\<rightarrow> \<^bold>\<l>>0)"
unfolding valid_def satisfies_def re_def  by blast

lemma clm_ge_zero:"\<Turnstile>(cl(c) \<^bold>\<rightarrow> \<^bold>\<l>>0)"
unfolding valid_def satisfies_def cl_def  by blast

lemma free_ge_zero:"\<Turnstile>free \<^bold>\<rightarrow> \<^bold>\<l>>0"
unfolding valid_def satisfies_def  by blast

lemma width_res:"\<Turnstile>(re(c) \<^bold>\<rightarrow> \<^bold>\<omega> = 1)"
unfolding valid_def satisfies_def re_def  by auto

lemma width_clm:"\<Turnstile>(cl(c) \<^bold>\<rightarrow> \<^bold>\<omega> = 1)"
unfolding valid_def satisfies_def  cl_def by simp

lemma width_free:"\<Turnstile>(free \<^bold>\<rightarrow> \<^bold>\<omega> = 1)"
unfolding valid_def satisfies_def  by simp

lemma width_somewhere_res:"\<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<rightarrow> (\<^bold>\<omega> \<ge> 1)"
proof -
  {
    fix ts v
  assume "ts,v \<Turnstile>  \<^bold>\<langle>re(c)\<^bold>\<rangle>"
  then have "ts,v \<Turnstile> (\<^bold>\<omega> \<ge> 1)" unfolding vchop_def hchop_def
    using view.hchop_def  view.vertical_chop_width_mon 
    unfolding satisfies_def re_def by fastforce  
}
  from this show ?thesis   unfolding valid_def 
    by (simp add: satisfies_def)
qed    

lemma clm_disj_res:"\<Turnstile> \<^bold>\<not> \<^bold>\<langle> cl(c) \<^bold>\<and> re(c) \<^bold>\<rangle>" 
proof -
  {
  fix ts v
  assume "ts,v \<Turnstile>\<^bold>\<langle>cl(c) \<^bold>\<and> re(c)\<^bold>\<rangle>"
  then obtain v' where "v' \<le> v \<and> (ts,v' \<Turnstile> cl(c) \<^bold>\<and> re(c))" unfolding satisfies_def hchop_def vchop_def
    by (meson view.somewhere_leq)
  then have False unfolding satisfies_def re_def cl_def using disjoint  
    by (metis card_non_empty_geq_one inf.idem restriction.restriction_clm_leq_one
        restriction.restriction_clm_res_disjoint)
}
  from this show ?thesis   unfolding valid_def satisfies_def  
    using satisfies_def by blast
qed

lemma width_ge:"\<Turnstile> (\<^bold>\<omega>> 0) \<^bold>\<rightarrow> (\<^bold>\<exists> x. (\<^bold>\<omega> = x) \<^bold>\<and> (x \<^bold>> 0))"
unfolding valid_def satisfies_def   using  vertical_chop_add1  add_gr_0 zero_less_one  
  using hmlsl.vchop_def hmlsl_axioms by auto

lemma two_res_width: "\<Turnstile>((re(c) \<^bold>\<smile> re(c)) \<^bold>\<rightarrow> \<^bold>\<omega> = 2)"
unfolding valid_def vchop_def satisfies_def re_def
  using view.vertical_chop_add1 by auto


lemma res_at_most_two:"\<Turnstile>\<^bold>\<not> (re(c) \<^bold>\<smile>  re(c)  \<^bold>\<smile>  re(c) )"
proof -
  {
  fix ts v 
  assume "ts, v \<Turnstile> (re(c) \<^bold>\<smile>  re(c)  \<^bold>\<smile>  re(c) )"
  then obtain v' and v1 and v2 and v3  
    where "v = v1--v'" and "v'=v2--v3" 
    and "ts,v1 \<Turnstile>re(c)" and "ts,v2 \<Turnstile>re(c)" and "ts,v3 \<Turnstile>re(c)" 
    unfolding satisfies_def  using vchop_def by auto
  then have False 
  proof -
    have "|restrict v' (res ts) c| < |restrict v (res ts) c|"
      using \<open>ts,v1 \<Turnstile>re(c)\<close> \<open>v=v1--v'\<close> restriction.restriction_add_res unfolding satisfies_def re_def by auto
    then show ?thesis unfolding satisfies_def vchop_def using  \<open>ts,v2 \<Turnstile> re(c)\<close> \<open>ts,v3 \<Turnstile>re(c)\<close> \<open>v'=v2--v3\<close> not_less 
          one_add_one restriction_add_res restriction_res_leq_two unfolding satisfies_def re_def by metis
  qed
}
  from this show ?thesis unfolding valid_def satisfies_def by blast
qed

lemma res_at_most_two2:"\<Turnstile>\<^bold>\<not> \<^bold>\<langle>re(c) \<^bold>\<smile>  re(c)  \<^bold>\<smile>  re(c)\<^bold>\<rangle>"
unfolding valid_def  satisfies_def  vchop_def hchop_def using res_at_most_two unfolding valid_def vchop_def satisfies_def  by blast

lemma res_at_most_somewhere:"\<Turnstile>\<^bold>\<not> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> " 
proof -
  {
  fix ts v
  assume assm:"ts,v \<Turnstile>  (\<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> )"
  obtain vu and v1 and vm and vd 
    where chops:"(v=vu--v1) \<and> (v1 = vm--vd)\<and> (ts,vu \<Turnstile>\<^bold>\<langle>re(c)\<^bold>\<rangle>) 
                 \<and> (ts,vm \<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle> ) \<and>( ts,vd \<Turnstile> \<^bold>\<langle> re(c)\<^bold>\<rangle>)"
    unfolding satisfies_def vchop_def hchop_def using assm unfolding hchop_def vchop_def satisfies_def by blast
  from chops have res_vu:"|restrict vu (res ts) c| \<ge> 1" unfolding satisfies_def vchop_def hchop_def re_def
    by (metis restriction_card_somewhere_mon)
  from chops have res_vm:"|restrict vm (res ts) c| \<ge> 1" unfolding satisfies_def vchop_def hchop_def re_def
    by (metis restriction_card_somewhere_mon)
  from chops have res_vd:"|restrict vd (res ts) c| \<ge> 1" unfolding satisfies_def vchop_def hchop_def re_def
    by (metis restriction_card_somewhere_mon)
  from chops have 
    "|restrict v (res ts) c | = 
     |restrict vu (res ts) c|+ |restrict vm (res ts) c| + |restrict vd (res ts) c| "
    using restriction_add_res by force
  with res_vu and res_vd res_vm have "|restrict v (res ts) c | \<ge> 3" 
    by linarith
  with restriction_res_leq_two have False  
    by (metis not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3)
}
  from this show ?thesis 
    using hmlsl.valid_def hmlsl_axioms satisfies_def by auto
qed

(*
lemma res_adj:"\<Turnstile>\<^bold>\<not>  (re(c) \<^bold>\<smile> (\<^bold>\<omega> > 0) \<^bold>\<smile> re(c)) " 
  unfolding valid_def
proof (rule allI|rule notI)+
  fix ts v
  assume "ts,v \<Turnstile> (re(c) \<^bold>\<smile> (\<^bold>\<omega> > 0) \<^bold>\<smile> re(c)) " 
  then obtain v1 and v' and v2 and vn  
    where chop:"(v=v1--v') \<and> (v'=vn--v2) \<and> (ts,v1\<Turnstile>re(c)) 
                \<and> (ts,vn \<Turnstile> \<^bold>\<omega> > 0) \<and> (ts,v2\<Turnstile>re(c))"
    by blast
  hence res1:"|restrict v1 (res ts) c| \<ge> 1" by (simp add: le_numeral_extra(4))
  from chop have res2: "|restrict v2 (res ts) c| \<ge> 1" by (simp add: le_numeral_extra(4))
  from res1 and res2 have "|restrict v (res ts) c| \<ge> 2"
    using chop restriction.restriction_add_res by auto  
  then have resv:"|restrict v (res ts) c| = 2"
    using dual_order.antisym restriction.restriction_res_leq_two by blast
  hence res_two_lanes:"|res ts c| =2" using atMostTwoRes restrict_res 
    by (metis (no_types, lifting) nat_int.card_subset_le dual_order.antisym)
  from this obtain p where p_def:"Rep_nat_int (res ts c) = {p, p+1}" 
    using consecutiveRes by force
  have "Abs_nat_int {p,p+1} \<sqsubseteq> lan v"  
    by (metis Rep_nat_int_inverse atMostTwoRes card_seteq finite_atLeastAtMost
        insert_not_empty nat_int.card'.rep_eq nat_int.card_seq less_eq_nat_int.rep_eq
        p_def resv restrict_res restrict_view)
  have vn_not_e:"lan vn \<noteq> \<emptyset>" using chop
 unfolding valid_def   by (metis nat_int.card_empty_zero less_irrefl width_ge)
  hence consec_vn_v2:"nat_int.consec (lan vn) (lan v2)" 
    using nat_int.card_empty_zero chop nat_int.nchop_def one_neq_zero vchop_def
    by auto
  have v'_not_e:"lan v' \<noteq> \<emptyset>" using chop 
    by (metis less_irrefl nat_int.card_empty_zero view.vertical_chop_assoc2 width_ge)
  hence consec_v1_v':"nat_int.consec (lan v1) (lan v')"
    by (metis (no_types, lifting) nat_int.card_empty_zero chop nat_int.nchop_def
        one_neq_zero vchop_def)
  hence consec_v1_vn:"nat_int.consec (lan v1) (lan vn)"
    by (metis (no_types, lifting) chop consec_vn_v2 nat_int.consec_def 
        nat_int.chop_min vchop_def)
  hence lesser_con:"\<forall>n m. (n \<^bold>\<in> (lan v1) \<and> m \<^bold>\<in> (lan v2) \<longrightarrow> n < m)" 
    using consec_v1_vn consec_vn_v2 nat_int.consec_trans_lesser
    by auto
  have p_in_v1:"p \<^bold>\<in> lan v1" 
  proof (rule ccontr)
    assume "\<not> p \<^bold>\<in> lan v1"
    then have "p \<^bold>\<notin> lan v1" by (simp )
    hence "p \<^bold>\<notin> restrict v1 (res ts) c"  using chop  by (simp add: chop )
    then have "p+1 \<^bold>\<in> restrict v1 (res ts) c"  
    proof -
       have "{p, p + 1} \<inter> (Rep_nat_int (res ts c) \<inter> Rep_nat_int (lan v1)) \<noteq> {}"
         by (metis chop Rep_nat_int_inject bot_nat_int.rep_eq consec_v1_v' 
             inf_nat_int.rep_eq nat_int.consec_def p_def restriction.restrict_def)
      then have "p + 1 \<in> Rep_nat_int (lan v1)"
        using \<open>p \<^bold>\<notin> restrict v1 (res ts) c\<close> inf_nat_int.rep_eq not_in.rep_eq
          restriction.restrict_def by force
      then show ?thesis
        using chop el.rep_eq by presburger
    qed
    hence suc_p:"p+1 \<^bold>\<in> lan v1" using chop by (simp add: chop)
    hence "p+1 \<^bold>\<notin> lan v2" using p_def restrict_def using lesser_con nat_int.el.rep_eq
        nat_int.not_in.rep_eq by auto
    then have "p \<^bold>\<in> restrict v2 (res ts) c"
    proof -
      have f1: "minimum (lan v2) \<in> Rep_nat_int (lan v2)"
        using consec_vn_v2 el.rep_eq minimum_in nat_int.consec_def by simp
      have "lan v2 \<sqsubseteq> res ts c"
        by (metis (no_types) chop restriction.restrict_res)
      then have "minimum (lan v2) = p" 
        using \<open>p + 1 \<^bold>\<notin> lan v2\<close> f1 less_eq_nat_int.rep_eq not_in.rep_eq p_def by auto
      then show ?thesis
        using f1 by (metis chop el.rep_eq)
    qed
    hence p:"p \<^bold>\<in> lan v2" using p_def restrict_def 
      using chop by auto
    show False using lesser_con suc_p p by blast
  qed
  hence p_not_in_v2:"p \<^bold>\<notin> lan v2" using p_def restrict_def lesser_con 
      nat_int.el.rep_eq nat_int.not_in.rep_eq
    by auto
  then have "p+1 \<^bold>\<in> restrict v2 (res ts) c"
  proof -
    have f1: "minimum (lan v2) \<^bold>\<in> lan v2"
      using consec_vn_v2 minimum_in nat_int.consec_def by simp
    obtain x where mini:"x = minimum (lan v2)" by blast
    have "x = p + 1"  
      by (metis IntD1 p_not_in_v2  chop el.rep_eq f1 inf_nat_int.rep_eq insertE mini
          not_in.rep_eq p_def restriction.restrict_def singletonD)
    then show ?thesis 
      using chop f1 mini by auto
  qed
  hence suc_p_in_v2:"p+1 \<^bold>\<in> lan v2" using p_def restrict_def using chop by auto
  have "\<forall>n m. (n \<^bold>\<in> (lan v1) \<and> m \<^bold>\<in> (lan vn) \<longrightarrow> n < m)" 
    using consec_v1_vn nat_int.consec_lesser by auto
  with p_in_v1 have ge_p:"\<forall>m. (m \<^bold>\<in> lan vn \<longrightarrow> p < m)" 
    by blast
  have "\<forall>n m. (n \<^bold>\<in> (lan vn) \<and> m \<^bold>\<in> (lan v2) \<longrightarrow> n < m)" 
    using consec_vn_v2 nat_int.consec_lesser by auto
  with suc_p_in_v2 have less_suc_p:"\<forall>m. (m \<^bold>\<in> lan vn \<longrightarrow>  m< p+1)"
    by blast
  have "\<forall>m. (m \<^bold>\<in> lan vn \<longrightarrow>  (m< p+1 \<and> m > p) )" 
    using ge_p less_suc_p by auto
  hence "\<not>(\<exists>m. (m \<^bold>\<in> lan vn))" 
    by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right linorder_not_less)
  hence "lan vn = \<emptyset>" using nat_int.non_empty_elem_in by auto
  with vn_not_e show False by blast 
qed
*)

lemma clm_sing:"\<Turnstile>\<^bold>\<not>  (cl(c) \<^bold>\<smile> cl(c)) "
unfolding valid_def vchop_def satisfies_def cl_def  using atMostOneClm  restriction_add_clm vchop_def restriction_clm_leq_one    
  by (metis (no_types, hide_lams) add_eq_self_zero le_add1 le_antisym one_neq_zero)

lemma clm_sing_somewhere:"\<Turnstile>\<^bold>\<not>  \<^bold>\<langle>cl(c) \<^bold>\<smile> cl(c)\<^bold>\<rangle> "
unfolding valid_def  vchop_def hchop_def using clm_sing unfolding satisfies_def  valid_def vchop_def hchop_def by blast

lemma clm_sing_not_interrupted:"\<Turnstile> \<^bold>\<not>(cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile> cl(c))"
unfolding valid_def vchop_def satisfies_def  cl_def using atMostOneClm  restriction_add_clm vchop_def restriction_clm_leq_one clm_sing
  by (metis (no_types, hide_lams) add.commute add_eq_self_zero dual_order.antisym
      le_add1 one_neq_zero)

lemma clm_sing_somewhere2:"\<Turnstile>\<^bold>\<not>  (\<^bold>\<top> \<^bold>\<smile> cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile>  cl(c) \<^bold>\<smile> \<^bold>\<top>) " 
  using view.vchop_def clm_sing_not_interrupted vertical_chop_assoc1 unfolding valid_def vchop_def satisfies_def 
  by meson

lemma clm_sing_somewhere3:"\<Turnstile>\<^bold>\<not>  \<^bold>\<langle>(\<^bold>\<top> \<^bold>\<smile> cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile>  cl(c) \<^bold>\<smile> \<^bold>\<top>)\<^bold>\<rangle> "  
  using clm_sing_somewhere2  unfolding valid_def  satisfies_def vchop_def hchop_def   by blast


lemma clm_at_most_somewhere:"\<Turnstile>\<^bold>\<not> (\<^bold>\<langle>cl(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>cl(c)\<^bold>\<rangle>)"
proof  -
  {
  fix ts v
  assume assm:"ts,v \<Turnstile>  (\<^bold>\<langle>cl(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>cl(c)\<^bold>\<rangle>)"
  obtain vu and vd 
    where chops:"(v=vu--vd)\<and> (ts,vu \<Turnstile>\<^bold>\<langle>cl(c)\<^bold>\<rangle>) \<and> ( ts,vd \<Turnstile> \<^bold>\<langle> cl(c)\<^bold>\<rangle>)" unfolding vchop_def hchop_def satisfies_def
    using assm unfolding vchop_def hchop_def satisfies_def by blast
  from chops have clm_vu:"|restrict vu (clm ts) c| \<ge> 1" unfolding vchop_def hchop_def satisfies_def cl_def
    by (metis restriction_card_somewhere_mon)
  from chops have clm_vd:"|restrict vd (clm ts) c| \<ge> 1" unfolding vchop_def hchop_def satisfies_def cl_def
    by (metis restriction_card_somewhere_mon)
  from chops have clm_add:
    "|restrict v (clm ts) c | = |restrict vu (clm ts) c| + |restrict vd (clm ts) c|"
    using restriction_add_clm      by auto
  with clm_vu and clm_vd have "|restrict v (clm ts) c | \<ge> 2" 
    using add.commute add_eq_self_zero dual_order.antisym le_add1 less_one not_le
      restriction_res_leq_two
    by linarith
  with restriction_clm_leq_one have False     
    by (metis One_nat_def not_less_eq_eq numeral_2_eq_2)
}
  from this show ?thesis using hmlsl.valid_def hmlsl_axioms unfolding vchop_def hchop_def satisfies_def 
     by fastforce
qed




lemma res_decompose: "\<Turnstile>(re(c)  \<^bold>\<rightarrow> re(c) \<^bold>\<frown> re(c))" 
proof - 
  {
  fix ts v
  assume assm:"ts,v \<Turnstile>re(c)"
  then obtain v1 and v2 
    where 1:"v=v1\<parallel>v2" and 2:"\<parallel>ext v1\<parallel> > 0" and 3:"\<parallel>ext v2\<parallel> > 0" unfolding satisfies_def re_def 
    using  view.horizontal_chop_non_empty  by blast
  then have 4:"|lan v1| = 1" and 5:"|lan v2| = 1"
    using assm view.hchop_def unfolding satisfies_def re_def by auto
  then have 6:"ts,v1 \<Turnstile>re(c)"  using  assm unfolding satisfies_def hchop_def re_def 
    by (metis 2 1  len_view_hchop_left  restriction.restrict_eq_lan_subs
        restriction.restrict_view restriction.restriction_stable1)
  from 5 have 7:"ts,v2 \<Turnstile>re(c)" using  assm "6" unfolding satisfies_def hchop_def re_def
    by (metis "1" "3"   len_view_hchop_right restriction.restrict_eq_lan_subs
        restriction.restrict_view restriction.restriction_stable)
  from 1 and 6 and 7 have "ts,v \<Turnstile>re(c) \<^bold>\<frown> re(c)" unfolding satisfies_def hchop_def by blast
}
  from this show ?thesis 
    using hmlsl.satisfies_def hmlsl.valid_def hmlsl_axioms by auto
qed

lemma res_compose: "\<Turnstile>(re(c) \<^bold>\<frown> re(c)  \<^bold>\<rightarrow> re(c))"     
  unfolding valid_def  hchop_def using  real_int.chop_dense len_compose_hchop view.hchop_def length_dense restrict_def
unfolding valid_def hchop_def satisfies_def re_def
  by (metis (no_types, lifting))

lemma res_dense:"\<Turnstile>re(c) \<^bold>\<leftrightarrow> re(c) \<^bold>\<frown> re(c)"
  using res_decompose res_compose unfolding valid_def satisfies_def by blast

lemma res_continuous :"\<Turnstile>(re(c)) \<^bold>\<rightarrow> (\<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown> ( \<^bold>\<not>re(c) \<^bold>\<and> \<^bold>\<l> > 0) \<^bold>\<frown> \<^bold>\<top>))"     
unfolding valid_def hchop_def satisfies_def re_def  by (metis (no_types, lifting) view.hchop_def len_view_hchop_left len_view_hchop_right
      restrict_def)

lemma no_clm_before_res:"\<Turnstile>\<^bold>\<not>(cl(c) \<^bold>\<frown> re(c))"  
unfolding valid_def  hchop_def satisfies_def re_def cl_def by (metis (no_types, lifting) nat_int.card_empty_zero nat_int.card_subset_le
      disjoint view.hchop_def inf_assoc inf_le1 not_one_le_zero restrict_def)

lemma no_clm_before_res2:"\<Turnstile>\<^bold>\<not> (cl(c) \<^bold>\<frown> \<^bold>\<top> \<^bold>\<frown> re(c))"
  unfolding valid_def hchop_def satisfies_def re_def cl_def
  by (metis (no_types, lifting) inf.idem nat_int.card_non_empty_geq_one restriction.restrict_def restriction.restriction_clm_leq_one restriction_clm_res_disjoint view.hchop_def)
(*proof (rule allI| rule impI)+
  fix ts v
  show "ts,v \<Turnstile> \<^bold>\<not> (cl(c) \<^bold>\<frown> \<^bold>\<top> \<^bold>\<frown> re(c))"
  proof (rule ccontr)
  assume "\<not> (ts,v \<Turnstile> \<^bold>\<not> (cl(c) \<^bold>\<frown> \<^bold>\<top> \<^bold>\<frown> re(c)))"
  then obtain ts and v where assm:"ts,v \<Turnstile> (cl(c) \<^bold>\<frown> \<^bold>\<top> \<^bold>\<frown> re(c))" unfolding valid_def by blast
 
  then have clm_subs:"restrict v (clm ts) c = restrict v (res ts) c"
    using restriction_stable
    by (metis (no_types, lifting) hchop_def restrict_def)      
  have "restrict v (clm ts )c \<noteq> \<emptyset>" 
    using assm nat_int.card_non_empty_geq_one restriction_stable1
    by auto
  then have res_in_neq:"restrict v (clm ts) c \<sqinter> restrict v (res ts) c \<noteq>\<emptyset>"
    using clm_subs inf_absorb1
    by (simp )   
  then show False  using valid_def restriction_clm_res_disjoint      
    by (metis inf_commute restriction.restriction_clm_res_disjoint)    
  qed 
qed 
*)
lemma clm_decompose: "\<Turnstile>(cl(c)  \<^bold>\<rightarrow> cl(c) \<^bold>\<frown> cl(c))" 
proof -
  {
  fix ts v
  assume assm: "ts,v \<Turnstile> cl(c)"
  have restr:"restrict v (clm ts) c = lan v" using assm unfolding satisfies_def cl_def by simp
  have len_ge_zero:"\<parallel>len v ts c\<parallel> > 0" using assm unfolding satisfies_def cl_def by simp
  have len:"len v ts c = ext v" using assm unfolding satisfies_def cl_def by simp
  obtain v1 v2 where chop:"(v=v1\<parallel>v2) \<and> \<parallel>ext v1\<parallel> > 0 \<and> \<parallel>ext v2\<parallel> > 0 " 
    using assm view.horizontal_chop_non_empty    
    using length_split unfolding hchop_def satisfies_def cl_def by blast    
  from chop and len have len_v1:"len v1 ts c = ext v1" 
    using len_view_hchop_left by blast
  from chop and len have len_v2:"len v2 ts c = ext v2" 
    using len_view_hchop_right by blast
  from chop and restr have restr_v1:"restrict v1 (clm ts) c = lan v1"      
    by (metis (no_types, lifting) view.hchop_def restriction.restriction_stable1)     
  from chop and restr have restr_v2:"restrict v2 (clm ts) c = lan v2"     
    by (metis (no_types, lifting) view.hchop_def restriction.restriction_stable2) 
  from chop and len_v1 len_v2 restr_v1 restr_v2 have "ts,v \<Turnstile>cl(c) \<^bold>\<frown> cl(c)"
    using view.hchop_def assm unfolding satisfies_def hchop_def cl_def by force
}
  from this show ?thesis unfolding valid_def satisfies_def
    using hmlsl.satisfies_def hmlsl_axioms by blast
qed


lemma clm_compose: "\<Turnstile>(cl(c) \<^bold>\<frown> cl(c)  \<^bold>\<rightarrow> cl(c))" 
  using  real_int.chop_dense len_compose_hchop view.hchop_def length_dense restrict_def     
unfolding valid_def hchop_def satisfies_def cl_def
  by (metis (no_types, lifting))

lemma clm_dense:"\<Turnstile>cl(c) \<^bold>\<leftrightarrow> cl(c) \<^bold>\<frown> cl(c)"
   using clm_decompose clm_compose unfolding valid_def satisfies_def by blast

lemma clm_continuous :"\<Turnstile>(cl(c)) \<^bold>\<rightarrow> (\<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( \<^bold>\<not>cl(c) \<^bold>\<and> \<^bold>\<l> > 0) \<^bold>\<frown> \<^bold>\<top>))"     
unfolding valid_def hchop_def satisfies_def  cl_def by (metis (no_types, lifting) view.hchop_def len_view_hchop_left len_view_hchop_right
      restrict_def)


lemma res_not_free: "\<Turnstile>(\<^bold>\<exists> c. re(c) \<^bold>\<rightarrow> \<^bold>\<not>free)" 
unfolding valid_def satisfies_def  using nat_int.card_empty_zero one_neq_zero re_def by auto

lemma clm_not_free: "\<Turnstile>(\<^bold>\<exists> c. cl(c) \<^bold>\<rightarrow> \<^bold>\<not>free)"
unfolding valid_def  satisfies_def using nat_int.card_empty_zero cl_def by auto

lemma free_no_res:"\<Turnstile>(free \<^bold>\<rightarrow>  \<^bold>\<not>(\<^bold>\<exists> c. re(c)))" 
unfolding valid_def  satisfies_def re_def using nat_int.card_empty_zero one_neq_zero 
  by (metis less_irrefl)

lemma free_no_clm:"\<Turnstile>(free \<^bold>\<rightarrow>  \<^bold>\<not>(\<^bold>\<exists> c. cl(c)))" 
unfolding valid_def  satisfies_def cl_def using nat_int.card_empty_zero one_neq_zero by (metis less_irrefl)

lemma free_decompose:"\<Turnstile>free \<^bold>\<rightarrow> ( free \<^bold>\<frown> free)"
proof - 
  {
  fix ts v
  assume assm:"ts,v \<Turnstile>free"
  obtain v1 and v2 
    where non_empty_v1_v2:"(v=v1\<parallel>v2) \<and> \<parallel>ext v1\<parallel> > 0 \<and> \<parallel>ext v2\<parallel> > 0"
    unfolding valid_def using assm length_dense unfolding valid_def satisfies_def hchop_def by blast
  have one_lane:"|lan v1| = 1 \<and> |lan v2| = 1" 
    using assm view.hchop_def non_empty_v1_v2 unfolding satisfies_def hchop_def
    by auto
  have nothing_on_v1:
    " (\<forall>c. \<parallel>len v1 ts c\<parallel> = 0 
        \<or> (restrict v1 (clm ts) c = \<emptyset> \<and> restrict v1 (res ts) c = \<emptyset>))"  using assm unfolding satisfies_def
    by (metis (no_types, lifting) len_empty_on_subview1 non_empty_v1_v2
        restriction_stable1)
  have nothing_on_v2:
    " (\<forall>c. \<parallel>len v2 ts c\<parallel> = 0 
        \<or> (restrict v2 (clm ts) c = \<emptyset> \<and> restrict v2 (res ts) c = \<emptyset>))"   using assm unfolding satisfies_def
    by (metis (no_types, lifting)  len_empty_on_subview2 non_empty_v1_v2
        restriction_stable2)
  have  
    "(v=v1\<parallel>v2) 
    \<and> 0 < \<parallel>ext v1\<parallel> \<and> |lan v1| = 1 
    \<and> (\<forall>c. \<parallel>len v1 ts c\<parallel> = 0 
        \<or>( restrict v1 (clm ts) c = \<emptyset> \<and> restrict v1 (res ts) c = \<emptyset>))
    \<and> 0 < \<parallel>ext v2\<parallel> \<and> |lan v2| = 1
    \<and> (\<forall>c. \<parallel>len v2 ts c\<parallel> = 0 
        \<or>( restrict v2 (clm ts) c = \<emptyset> \<and> restrict v2 (res ts) c = \<emptyset>))"
    using non_empty_v1_v2 nothing_on_v1 nothing_on_v2 one_lane by blast      
  then have "ts,v \<Turnstile>(free \<^bold>\<frown> free)" unfolding satisfies_def hchop_def by blast
}
  from this show ?thesis unfolding valid_def 
    by (simp add: satisfies_def)
qed

lemma free_compose:"\<Turnstile>(free \<^bold>\<frown> free) \<^bold>\<rightarrow> free"
proof -
  {
  fix ts v
  assume assm:"ts,v \<Turnstile>free \<^bold>\<frown> free"
  have len_ge_0:"\<parallel>ext v\<parallel> > 0" 
    unfolding valid_def using assm length_meld unfolding valid_def satisfies_def hchop_def by blast
  have widt_one:"|lan v| = 1" using assm unfolding satisfies_def hchop_def    
    by (metis horizontal_chop_width_stable)
  have no_car:
    "(\<forall>c. \<parallel>len v ts c\<parallel> = 0 \<or> restrict v (clm ts) c = \<emptyset> \<and> restrict v (res ts) c = \<emptyset>)"  
  proof (rule ccontr)
    assume 
      "\<not>(\<forall>c. \<parallel>len v ts c\<parallel> = 0 
           \<or> (restrict v (clm ts) c = \<emptyset> \<and> restrict v (res ts) c = \<emptyset>))" 
    then obtain c 
      where ex:
        "\<parallel>len v ts c\<parallel> \<noteq> 0 \<and> (restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)" 
      by blast
    from ex have 1:"\<parallel>len v ts c\<parallel> > 0" 
      using less_eq_real_def real_int.length_ge_zero by auto
    have "(restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)" using ex ..
    then show False
    proof
      assume "restrict v (clm ts) c \<noteq> \<emptyset>"
      then show False using assm unfolding satisfies_def hchop_def
        by (metis (no_types, hide_lams)  add.left_neutral ex len_hchop_add
            restriction.restrict_def view.hchop_def)    
    next
      assume "restrict v (res ts) c \<noteq> \<emptyset>"
      then show False using assm unfolding satisfies_def hchop_def
        by (metis (no_types, hide_lams)  add.left_neutral ex len_hchop_add 
            restriction.restrict_def view.hchop_def)  
    qed
  qed
  have "ts,v \<Turnstile>free"
    using len_ge_0 widt_one no_car unfolding satisfies_def by blast
}
  from this show ?thesis unfolding valid_def satisfies_def by blast
qed


lemma free_dense:"\<Turnstile>free \<^bold>\<leftrightarrow> (free \<^bold>\<frown> free)"
 using free_decompose free_compose unfolding valid_def satisfies_def by blast

lemma free_dense2:"\<Turnstile>free \<^bold>\<rightarrow> \<^bold>\<top> \<^bold>\<frown> free \<^bold>\<frown> \<^bold>\<top>"
unfolding valid_def hchop_def satisfies_def  using horizontal_chop_empty_left horizontal_chop_empty_right  by fastforce

text \<open>
The next lemmas show the connection between the spatial. In particular,
if the view consists of one lane and a non-zero extension, where neither
a reservation nor a car resides, the view satisfies free (and vice versa). 
\<close>
(*
lemma no_cars_means_free:
  "\<Turnstile>((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))) \<^bold>\<rightarrow> free" 
proof -
  {
  fix ts v
  assume assm:
    "ts,v \<Turnstile> ((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))"
  have ge_0:"ts,v \<Turnstile> \<^bold>\<l> > 0" using assm unfolding satisfies_def by best
  have one_lane:"ts,v \<Turnstile>\<^bold>\<omega> = 1" using assm unfolding satisfies_def  by best    
  have "ts,v \<Turnstile> free" unfolding satisfies_def 
  proof (rule ccontr)
    have no_car: "ts,v \<Turnstile>\<^bold>\<not>( \<^bold>\<exists> c.  (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))"
      using assm unfolding satisfies_def  by best
    assume "ts,v \<Turnstile> \<^bold>\<not> free"
    hence contra:
      "\<not>(\<forall>c. \<parallel>len v ts c\<parallel> = 0 \<or> restrict v (clm ts) c = \<emptyset> \<and> restrict v (res ts) c = \<emptyset>)"
      using ge_0 one_lane unfolding satisfies_def  by blast
    hence ex_car:
      "\<exists>c. \<parallel>len v ts c\<parallel> > 0 \<and> (restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)" 
      using real_int.length_ge_zero dual_order.antisym not_le 
      by metis
    obtain c where c_def:
      "\<parallel>len v ts c\<parallel> > 0 \<and> (restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)"       
      using ex_car by blast
    hence "(restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)" by best
    thus False 
    proof
      assume "restrict v (clm ts) c \<noteq> \<emptyset>"
      with one_lane have clm_one:"|restrict v (clm ts) c| = 1" 
        using el_in_restriction_clm_singleton      
        by (metis card_non_empty_geq_one dual_order.antisym restriction.restriction_clm_leq_one)
      obtain v1 and v2 and v3 and v4 
        where "v=v1\<parallel>v2" and "v2=v3\<parallel>v4" 
          and len_eq:"len v3 ts c = ext v3 \<and> \<parallel>len v3 ts c\<parallel> = \<parallel>len v ts c\<parallel> " 
        using horizontal_chop_empty_left horizontal_chop_empty_right 
          len_fills_subview c_def by blast
      then have res_non_empty:"restrict v3 (clm ts) c \<noteq> \<emptyset>" 
        using \<open>restrict v (clm ts) c \<noteq> \<emptyset>\<close> restriction_stable restriction_stable1
        by auto
      have len_non_empty:"\<parallel>len v3 ts c\<parallel> > 0" 
        using len_eq c_def by auto
      have "|restrict v3 (clm ts) c| =1 " 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> clm_one restriction_stable restriction_stable1
        by auto
      have v3_one_lane:"|lan v3| = 1" 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> hchop_def one_lane
        by auto
      have clm_fills_v3:"restrict v3 (clm ts) c = lan v3" 
      proof (rule ccontr)
        assume  aux:"restrict v3 (clm ts) c \<noteq> lan v3"
        have "restrict v3 (clm ts) c \<sqsubseteq> lan v3"      
          by (simp add: restrict_view)
        hence "\<exists>n. n \<^bold>\<notin> restrict v3 (clm ts) c \<and> n \<^bold>\<in> lan v3" 
          using aux \<open>|restrict v3 (clm ts) c| = 1\<close> 
            restriction.restrict_eq_lan_subs v3_one_lane
          by auto
        hence "|lan v3| > 1" 
          using \<open>| (restrict v3 (clm ts) c)| = 1\<close> \<open>restrict v3 (clm ts) c \<le> lan v3\<close> aux
            restriction.restrict_eq_lan_subs v3_one_lane
          by auto
        thus False using v3_one_lane by auto
      qed
      have "\<parallel>ext v3\<parallel> > 0" using c_def len_eq by auto
      have "ts, v3 \<Turnstile> cl(c)" using clm_one len_eq c_def clm_fills_v3 v3_one_lane
        by auto
      hence "ts,v \<Turnstile>  (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> by blast
      hence "ts,v \<Turnstile>\<^bold>\<exists> c. (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" by blast
      thus False using no_car by best
    next
      assume "restrict v (res ts) c \<noteq> \<emptyset>"
      with one_lane have clm_one:"|restrict v (res ts) c| = 1" 
        using el_in_restriction_clm_singleton      
        by (metis nat_int.card_non_empty_geq_one nat_int.card_subset_le 
            dual_order.antisym restrict_view)
      obtain v1 and v2 and v3 and v4 
        where "v=v1\<parallel>v2" and "v2=v3\<parallel>v4" 
          and len_eq:"len v3 ts c = ext v3 \<and> \<parallel>len v3 ts c\<parallel> = \<parallel>len v ts c\<parallel> " 
        using horizontal_chop_empty_left horizontal_chop_empty_right 
          len_fills_subview c_def by blast
      then have res_non_empty:"restrict v3 (res ts) c \<noteq> \<emptyset>" 
        using \<open>restrict v (res ts) c \<noteq> \<emptyset>\<close> restriction_stable restriction_stable1
        by auto
      have len_non_empty:"\<parallel>len v3 ts c\<parallel> > 0" 
        using len_eq c_def by auto
      have "|restrict v3 (res ts) c| =1 " 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> clm_one restriction_stable restriction_stable1
        by auto
      have v3_one_lane:"|lan v3| = 1" 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> hchop_def one_lane
        by auto
      have "restrict v3 (res ts) c = lan v3" 
      proof (rule ccontr)
        assume  aux:"restrict v3 (res ts) c \<noteq> lan v3"
        have "restrict v3 (res ts) c \<sqsubseteq> lan v3"      
          by (simp add: restrict_view)
        hence "\<exists>n. n \<^bold>\<notin> restrict v3 (res ts) c \<and> n \<^bold>\<in> lan v3"
          using aux \<open>|restrict v3 (res ts) c| = 1\<close> restriction.restrict_eq_lan_subs v3_one_lane
          by auto
        hence "|lan v3| > 1" 
          using \<open>| (restrict v3 (res ts) c)| = 1\<close> \<open>restrict v3 (res ts) c \<le> lan v3\<close> aux
            restriction.restrict_eq_lan_subs v3_one_lane
          by auto
        thus False using v3_one_lane by auto
      qed
      have "\<parallel>ext v3\<parallel> > 0" using c_def len_eq by auto
      have "ts, v3 \<Turnstile> re(c)" 
        using clm_one len_eq c_def \<open>restrict v3 (res ts) c = lan v3\<close> v3_one_lane
        by auto
      hence "ts,v \<Turnstile>  (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> by blast
      hence "ts,v \<Turnstile>\<^bold>\<exists> c. (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" by blast
      thus False using no_car by best
    qed
  qed
qed

lemma free_means_no_cars:
  "\<Turnstile>free \<^bold>\<rightarrow> ((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))" 
  unfolding valid_def
proof (rule allI | rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile> free"
  have no_car:"ts,v \<Turnstile>(\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))"
  proof (rule ccontr)
    assume "\<not> (ts,v \<Turnstile>(\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))"
    hence contra:"ts,v \<Turnstile> \<^bold>\<exists> c. \<^bold>\<top> \<^bold>\<frown> (cl(c) \<^bold>\<or> re(c)) \<^bold>\<frown> \<^bold>\<top>" by blast
    from this obtain c and v1 and v' and v2 and vc where 
      vc_def:"(v=v1\<parallel>v') \<and> (v'=vc\<parallel>v2) \<and> (ts,vc \<Turnstile> cl(c) \<^bold>\<or> re(c))" by blast
    hence len_ge_zero:"\<parallel>len v ts c\<parallel> > 0" 
      by (metis len_empty_on_subview1 len_empty_on_subview2 less_eq_real_def
          real_int.length_ge_zero)
    from vc_def have vc_ex_car:
      "restrict vc (clm ts) c \<noteq> \<emptyset> \<or> restrict vc (res ts) c \<noteq>\<emptyset>" 
      using nat_int.card_empty_zero one_neq_zero by auto
    have eq_lan:"lan v = lan vc" using vc_def hchop_def by auto
    hence v_ex_car:"restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq>\<emptyset>" 
      using vc_ex_car by (simp add: restrict_def)
    from len_ge_zero and v_ex_car and assm show False by force
  qed
  with assm show 
    "ts,v \<Turnstile>((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))"
    by blast
qed

lemma free_eq_no_cars:
  "\<Turnstile>free \<^bold>\<leftrightarrow> ((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))" 
unfolding valid_def   using no_cars_means_free free_means_no_cars unfolding valid_def by blast

lemma free_nowhere_res:"\<Turnstile>free \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<top> \<^bold>\<frown> (re(c)) \<^bold>\<frown> \<^bold>\<top>)"
unfolding valid_def  using free_eq_no_cars unfolding valid_def by blast

lemma two_res_not_res: "\<Turnstile>((re(c) \<^bold>\<smile> re(c)) \<^bold>\<rightarrow> \<^bold>\<not>re(c))" 
  unfolding valid_def  
  using view.vertical_chop_singleton by fastforce

lemma two_clm_width: "\<Turnstile>((cl(c) \<^bold>\<smile> cl(c)) \<^bold>\<rightarrow> \<^bold>\<omega> = 2)"
  unfolding valid_def  
  using view.vertical_chop_add1 by auto

lemma two_res_no_car: "\<Turnstile>(re(c) \<^bold>\<smile> re(c)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> c. ( cl(c) \<^bold>\<or> re(c)) )" 
unfolding valid_def sledgehammer
  using view.vertical_chop_singleton by force 

lemma two_lanes_no_car:"\<Turnstile>(\<^bold>\<not> \<^bold>\<omega>= 1) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> c.(cl(c) \<^bold>\<or> re(c)))"
unfolding valid_def  by simp

lemma empty_no_car:"\<Turnstile>( \<^bold>\<l> = 0) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> c.(cl(c) \<^bold>\<or> re(c)))"
unfolding valid_def  by simp

lemma car_one_lane_non_empty: "\<Turnstile>(\<^bold>\<exists> c.(cl(c) \<^bold>\<or> re(c))) \<^bold>\<rightarrow> ((\<^bold>\<omega> =1) \<^bold>\<and> (\<^bold>\<l> > 0))"
unfolding valid_def  by blast

lemma one_lane_notfree:
  "\<Turnstile>(\<^bold>\<omega> =1) \<^bold>\<and>(\<^bold>\<l>> 0) \<^bold>\<and> (\<^bold>\<not> free) \<^bold>\<rightarrow> ( (\<^bold>\<top> \<^bold>\<frown> (\<^bold>\<exists> c. (re(c) \<^bold>\<or> cl(c))) \<^bold>\<frown> \<^bold>\<top> ))"
  unfolding valid_def
proof (rule allI|rule impI)+
  fix ts v
  assume assm:"ts,v \<Turnstile>(\<^bold>\<omega> =1) \<^bold>\<and>(\<^bold>\<l>> 0) \<^bold>\<and> (\<^bold>\<not> free)"
  hence not_free:"ts,v \<Turnstile>\<^bold>\<not> free" by blast
  with free_eq_no_cars have 
    "ts,v \<Turnstile>\<^bold>\<not> ((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))"
   unfolding valid_def by blast
  hence "ts,v \<Turnstile> \<^bold>\<not>  (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))" 
    using assm by blast
  thus "ts,v \<Turnstile>(\<^bold>\<top> \<^bold>\<frown> (\<^bold>\<exists> c. (re(c) \<^bold>\<or> cl(c))) \<^bold>\<frown> \<^bold>\<top> )" by blast
qed

lemma one_lane_empty_or_car:
  "\<Turnstile>(\<^bold>\<omega> =1) \<^bold>\<and>(\<^bold>\<l>> 0) \<^bold>\<rightarrow> (free \<^bold>\<or> (\<^bold>\<top> \<^bold>\<frown> (\<^bold>\<exists> c. (re(c) \<^bold>\<or> cl(c))) \<^bold>\<frown> \<^bold>\<top> ))"
unfolding valid_def  using one_lane_notfree unfolding valid_def by blast
end
*)
lemma valid_imp_sat: \<open>\<Turnstile> \<phi> \<Longrightarrow> ts,v \<Turnstile> \<phi>\<close>
  by (simp add: valid_def)

end
end