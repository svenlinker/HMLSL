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

locale hmlsl = restriction+sensors
(*  fixes sensors::"cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real" 
  assumes sensors_ge:"(sensors e ts c) > 0"  *)
begin
(*end

(*sublocale hmlsl<sensors 
  by (simp add: sensors.intro sensors_ge)*)

context hmlsl

begin
*)
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
definition mexists1 ::  "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder "\<^bold>\<exists>!"[8]9) 
  where "\<^bold>\<exists>! x. \<phi>(x) \<equiv> \<lambda>ts w. \<exists>!x. \<phi>(x)(ts)(w)"
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

definition free:: "\<sigma>" ("free")
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
    and minorP: "ts,v \<Turnstile> P \<Longrightarrow> R"
    and minorQ: "ts,v \<Turnstile> Q \<Longrightarrow> R"
  shows "R" 
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

lemma mnot_mnotE: "(ts,v \<Turnstile>\<^bold>\<not>\<^bold>\<not>P) = (ts,v \<Turnstile>P)" 
  using mnotE mnotI2 by blast

lemma mclassical:
  assumes prem: "ts,v \<Turnstile> \<^bold>\<not> P \<Longrightarrow> ts,v \<Turnstile> P"
  shows "ts,v \<Turnstile>P"  
  using mnotI prem by blast

lemmas mccontr = mFalseE [THEN mclassical]


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

subsubsection \<open>Quantifiers\<close>
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


lemma mexI: "ts,v \<Turnstile> P x \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<exists>x::'a. P x"
  by (metis mexistsB_def mexists_def satisfies_def)

lemma mexE:
  assumes major: "ts,v \<Turnstile>\<^bold>\<exists>x::'a. P x"
    and minor: "\<And>x. ts,v \<Turnstile> P x \<Longrightarrow> Q"
  shows "Q"
  by (metis major mexistsB_def mexists_def minor satisfies_def)

lemma mex1I:
  assumes "ts,v \<Turnstile>P a" "\<And>x. ts,v \<Turnstile> P x \<Longrightarrow> ts,v \<Turnstile>x \<^bold>= a"
  shows "ts,v \<Turnstile> \<^bold>\<exists>! x. P x"
  by (metis assms(1) assms(2) meq_def mexists1_def satisfies_def)


lemma mex_ex1I:
  assumes ex_prem: "ts,v \<Turnstile> \<^bold>\<exists> x. P x"
    and eq: "\<And>x y. \<lbrakk>ts,v \<Turnstile>P x; ts,v \<Turnstile>P y\<rbrakk> \<Longrightarrow> ts,v \<Turnstile>x \<^bold>=  y"
  shows "ts,v \<Turnstile>\<^bold>\<exists>!x. P x"
  by (metis eq ex_prem mex1I mexE)

lemma mex1E:
  assumes major: "ts,v \<Turnstile>\<^bold>\<exists>!x. P x"
    and minor: "\<And>x. \<lbrakk>ts,v \<Turnstile>P x; ts,v \<Turnstile>\<^bold>\<forall>y. P y \<^bold>\<rightarrow> y \<^bold>= x\<rbrakk> \<Longrightarrow> R"
  shows R
proof -
  from major have "\<And>x y. \<lbrakk>ts,v \<Turnstile>P x; ts,v \<Turnstile>P y\<rbrakk> \<Longrightarrow> ts,v \<Turnstile>x \<^bold>=  y"
    by (metis meq_def mexists1_def satisfies_def)
  then have "\<And>x. ts,v \<Turnstile>P x \<Longrightarrow> ts,v \<Turnstile>\<^bold>\<forall>y. P y \<^bold>\<rightarrow> y \<^bold>= x" 
    by (simp add: mallI mimpI) 
  then show "R" using minor 
    by (metis (no_types, lifting) hmlsl.mexists1_def hmlsl_axioms major satisfies_def)
qed

lemma mex1_implies_mex: "ts,v \<Turnstile>\<^bold>\<exists>!x. P x \<Longrightarrow> ts,v \<Turnstile>\<^bold>\<exists>x. P x"
  apply (erule mex1E)
  apply (rule mexI)
  apply assumption
  done




subsubsection\<open>True (2)\<close>

lemma mTrueE: "ts,v \<Turnstile> \<^bold>\<top> \<Longrightarrow> ts',v' \<Turnstile> P \<Longrightarrow> ts',v' \<Turnstile> P" .
lemma mnotFalseE: "ts,v \<Turnstile> \<^bold>\<not> \<^bold>\<bottom> \<Longrightarrow> ts',v' \<Turnstile>P \<Longrightarrow> ts',v' \<Turnstile> P" .




subsubsection\<open>Equational\<close>

lemma mrefl:" ts,v \<Turnstile> x \<^bold>= x" 
  by (simp add: meq_def satisfies_def) 

lemma rigid_eq:" x = y \<Longrightarrow> ts,v \<Turnstile> x \<^bold>= y" 
  by (simp add: mrefl)


subsubsection\<open>Modal Operators\<close>
lemma hchopE: 
  assumes "ts,v \<Turnstile>P \<^bold>\<frown> Q " 
  obtains u and w 
    where "v=u\<parallel>w" and "ts,u \<Turnstile> P" and "ts,w \<Turnstile> Q" 
  using assms hchop_def satisfies_def by auto

lemma hchopI: "v=u\<parallel>w \<Longrightarrow> ts,u \<Turnstile>P \<Longrightarrow> ts,w \<Turnstile> Q \<Longrightarrow> ts,v \<Turnstile> P \<^bold>\<frown> Q" 
  using hchop_def satisfies_def by auto

lemma vchopE: 
  assumes "ts,v \<Turnstile>P \<^bold>\<smile> Q " 
  obtains u and w 
    where "v=u--w" and "ts,u \<Turnstile> P" and "ts,w \<Turnstile> Q" 
  using assms vchop_def satisfies_def by auto

lemma vchopI: "v=u--w \<Longrightarrow> ts,u \<Turnstile>P \<Longrightarrow> ts,w \<Turnstile> Q \<Longrightarrow> ts,v \<Turnstile> P \<^bold>\<smile> Q" 
  using vchop_def satisfies_def by auto

lemma someE: 
  assumes "ts,v \<Turnstile>\<^bold>\<langle> P \<^bold>\<rangle> " 
  obtains u  
  where "u \<le> v" and "ts,u \<Turnstile> P" 
proof -
   obtain v1 v2 vl vr where 1: " (v=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (ts,v2 \<Turnstile> \<^bold>\<top> \<^bold>\<smile> P \<^bold>\<smile> \<^bold>\<top>)" 
    using hchop_def satisfies_def  somewhere_def assms by auto  
  then obtain v3 vu vd v' where 2:"(v=vl\<parallel>v1) \<and> (v1=v2\<parallel>vr) \<and> (v2=vd--v3) \<and> (v3=v'--vu) \<and> (ts,v' \<Turnstile> P)" 
    using  satisfies_def vchop_def assms by auto
  then have "v' \<le> v" using somewhere_leq 1 2 by blast
  then show ?thesis using that 2 by blast
qed

lemma someI:" u \<le> v \<Longrightarrow> ts,u \<Turnstile> P \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<langle> P \<^bold>\<rangle>" 
  using somewhere_def somewhere_leq  hchopI mTrueI vchopI by auto

lemma atE:
  assumes "ts,v \<Turnstile> \<^bold>@c P" 
  obtains u
  where "v =c> u" and "ts,u \<Turnstile> P" 
  by (metis assms at_def satisfies_def view.switch_exists)

lemma atI:
  "\<lbrakk>\<And>u. v =c> u \<Longrightarrow> ts,u \<Turnstile> P\<rbrakk> \<Longrightarrow> ts,v \<Turnstile> \<^bold>@c P" 
  by (simp add: at_def satisfies_def)


subsubsection\<open>Global Invariants\<close>
lemma globallyE: 
  assumes major: " ts,v \<Turnstile> \<^bold>G P" 
    and relation:" ts \<^bold>\<Rightarrow> ts'" 
  shows " ts',(move ts ts' v) \<Turnstile> P"  
  using globally_def major relation satisfies_def by auto

lemma globallyI:
  assumes "\<And>ts'. ts \<^bold>\<Rightarrow> ts' \<Longrightarrow> ts', (move ts ts' v) \<Turnstile> P" 
  shows "ts,v \<Turnstile> \<^bold>G P" 
  using assms globally_def satisfies_def by auto

lemma crResE:
  assumes major:"ts,v \<Turnstile>\<^bold>\<box>r(c) P" 
  and relation: "ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts'" 
  shows "ts',v \<Turnstile>P" 
  using res_box_def major relation satisfies_def by auto

lemma crResI:
  assumes "\<And>ts'. ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts' \<Longrightarrow> ts', v \<Turnstile> P" 
  shows "ts,v \<Turnstile> \<^bold>\<box>r(c) P" 
  using assms res_box_def satisfies_def by auto 

lemma crClmE:
  assumes major:"ts,v \<Turnstile>\<^bold>\<box>c(c) P" 
  and relation: "ts \<^bold>\<midarrow>c(c,m)\<^bold>\<rightarrow>ts'" 
  shows "ts',v \<Turnstile>P" 
  using clm_box_def major relation satisfies_def by auto

lemma crClmI:
  assumes "\<And>ts' m. ts \<^bold>\<midarrow>c(c,m)\<^bold>\<rightarrow> ts' \<Longrightarrow> ts', v \<Turnstile> P" 
  shows "ts,v \<Turnstile> \<^bold>\<box>c(c) P" 
  using assms clm_box_def satisfies_def by auto 


lemma wdResE:
  assumes major:"ts,v \<Turnstile>\<^bold>\<box>wdr(c) P" 
  and relation: "ts \<^bold>\<midarrow>wdr(c,m)\<^bold>\<rightarrow>ts'" 
  shows "ts',v \<Turnstile>P" 
  using wdres_box_def major relation satisfies_def by auto

lemma wdResI:
  assumes "\<And>ts' m. ts \<^bold>\<midarrow>wdr(c,m)\<^bold>\<rightarrow> ts' \<Longrightarrow> ts', v \<Turnstile> P" 
  shows "ts,v \<Turnstile> \<^bold>\<box>wdr(c) P" 
  using assms wdres_box_def satisfies_def by auto 

lemma wdClmE:
  assumes major:"ts,v \<Turnstile>\<^bold>\<box>wdc(c) P" 
  and relation: "ts \<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow>ts'" 
  shows "ts',v \<Turnstile>P" 
  using wdclm_box_def major relation satisfies_def by auto

lemma wdClmI:
  assumes "\<And>ts'. ts \<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow> ts' \<Longrightarrow> ts', v \<Turnstile> P" 
  shows "ts,v \<Turnstile> \<^bold>\<box>wdc(c) P" 
  using assms wdclm_box_def satisfies_def by auto 


subsubsection\<open>Classical Reasoning\<close>
lemma mdisjCI:
  assumes "ts,v \<Turnstile>\<^bold>\<not> Q \<Longrightarrow> ts,v \<Turnstile>P"
  shows "ts,v \<Turnstile> P \<^bold>\<or> Q"
  by (rule mclassical) (iprover intro: assms mdisjI1 mdisjI2 mnotI elim: mnotE)

lemma mexcluded_middle: "ts,v \<Turnstile> \<^bold>\<not> P \<^bold>\<or> P"
  by (iprover intro: mdisjCI)

text \<open>Classical implies elimination.\<close>
lemma mimpCE:
  assumes major: "ts,v \<Turnstile>P \<^bold>\<rightarrow>  Q"
    and minor: "ts,v \<Turnstile> \<^bold>\<not> P \<Longrightarrow> R" "ts,v \<Turnstile>Q \<Longrightarrow> R"
  shows R  
  using major mclassical minor(1) minor(2) mrev_mp by blast

lemma miffCE:
  assumes major: "ts,v \<Turnstile>P \<^bold>\<leftrightarrow> Q"
    and minor: "\<lbrakk>ts,v \<Turnstile>P; ts,v \<Turnstile> Q\<rbrakk> \<Longrightarrow> R" "\<lbrakk>ts,v \<Turnstile>\<^bold>\<not> P; ts,v \<Turnstile>\<^bold>\<not> Q\<rbrakk> \<Longrightarrow> R"
  shows R
  by (rule major [THEN miffE]) (iprover intro: minor elim: mimpCE mnotE)

lemma mexCI:
  assumes "ts,v \<Turnstile> \<^bold>\<forall>x. \<^bold>\<not> P x \<Longrightarrow> ts,v \<Turnstile>P a"
  shows "ts,v \<Turnstile>\<^bold>\<exists> x. P x"  
  by (metis assms mallI mclassical mexI)

(*lemmas [elim!] = mimpCE mdisjE miffCE  mFalseE mconjE mexE mTrueE mnotFalseE globallyE hchopE vchopE someE atE 
  and [intro!] = mdisjCI mexCI miffI mconjI mimpI mTrueI mnotI mallI mrefl globallyI hchopI vchopI someI atI
  and [elim 2] = mallE 
  and [intro] = mexI mdisjI2 mdisjI1
*)
declare miffI [intro!]
  and mnotI [intro!]
  and mimpI [intro!]
  and mdisjCI [intro!]
  and mconjI [intro!]
  and mTrueI [intro!]
  and mrefl [intro!]

declare miffCE [elim!]
  and mFalseE [elim!]
  and mimpCE [elim!]
  and mdisjE [elim!]
  and mconjE [elim!]

bundle chop_rules = hchopE [elim!] vchopE [elim!]   hchopI [intro!] vchopI [intro!]
bundle somewhere_rules =    someE [elim!]    someI [intro!]
bundle spatial_rules =  hchopE [elim!] vchopE [elim!]   hchopI [intro!] vchopI [intro!]  someE [elim!]    someI [intro!]
   atE [elim!] atI [intro!]

bundle dynamic_rules =
   globallyE [elim!]
   crResE [elim!]
   crClmE [elim!]
   wdResE [elim!]
   wdClmE [elim!]
   globallyI [intro!]
   crResI [intro!]
   crClmI [intro!]
   wdResI [intro!]
   wdClmI [intro!]

declare mex_ex1I [intro!]
  and mallI [intro!]
  and mexI [intro]

declare mexE [elim!]
  mallE [elim]

print_facts

lemma mimp_cong: "ts,v \<Turnstile>(P \<^bold>\<leftrightarrow> P') \<Longrightarrow> (ts,v \<Turnstile> P' \<Longrightarrow> (ts,v \<Turnstile> Q \<^bold>\<leftrightarrow> Q')) \<Longrightarrow> ((ts,v \<Turnstile> P \<^bold>\<rightarrow> Q) \<longleftrightarrow> (ts,v \<Turnstile>P' \<^bold>\<rightarrow> Q'))" 
  by (metis miffD1 miffD2 mimpE mimpI)


lemma miff_mexI:
  assumes "\<And>x. (ts,v \<Turnstile> P x) = (ts,v \<Turnstile> Q x)"
  shows "(ts,v \<Turnstile> \<^bold>\<exists> x. P x) = (ts,v \<Turnstile>\<^bold>\<exists> x. Q x)"
  using assms by blast

lemma miff_mallI:
  assumes "\<And>x. (ts,v \<Turnstile> P x) = (ts,v \<Turnstile> Q x)"
  shows "(ts,v \<Turnstile> \<^bold>\<forall> x. P x) = (ts,v \<Turnstile>\<^bold>\<forall> x. Q x)"
  using assms by blast

declare                       mimp_cong[cong]
                      miff_mexI[cong] 
                      miff_mallI[cong]





subsubsection\<open>HMLSL Simplifier Rules\<close>

lemma iff_atomize[atomize]:"((ts,v \<Turnstile>P) = (ts,v \<Turnstile>Q)) \<equiv> (ts,v \<Turnstile>P \<^bold>\<leftrightarrow> Q)" 
  by (simp add: mequ_def satisfies_def)

print_facts

lemma not_not: "ts,v \<Turnstile>(\<^bold>\<not> \<^bold>\<not> P) \<^bold>\<leftrightarrow> P"   
  using miffI mnot_mnotE by (presburger)
lemma Not_eq_iff: "(ts,v \<Turnstile> ((\<^bold>\<not> P) \<^bold>\<leftrightarrow> (\<^bold>\<not>  Q))) = (ts,v \<Turnstile>P \<^bold>\<leftrightarrow> Q)"
  by (simp add: mequ_def mnot_def)

lemma prop_simps[simp]:
    "((ts,v \<Turnstile> P) \<noteq> (ts,v \<Turnstile>Q)) == ((ts,v \<Turnstile> P) = (ts,v \<Turnstile>\<^bold>\<not>Q))" 
    "ts,v \<Turnstile> P \<^bold>\<or> \<^bold>\<not>P == True" 
    "ts,v \<Turnstile> \<^bold>\<not>P \<^bold>\<or> P == True" 
    "ts,v \<Turnstile> x \<^bold>= x == True"   
    "ts,v \<Turnstile> \<^bold>\<not> \<^bold>\<top> == ts,v \<Turnstile>\<^bold>\<bottom>" 
    "ts,v \<Turnstile>\<^bold>\<not> \<^bold>\<bottom> == ts,v \<Turnstile> \<^bold>\<top>" 
    "(ts,v \<Turnstile> \<^bold>\<not>P) \<noteq> (ts,v \<Turnstile>P)" 
    "(ts,v \<Turnstile>  P) \<noteq> (ts,v \<Turnstile>\<^bold>\<not>P)" 
    "ts,v \<Turnstile>(\<^bold>\<top> \<^bold>\<leftrightarrow> P) == ts,v \<Turnstile> P"
    "ts,v \<Turnstile>(P \<^bold>\<leftrightarrow> \<^bold>\<top>) == ts,v \<Turnstile> P"
    "ts,v \<Turnstile>(\<^bold>\<bottom> \<^bold>\<leftrightarrow> P) == ts,v \<Turnstile> (\<^bold>\<not> P)"
    "ts,v \<Turnstile>(P \<^bold>\<leftrightarrow> \<^bold>\<bottom>) == ts,v \<Turnstile> (\<^bold>\<not> P)"
    "ts,v \<Turnstile> (\<^bold>\<top> \<^bold>\<rightarrow> P) == ts,v \<Turnstile> P"  
    "ts,v \<Turnstile> (\<^bold>\<bottom> \<^bold>\<rightarrow> P) == True"
    "ts,v \<Turnstile>(P \<^bold>\<rightarrow> \<^bold>\<top>) == True"  
    "ts,v \<Turnstile>(P \<^bold>\<rightarrow> P) == True"
    "ts,v \<Turnstile>(P \<^bold>\<rightarrow> \<^bold>\<bottom>) == ts,v \<Turnstile> (\<^bold>\<not> P)"  
    "ts,v \<Turnstile>(P \<^bold>\<rightarrow> \<^bold>\<not> P) == ts,v \<Turnstile> (\<^bold>\<not> P)"
    "ts,v \<Turnstile>(P \<^bold>\<and> \<^bold>\<top>) == ts,v \<Turnstile> P"  
    "ts,v \<Turnstile>(\<^bold>\<top> \<^bold>\<and> P) == ts,v \<Turnstile> P"
    "ts,v \<Turnstile>(P \<^bold>\<and> \<^bold>\<bottom>) == False"  
    "ts,v \<Turnstile>(\<^bold>\<bottom> \<^bold>\<and> P) == False"
    "ts,v \<Turnstile>(P \<^bold>\<and> P) == ts,v \<Turnstile> P"  
    "ts,v \<Turnstile>(P \<^bold>\<and> (P \<^bold>\<and> Q)) == ts,v \<Turnstile>(P \<^bold>\<and> Q)"
    "ts,v \<Turnstile>(P \<^bold>\<and> \<^bold>\<not> P) == False"    
    "ts,v \<Turnstile>(\<^bold>\<not> P \<^bold>\<and> P) == False"
    "ts,v \<Turnstile>(P \<^bold>\<or> \<^bold>\<top>) == True"  
    "ts,v \<Turnstile>(\<^bold>\<top> \<^bold>\<or> P) == True"
    "ts,v \<Turnstile>(P \<^bold>\<or> \<^bold>\<bottom>) == ts,v \<Turnstile> P"  
    "ts,v \<Turnstile>(\<^bold>\<bottom> \<^bold>\<or> P) == ts,v \<Turnstile> P"
    "ts,v \<Turnstile>(P \<^bold>\<or> P) == ts,v \<Turnstile> P "  
    "ts,v \<Turnstile>(P \<^bold>\<or> (P \<^bold>\<or> Q)) == ts,v \<Turnstile>(P \<^bold>\<or> Q)"
  by (simp add: satisfies_def mimp_def mtrue_def mfalse_def mnot_def mand_def mor_def mequ_def meq_def)+

lemma quant_simps[simp]:
    "ts,v \<Turnstile>(\<^bold>\<forall>x. P) == ts,v \<Turnstile> P"  
    "ts,v \<Turnstile>(\<^bold>\<exists> x. P) == ts,v \<Turnstile> P"  
    "ts,v \<Turnstile> \<^bold>\<exists> x. x \<^bold>= t"  
    "ts,v \<Turnstile> \<^bold>\<exists> x. t \<^bold>= x"
    "\<And>P. (ts,v \<Turnstile> \<^bold>\<exists> x. x \<^bold>= t \<^bold>\<and> P x) == ts,v \<Turnstile> P t"  
    "\<And>P. (ts,v \<Turnstile> \<^bold>\<exists> x. t \<^bold>= x \<^bold>\<and> P x) == ts,v \<Turnstile> P t"
    "\<And>P. (ts,v \<Turnstile> \<^bold>\<forall> x. x \<^bold>= t \<^bold>\<rightarrow> P x) == ts,v \<Turnstile> P t"
    "\<And>P. (ts,v \<Turnstile> \<^bold>\<forall> x. t \<^bold>= x \<^bold>\<rightarrow> P x) == ts,v \<Turnstile> P t"
    "ts,v \<Turnstile> (\<^bold>\<forall>x. \<^bold>\<not> x \<^bold>= t) == False"  
    "ts,v \<Turnstile> (\<^bold>\<forall>x. \<^bold>\<not> t \<^bold>= x) == False" 
  by (simp add: mand_def meq_def mexistsB_def mexists_def mforallB_def mforall_def mimp_def satisfies_def mnot_def)+

lemma de_Morgan_mdisj: "(ts,v \<Turnstile> \<^bold>\<not> (P \<^bold>\<or> Q)) \<longleftrightarrow> (ts,v \<Turnstile>\<^bold>\<not> P \<^bold>\<and> \<^bold>\<not> Q)" 
  using hmlsl.mor_def hmlsl_axioms mand_def mnot_def by auto
lemma de_Morgan_mconj: "(ts,v \<Turnstile> \<^bold>\<not> (P \<^bold>\<and> Q)) \<longleftrightarrow> (ts,v \<Turnstile> \<^bold>\<not> P \<^bold>\<or> \<^bold>\<not> Q)" 
  using hmlsl.mor_def hmlsl_axioms mand_def mnot_def by auto

lemma mall_not_mex: "(ts,v \<Turnstile> (\<^bold>\<forall>x. P x)) \<longleftrightarrow> (ts,v \<Turnstile> \<^bold>\<not> ( \<^bold>\<exists> x. \<^bold>\<not> P x))" 
  by (metis   mclassical mexE mexI mexistsB_def mforallB_def mforall_def mnotE mnot_def satisfies_def)

lemma not_mall: "(ts,v \<Turnstile> \<^bold>\<not>(\<^bold>\<forall>x. P x)) \<longleftrightarrow> (ts,v \<Turnstile> ( \<^bold>\<exists> x. \<^bold>\<not> P x))" 
  by (metis   mclassical mexE mexI mexistsB_def mforallB_def mforall_def mnotE mnot_def satisfies_def)

(*lemma mimp_mall :"(ts,v \<Turnstile>( \<^bold>\<forall>x. Px) \<^bold>\<rightarrow> Q) \<longleftrightarrow> (ts,v \<Turnstile> \<^bold>\<exists> x. ( P x \<^bold>\<rightarrow> Q))  "*) 

lemma not_mex: "(ts,v \<Turnstile> \<^bold>\<not> (\<^bold>\<exists> x. P x)) == (ts,v \<Turnstile>(\<^bold>\<forall>x. \<^bold>\<not> P x))" 
  by (simp add: satisfies_def mexistsB_def mforallB_def mforall_def mexists_def mnot_def)

(*lemma mimp_mex: "(ts,v \<Turnstile> ((\<^bold>\<exists> x. P x) \<^bold>\<rightarrow> Q)) \<longleftrightarrow> (ts,v \<Turnstile> \<^bold>\<forall>x.( P x \<^bold>\<rightarrow> Q))" 
  by (metis (mono_tags, lifting) mallE mallI mimpE' mimpI mnotE' mnotI2 not_m ex) 
*)







lemma disj_imp: "(ts,v \<Turnstile> P \<^bold>\<or> Q) \<longleftrightarrow>  (ts,v \<Turnstile>\<^bold>\<not> P \<^bold>\<rightarrow> Q)" 
   using hmlsl.mnotE' hmlsl_axioms by blast

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


bundle hmlsl_simps =  
                      de_Morgan_mconj[simp]
                      de_Morgan_mdisj[simp]
                      mall_not_mex[simp] 
                      not_mall[simp] 
                      not_mex[simp] 
(*                      mimp_mex[simp] *)
                      mnot_mnotE[simp]
                      hchop_neg1[simp]
                      hchop_neg2[simp]

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

lemma vchop_leq1: 
  assumes "ts,v \<Turnstile> \<phi> \<^bold>\<smile> \<psi>"
  shows "\<exists>v'. v' \<le> v \<and> (ts, v' \<Turnstile>\<phi>)" 
  by (meson assms vchopE view.vertical_chop_leq1)

lemma vchop_leq2: 
  assumes "ts,v \<Turnstile> \<phi> \<^bold>\<smile> \<psi>"
  shows "\<exists> v'. v' \<le> v \<and> (ts, v' \<Turnstile>\<psi>)" 
  by (meson assms vchopE view.vertical_chop_leq2)


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
  using view.switch_exists view.switch_refl 
  by (metis atI mexI)
(*proof -
  assume a: "ts,v \<Turnstile> \<phi>"
  obtain d where d_def:"d=own v" by blast
  then have "v =d> v" 
    by (simp add: view.switch_refl)
  have "\<And>u. (v =d> u) \<longrightarrow> u = v" using switch_unique 
    using d_def view.switch_def by blast
  then have "ts,v \<Turnstile> \<^bold>@d \<phi>" 
    using a at_def satisfies_def by auto
  then show "ts,v \<Turnstile> (\<^bold>\<exists> c. \<^bold>@c \<phi>)" 
    by (meson mexI) 
qed
*)
(*proof
  fix ts v
  assume assm:"ts,v \<Turnstile>\<phi>"
  obtain d where d_def:"d=own v" by blast
  then have "ts,v \<Turnstile> \<^bold>@d \<phi>" using assm switch_refl switch_unique unfolding  satisfies_def   by fastforce
  show "ts,v \<Turnstile> (\<^bold>\<exists> c. \<^bold>@c \<phi>)"
qed
*)

lemma at_conj_distr:"(ts,v \<Turnstile>\<^bold>@c ( \<phi> \<^bold>\<and> \<psi>)) = ( ts,v \<Turnstile> (\<^bold>@c \<phi>) \<^bold>\<and> (\<^bold>@c \<psi>))" 
  using at_def mand_def satisfies_def by auto

lemma at_disj_dist:"(ts,v \<Turnstile>\<^bold>@c (\<phi> \<^bold>\<or> \<psi>)) = (ts,v \<Turnstile> (\<^bold>@c \<phi> )  \<^bold>\<or> ( \<^bold>@c \<psi> ))"  
  by (metis  at_def mor_def satisfies_def switch_exists)

lemma at_hchop_dist1:"ts,v \<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>)) \<Longrightarrow> ts,v \<Turnstile>  ((\<^bold>@c \<phi>) \<^bold>\<frown> (\<^bold>@c \<psi>))"  
proof -  
  assume assm:"ts, v \<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>))"
  obtain v' where v':"v=c>v'" using switch_exists  by fastforce
  with assm obtain v1' and v2'
    where chop:"(v'=v1'\<parallel>v2') \<and> (ts,v1' \<Turnstile> \<phi>) \<and> (ts,v2'\<Turnstile>\<psi>)" 
    unfolding satisfies_def   using hchop_def at_def by auto 
  from chop and v' obtain v1 and v2 
    where origin:"(v1=c>v1') \<and> (v2=c>v2') \<and> (v=v1\<parallel>v2)" 
    using switch_hchop2  by fastforce
  hence v1:"ts,v1 \<Turnstile> (\<^bold>@c \<phi>)" and v2:"ts,v2 \<Turnstile> (\<^bold>@c \<psi>)" 
    unfolding satisfies_def  using switch_unique chop at_def unfolding satisfies_def  by fastforce+   
  from  v1 and v2 and origin show "ts,v \<Turnstile>(\<^bold>@c \<phi>) \<^bold>\<frown> (\<^bold>@c \<psi>)"  unfolding satisfies_def hchop_def by blast
qed

lemma at_hchop_dist2:"ts,v \<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<frown> (\<^bold>@c \<psi>)) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>))  " 
proof -
  assume a:"ts,v \<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<frown> (\<^bold>@c \<psi>))"
  then obtain v1 and v2
    where chop:"(v=v1\<parallel>v2) \<and> (ts,v1 \<Turnstile> \<^bold>@c \<phi>) \<and> (ts,v2\<Turnstile> \<^bold>@c \<psi>)" 
    using hchop_def satisfies_def by auto
  then obtain v' and v1' and v2' where 1:"v =c>v'" and "v'=v1'\<parallel>v2'" and "ts,v1' \<Turnstile> \<phi>" and "ts,v2' \<Turnstile>\<psi>"  
    by (metis at_def satisfies_def view.switch_exists switch_hchop1)
  then have "ts,v' \<Turnstile> \<phi> \<^bold>\<frown> \<psi>" 
    using hchop_def satisfies_def by auto
  then show "ts,v \<Turnstile> (\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>))  " 
    using at_def satisfies_def 1 view.switch_unique by metis
qed

lemma at_hchop_dist:"(ts,v \<Turnstile>(\<^bold>@c \<phi>) \<^bold>\<frown>  (\<^bold>@c \<psi>)) = (ts,v \<Turnstile>\<^bold>@c (\<phi> \<^bold>\<frown> \<psi>))  "
  using at_hchop_dist1 at_hchop_dist2 
  by meson

lemma at_vchop_dist1:"ts,v \<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>)) \<Longrightarrow> ts,v \<Turnstile> ( (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>))"
proof -
  fix ts v
  assume assm:"ts, v \<Turnstile>(\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>))"
  obtain v' where v':"v=c>v'" using switch_exists by fastforce
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
  from v1 and v2 and origin show "ts,v \<Turnstile> (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>)" unfolding satisfies_def 
    using vchop_def by auto
qed

lemma at_vchop_dist2:"ts,v \<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>)) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>))  "
proof -
  assume a:"ts,v \<Turnstile>( (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>))"
  then obtain v1 and v2
    where chop:"(v=v1--v2) \<and> (ts,v1 \<Turnstile> \<^bold>@c \<phi>) \<and> (ts,v2\<Turnstile> \<^bold>@c \<psi>)" 
    using vchop_def satisfies_def by auto
  then obtain v' and v1' and v2' where 1:"v =c>v'" and "v'=v1'--v2'" and "ts,v1' \<Turnstile> \<phi>" and "ts,v2' \<Turnstile>\<psi>"  
    by (metis at_def satisfies_def view.switch_exists switch_vchop1)
  then have "ts,v' \<Turnstile> \<phi> \<^bold>\<smile> \<psi>" 
    using vchop_def satisfies_def by auto
  then show "ts,v \<Turnstile> (\<^bold>@c (\<phi> \<^bold>\<smile> \<psi>))  " 
    using at_def satisfies_def 1 view.switch_unique by metis
qed
  

lemma at_vchop_dist:"(ts,v \<Turnstile>  (\<^bold>@c \<phi>) \<^bold>\<smile> (\<^bold>@c \<psi>)) = (ts,v \<Turnstile> \<^bold>@c (\<phi> \<^bold>\<smile> \<psi>))  "
  using at_vchop_dist1 at_vchop_dist2 by meson

lemma eq_rigid:" (c = d) = (ts,v \<Turnstile> c \<^bold>= d)" 
  by (simp add: meq_def satisfies_def)

lemma at_eq:"(ts,v \<Turnstile> \<^bold>@e c \<^bold>= d) = (ts,v \<Turnstile> c \<^bold>= d)" 
  using eq_rigid 
  by (metis at_def satisfies_def switch_exists)

(*lemma at_eq':"\<Turnstile>(\<^bold>@e c \<^bold>= d) \<^bold>\<leftrightarrow> (c \<^bold>= d)"
  unfolding valid_def satisfies_def using switch_exists   
  by (metis at_def meq_def mequ_def)
*)

lemma at_neg1:"ts,v \<Turnstile>(\<^bold>@c \<^bold>\<not> \<phi>) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<not> (\<^bold>@c \<phi>)"
  using satisfies_def  switch_unique  at_def 
  by (metis mnotE mnotI2 view.switch_exists)

lemma at_neg2:"ts,v \<Turnstile>\<^bold>\<not> (\<^bold>@c \<phi> ) \<Longrightarrow> ts,v \<Turnstile> ( (\<^bold>@c \<^bold>\<not> \<phi>))"
  using satisfies_def  switch_unique  at_def 
  by (metis mnotE mnotI2 view.switch_exists)

lemma at_neg :"(ts,v \<Turnstile>\<^bold>@c( \<^bold>\<not> \<phi>)) = (ts,v \<Turnstile> \<^bold>\<not> (\<^bold>@c \<phi>))" 
  by (meson at_neg1 at_neg2)

lemma at_neg':"ts,v \<Turnstile> \<^bold>\<not> (\<^bold>@c \<phi>) \<^bold>\<leftrightarrow> (\<^bold>@c( \<^bold>\<not> \<phi>))" 
  by (simp add: at_neg1 at_neg2 miffI)
  

lemma at_neg_neg1:"ts,v \<Turnstile>(\<^bold>@c \<phi>) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<not>(\<^bold>@c \<^bold>\<not> \<phi>)"   
  using at_neg1 mnot_def satisfies_def by auto

lemma at_neg_neg2:"ts,v \<Turnstile>\<^bold>\<not>(\<^bold>@c \<^bold>\<not> \<phi>) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>@c  \<phi>)" 
  using at_neg2 mnot_def satisfies_def by auto

lemma at_neg_neg:"(ts,v \<Turnstile> \<^bold>@c \<phi>) = (ts,v \<Turnstile> \<^bold>\<not>(\<^bold>@c \<^bold>\<not> \<phi>))" 
  by (meson at_neg_neg1 at_neg_neg2)

lemma globally_all_iff:"(ts,v \<Turnstile> (\<^bold>G(\<^bold>\<forall>c. \<phi>))) = (ts,v \<Turnstile> \<^bold>\<forall>c.( \<^bold>G \<phi>))" 
  using globallyE 
  by (metis hmlsl.globallyI hmlsl_axioms mallI mspec)

lemma globally_all_iff':"ts,v\<Turnstile> (\<^bold>G(\<^bold>\<forall>c. \<phi>)) \<^bold>\<leftrightarrow> (\<^bold>\<forall>c.( \<^bold>G \<phi>))" 
  by (metis globally_all_iff )

lemma globally_refl:" ts,v \<Turnstile>(\<^bold>G \<phi>) \<Longrightarrow> ts,v \<Turnstile> \<phi>" 
  using globallyE abstract.refl 
  by (metis view.move_nothing)

lemma globally_4: "ts,v \<Turnstile> (\<^bold>G  \<phi>) \<Longrightarrow> ts,v \<Turnstile> \<^bold>G \<^bold>G \<phi>"
  using globallyE globallyI traffic.abs_trans traffic.move_trans by presburger
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

lemma spatial_weaken: "ts,v \<Turnstile> \<phi> \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<langle>\<phi>\<^bold>\<rangle>" 
  using somewhere_leq by auto

lemma spatial_weaken2:"ts,v \<Turnstile> (\<phi> \<^bold>\<rightarrow> \<psi>) \<Longrightarrow> ts,v \<Turnstile> (\<phi> \<^bold>\<rightarrow> \<^bold>\<langle>\<psi>\<^bold>\<rangle>)"
  by (meson mimpE mimpI spatial_weaken)

lemma somewhere_distr: "(ts,v \<Turnstile> \<^bold>\<langle>\<phi>\<^bold>\<or>\<psi>\<^bold>\<rangle>) = (ts,v \<Turnstile> \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle>\<psi>\<^bold>\<rangle> )" 
  using mor_def satisfies_def somewhere_leq by auto

lemma somewhere_and:"ts,v \<Turnstile> \<^bold>\<langle>\<phi> \<^bold>\<and> \<psi>\<^bold>\<rangle> \<Longrightarrow> ts,v \<Turnstile>  \<^bold>\<langle>\<phi>\<^bold>\<rangle> \<^bold>\<and> \<^bold>\<langle>\<psi>\<^bold>\<rangle>"
  using somewhere_leq by auto

lemma somewhere_and_or_distr :"(ts,v \<Turnstile>\<^bold>\<langle> \<chi> \<^bold>\<and> (\<phi> \<^bold>\<or> \<psi>) \<^bold>\<rangle>) = (ts,v \<Turnstile> \<^bold>\<langle> \<chi> \<^bold>\<and>  \<phi> \<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> \<chi> \<^bold>\<and> \<psi> \<^bold>\<rangle>)" 
proof
  assume "ts,v \<Turnstile>\<^bold>\<langle> \<chi> \<^bold>\<and> (\<phi> \<^bold>\<or> \<psi>) \<^bold>\<rangle>"
  then obtain v' where "v' \<le> v" and "ts,v' \<Turnstile> \<chi> \<^bold>\<and> (\<phi> \<^bold>\<or> \<psi>)" 
    using somewhere_leq 
    by meson
  then have "ts,v' \<Turnstile> (\<chi> \<^bold>\<and>  \<phi>) \<^bold>\<or> (\<chi> \<^bold>\<and> \<psi>)" 
    by (metis mconjI mconjunct1 mconjunct2 mdisjE mdisjI1 mdisjI2)
  then have "ts,v \<Turnstile> \<^bold>\<langle> (\<chi> \<^bold>\<and>  \<phi>) \<^bold>\<or> (\<chi> \<^bold>\<and> \<psi>) \<^bold>\<rangle>" 
    using \<open>v' \<le> v\<close> somewhere_leq 
    by meson
  then show "ts,v \<Turnstile> \<^bold>\<langle> \<chi> \<^bold>\<and>  \<phi> \<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> \<chi> \<^bold>\<and> \<psi> \<^bold>\<rangle>" using somewhere_distr 
    by simp
next
  assume "ts,v \<Turnstile> \<^bold>\<langle> \<chi> \<^bold>\<and>  \<phi> \<^bold>\<rangle> \<^bold>\<or> \<^bold>\<langle> \<chi> \<^bold>\<and> \<psi> \<^bold>\<rangle>" 
  then show "ts,v \<Turnstile>\<^bold>\<langle> \<chi> \<^bold>\<and> (\<phi> \<^bold>\<or> \<psi>) \<^bold>\<rangle>" 
    by (metis (full_types) mconjI mconjunct1 mconjunct2 mdisjE mdisjI1 mdisjI2 somewhere_leq)
qed

lemma width_add1:"ts,v \<Turnstile>(\<^bold>\<omega> = x) \<^bold>\<smile> (\<^bold>\<omega> = y) \<Longrightarrow> (ts,v \<Turnstile> \<^bold>\<omega> = x+y)"  
  using satisfies_def vertical_chop_add1 width_eq_def 
  by (metis (mono_tags, lifting) vchopE)

lemma width_add2:"ts,v \<Turnstile>(\<^bold>\<omega> = x+y) \<Longrightarrow> ts,v \<Turnstile>  (\<^bold>\<omega> = x) \<^bold>\<smile> (\<^bold>\<omega> = y)"
  using satisfies_def  width_eq_def vchop_def view.vertical_chop_add2 by auto

lemma width_hchop_stable: "(ts,v \<Turnstile>(\<^bold>\<omega> = x)) = (ts,v \<Turnstile> (\<^bold>\<omega> = x) \<^bold>\<frown> (\<^bold>\<omega>=x))"
  by (metis (mono_tags, hide_lams) hchopI hmlsl.hchopE hmlsl_axioms horizontal_chop_empty_right horizontal_chop_lanes_stable satisfies_def width_eq_def)

lemma length_geq_zero:"ts,v \<Turnstile> (\<^bold>\<l> \<ge> 0)" 
proof -
  have "\<parallel>ext v\<parallel> \<ge> 0" 
    by (simp add: length_ge_zero)
  then show "ts,v \<Turnstile> (\<^bold>\<l> \<ge> 0)" 
    using hmlsl.length_eq_def hmlsl_axioms length_ge_def length_geq_def mor_def satisfies_def by auto
qed

lemma length_split: "ts,v \<Turnstile>(\<^bold>\<l> > 0) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<l> > 0) \<^bold>\<frown> (\<^bold>\<l> > 0)" 
  by (metis  hchopI length_ge_def satisfies_def view.horizontal_chop_non_empty)

lemma length_meld: "ts,v \<Turnstile>(\<^bold>\<l> > 0) \<^bold>\<frown> (\<^bold>\<l> > 0) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<l> > 0)"
proof -
  assume "ts,v \<Turnstile>(\<^bold>\<l> > 0) \<^bold>\<frown> (\<^bold>\<l> > 0)" 
  then obtain u and w where "v=u\<parallel>w" and "\<parallel>ext u\<parallel> > 0" and "\<parallel>ext w \<parallel> > 0" 
    using length_ge_def  
    by (metis hchopE satisfies_def)
  then have "\<parallel>ext v\<parallel> > 0" 
    using chop_add_length_ge_0 view.hchop_def by blast
  then show "ts,v \<Turnstile> (\<^bold>\<l> > 0)" 
    using length_ge_def satisfies_def by auto
qed

lemma length_dense:"(ts,v \<Turnstile>(\<^bold>\<l> > 0)) = (ts,v \<Turnstile> (\<^bold>\<l> > 0) \<^bold>\<frown> (\<^bold>\<l> > 0))" 
  by (meson length_meld length_split)

lemma length_add1:"ts,v \<Turnstile>(\<^bold>\<l>=x) \<^bold>\<frown> (\<^bold>\<l>= y) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<l>= x+y" 
proof -
  assume "ts,v \<Turnstile>(\<^bold>\<l>=x) \<^bold>\<frown> (\<^bold>\<l>= y)"
  then obtain v1 and v2 where "v=v1\<parallel>v2" and "ts,v1 \<Turnstile>\<^bold>\<l> = x" and "ts,v2 \<Turnstile> \<^bold>\<l>=y" 
    using  hchopE by blast
  then have "\<parallel>ext v\<parallel> = x + y " 
    by (simp add: length_def length_eq_def rchop_def satisfies_def view.hchop_def)
  then show " ts,v \<Turnstile> \<^bold>\<l>= x+y" 
    by (simp add: length_def length_eq_def  satisfies_def )
qed

lemma length_add2:"ts,v \<Turnstile> (x \<^bold>\<ge> 0 \<^bold>\<and> y \<^bold>\<ge> 0)  \<Longrightarrow> ts,v \<Turnstile>  (\<^bold>\<l>=x+y) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<l>=x) \<^bold>\<frown> (\<^bold>\<l>=y)" 
proof -
  assume 1:"ts,v \<Turnstile>  (x \<^bold>\<ge> 0 \<^bold>\<and> y \<^bold>\<ge> 0)" and 2:" ts,v \<Turnstile>  (\<^bold>\<l>=x+y)" 
  from 1 have "x \<ge> 0 \<and> y \<ge> 0" 
    by (meson mconjunct1 mconjunct2 mgeq_def satisfies_def)
  then obtain u and w where " v=u\<parallel>w" and "ts,u \<Turnstile>  (\<^bold>\<l>=x)" and " ts,w \<Turnstile>  (\<^bold>\<l>=y)"
    using 2 horizontal_chop_split_add 
    by (metis length_eq_def  satisfies_def )
  then show "ts,v \<Turnstile> (\<^bold>\<l>=x) \<^bold>\<frown> (\<^bold>\<l>=y)" 
    using hchopI by auto
qed

lemma length_add:"ts,v \<Turnstile> (x \<^bold>\<ge> 0 \<^bold>\<and> y \<^bold>\<ge> 0) \<Longrightarrow>  (ts,v \<Turnstile>\<^bold>\<l>=x+y) = (ts,v \<Turnstile> (\<^bold>\<l>=x) \<^bold>\<frown> (\<^bold>\<l>=y))"
   using length_add1 length_add2 by meson

lemma length_vchop_stable:"(ts,v \<Turnstile> \<^bold>\<l> = x) =  (ts,v \<Turnstile>(\<^bold>\<l> = x) \<^bold>\<smile> ( \<^bold>\<l> = x))" 
proof
  assume a:"ts,v \<Turnstile> \<^bold>\<l> = x"
  then have 1:"\<parallel>ext v\<parallel> = x" 
    by (simp add: length_eq_def satisfies_def) 
   obtain u and w where "v=u--w" and "\<parallel>ext u \<parallel> = x " and "\<parallel>ext w\<parallel> = x" 
     by (metis "1" a v_chop_weaken1 vchopE view.vertical_chop_length_stable)
  then show "ts,v \<Turnstile>(\<^bold>\<l> = x) \<^bold>\<smile> ( \<^bold>\<l> = x)" 
    using length_eq_def satisfies_def vchopI by auto
next
  assume "ts,v \<Turnstile>(\<^bold>\<l> = x) \<^bold>\<smile> ( \<^bold>\<l> = x)" 
  then show "ts,v \<Turnstile>(\<^bold>\<l> = x)" 
    using length_eq_def satisfies_def view.vchop_def 
    by (metis vchopE)
qed

lemma res_ge_zero:"ts,v \<Turnstile>re(c) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<l>>0" 
  by (simp add: length_ge_def re_def satisfies_def) 

lemma clm_ge_zero:"ts,v \<Turnstile>cl(c) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<l>>0"
  by (simp add: length_ge_def cl_def satisfies_def) 

lemma free_ge_zero:"ts,v \<Turnstile>free \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<l>>0"
  by (simp add: length_ge_def free_def satisfies_def)

lemma width_res:"ts,v \<Turnstile>re(c) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<omega> = 1"
  by (simp add: re_def satisfies_def width_eq_def)

lemma width_clm:"ts,v \<Turnstile>cl(c) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<omega> = 1"
  by (simp add: cl_def satisfies_def width_eq_def)

lemma width_free:"ts,v \<Turnstile>free \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<omega> = 1"
  by (simp add: free_def satisfies_def width_eq_def)

lemma width_somewhere_res:"ts,v \<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<omega> \<ge> 1" 
  using leq_lan re_def satisfies_def width_geq_def 
  using somewhere_leq by fastforce

lemma clm_disj_res:
 includes spatial_rules
 shows "ts,v \<Turnstile> \<^bold>\<not> \<^bold>\<langle> cl(c) \<^bold>\<and> re(c) \<^bold>\<rangle>" 
proof  
  assume "ts,v \<Turnstile>\<^bold>\<langle>cl(c) \<^bold>\<and> re(c)\<^bold>\<rangle>"
  then obtain v' where "v' \<le> v \<and> (ts,v' \<Turnstile> cl(c) \<^bold>\<and> re(c))"  by blast
  then have "ts,v' \<Turnstile> \<^bold>\<bottom>"  using disjoint  
    by (metis card_non_empty_geq_one hmlsl.cl_def hmlsl.re_def hmlsl_axioms inf.idem mand_def order_refl restriction_clm_res_disjoint satisfies_def)
  then show "ts,v \<Turnstile> \<^bold>\<bottom>" 
    by auto
qed

lemma width_ge:"ts,v \<Turnstile> (\<^bold>\<omega>> 0) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<exists> x. (\<^bold>\<omega> = x) \<^bold>\<and> (x \<^bold>> 0))"
proof -
  assume a: "ts,v \<Turnstile> (\<^bold>\<omega>> 0)" 
  obtain x where x:"ts,v \<Turnstile> \<^bold>\<omega> = x" 
    by (simp add: satisfies_def width_eq_def)
  then have "x > 0" using a 
    using satisfies_def vchop_def vertical_chop_add1 width_eq_def width_ge_def by auto
  then have "ts,v \<Turnstile>  (\<^bold>\<omega> = x ) \<^bold>\<and> x \<^bold>> 0" 
    by (metis hmlsl.mge_def hmlsl_axioms mconjI satisfies_def x)
  then show ?thesis 
    by blast
qed

lemma two_res_width: 
 includes spatial_rules
 shows "ts,v \<Turnstile>re(c) \<^bold>\<smile> re(c) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<omega> = 2"
  using hmlsl.re_def hmlsl_axioms satisfies_def vertical_chop_add1 width_eq_def by force


lemma res_at_most_two:"ts,v \<Turnstile>\<^bold>\<not> (re(c) \<^bold>\<smile>  re(c)  \<^bold>\<smile>  re(c) )" 
proof 
  assume "ts, v \<Turnstile> (re(c) \<^bold>\<smile>  re(c)  \<^bold>\<smile>  re(c) )"
  then obtain v' and v1 and v2 and v3  
    where "v = v1--v'" and "v'=v2--v3" 
    and "ts,v1 \<Turnstile>re(c)" and "ts,v2 \<Turnstile>re(c)" and "ts,v3 \<Turnstile>re(c)" 
    unfolding satisfies_def  using vchop_def by auto
  then show "ts,v \<Turnstile> \<^bold>\<bottom>"  
  proof -
    have "|restrict v' (res ts) c| < |restrict v (res ts) c|"
      using \<open>ts,v1 \<Turnstile>re(c)\<close> \<open>v=v1--v'\<close> restriction.restriction_add_res unfolding satisfies_def re_def by auto
    then show ?thesis unfolding satisfies_def vchop_def using  \<open>ts,v2 \<Turnstile> re(c)\<close> \<open>ts,v3 \<Turnstile>re(c)\<close> \<open>v'=v2--v3\<close> not_less 
          one_add_one restriction_add_res restriction_res_leq_two unfolding satisfies_def re_def by metis
  qed
qed

lemma res_at_most_two2:
 includes spatial_rules
 shows "ts,v \<Turnstile>\<^bold>\<not> \<^bold>\<langle>re(c) \<^bold>\<smile>  re(c)  \<^bold>\<smile>  re(c)\<^bold>\<rangle>" 
  using res_at_most_two  mnotE by blast

lemma res_at_most_somewhere:
 includes spatial_rules
 shows "ts,v \<Turnstile>\<^bold>\<not> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> " 
proof 
  assume assm:"ts,v \<Turnstile>  (\<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>re(c)\<^bold>\<rangle> )"
  obtain vu and v1 and vm and vd 
    where chops:"(v=vu--v1) \<and> (v1 = vm--vd)\<and> (ts,vu \<Turnstile>\<^bold>\<langle>re(c)\<^bold>\<rangle>) 
                 \<and> (ts,vm \<Turnstile> \<^bold>\<langle>re(c)\<^bold>\<rangle> ) \<and>( ts,vd \<Turnstile> \<^bold>\<langle> re(c)\<^bold>\<rangle>)"
    unfolding satisfies_def vchop_def hchop_def using assm unfolding hchop_def vchop_def satisfies_def by blast
  then obtain vu' and vm' and vd' where "vu' \<le> vu \<and> (ts,vu' \<Turnstile>re(c))" and "vm' \<le> vm \<and> (ts,vm' \<Turnstile>re(c)) " and "vd' \<le> vd \<and> (ts, vd' \<Turnstile> re(c))" 
    by blast
  then have 
    res_vu:"|restrict vu (res ts) c| \<ge> 1" 
    and  res_vm:"|restrict vm (res ts) c| \<ge> 1"
    and res_vd:"|restrict vd (res ts) c| \<ge> 1" using re_def somewhere_leq satisfies_def somewhere_def 
    by (metis restriction_card_leq_mon)+
  from chops have 
    "|restrict v (res ts) c | = 
     |restrict vu (res ts) c|+ |restrict vm (res ts) c| + |restrict vd (res ts) c| "
    using restriction_add_res by force
  with res_vu and res_vd res_vm have "|restrict v (res ts) c | \<ge> 3" 
    by linarith
  with restriction_res_leq_two show "ts,v \<Turnstile> \<^bold>\<bottom>"   
    by (metis not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3)
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

lemma clm_sing:
 includes spatial_rules
 shows "ts,v \<Turnstile>\<^bold>\<not>  (cl(c) \<^bold>\<smile> cl(c)) "
proof
  assume "ts,v \<Turnstile> cl(c) \<^bold>\<smile> cl(c)" 
  then obtain v1 and v2 where "v=v1--v2" and "ts,v1 \<Turnstile>cl(c)" and "ts,v2 \<Turnstile> cl(c)" 
    by blast
  then have "|restrict v (clm ts )  c| = 2"  using restriction_add_clm 
    using cl_def satisfies_def by auto 
  then show "ts,v \<Turnstile> \<^bold>\<bottom>" using atMostOneClm 
    by (metis numeral_le_one_iff restriction.restriction_clm_leq_one semiring_norm(69))
qed

lemma clm_sing_somewhere:
 includes spatial_rules
 shows "ts,v \<Turnstile>\<^bold>\<not>  \<^bold>\<langle>cl(c) \<^bold>\<smile> cl(c)\<^bold>\<rangle> " 
  using clm_sing mnotE by blast

lemma clm_sing_not_interrupted:
 includes spatial_rules
 shows "ts,v \<Turnstile> \<^bold>\<not>(cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile> cl(c))" 
proof
  assume "ts,v \<Turnstile> cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile> cl(c)"
  then obtain v1 and v2 and v3  and vm where "v=v1--vm" and "vm=v2--v3" and "ts,v1 \<Turnstile> cl(c)" and "ts,v3 \<Turnstile> cl(c)" by blast
  then have "|restrict v (clm ts) c| \<ge> 2" using restriction_add_clm cl_def satisfies_def by auto
  then show "ts,v \<Turnstile>\<^bold>\<bottom>" using atMostOneClm 
    by (metis Suc_1 not_less_eq_eq restriction.restriction_clm_leq_one)
qed

lemma clm_sing_somewhere2:
 includes spatial_rules
 shows "ts,v \<Turnstile>\<^bold>\<not>  ((\<^bold>\<top> \<^bold>\<smile> cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile>  cl(c)) \<^bold>\<smile> \<^bold>\<top>) " 
proof
  assume 1:"ts,v \<Turnstile>  (\<^bold>\<top> \<^bold>\<smile> cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile>  cl(c)) \<^bold>\<smile> \<^bold>\<top>"
  then obtain v3 where   "ts,v3 \<Turnstile> cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile> cl(c)" by blast
  then show "ts,v \<Turnstile> \<^bold>\<bottom> " using clm_sing_not_interrupted 
    using mnotE by blast
qed

lemma clm_sing_somewhere3:
 includes spatial_rules
 shows "ts,v \<Turnstile>\<^bold>\<not>  \<^bold>\<langle>(\<^bold>\<top> \<^bold>\<smile> cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile>  cl(c)) \<^bold>\<smile> \<^bold>\<top>\<^bold>\<rangle> "  
proof
  assume "ts,v \<Turnstile> \<^bold>\<langle>(\<^bold>\<top> \<^bold>\<smile> cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile>  cl(c)) \<^bold>\<smile> \<^bold>\<top>\<^bold>\<rangle> " 
  then obtain v' where "ts,v' \<Turnstile> (\<^bold>\<top> \<^bold>\<smile> cl(c) \<^bold>\<smile> \<^bold>\<top> \<^bold>\<smile>  cl(c)) \<^bold>\<smile> \<^bold>\<top>" by best
  then show "ts,v \<Turnstile> \<^bold>\<bottom>" 
  using clm_sing_somewhere2 mnotE by blast
qed


lemma clm_at_most_somewhere:
 includes spatial_rules
 shows "ts,v \<Turnstile>\<^bold>\<not> (\<^bold>\<langle>cl(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>cl(c)\<^bold>\<rangle>)" 
proof  
  assume assm:"ts,v \<Turnstile>  (\<^bold>\<langle>cl(c)\<^bold>\<rangle> \<^bold>\<smile> \<^bold>\<langle>cl(c)\<^bold>\<rangle>)"
  obtain vu and vd 
    where chops:"(v=vu--vd)\<and> (ts,vu \<Turnstile>\<^bold>\<langle>cl(c)\<^bold>\<rangle>) \<and> ( ts,vd \<Turnstile> \<^bold>\<langle> cl(c)\<^bold>\<rangle>)" 
    using assm vchop_def hchop_def  by blast
  from chops have clm_vu:"|restrict vu (clm ts) c| \<ge> 1" 
    by (metis cl_def restriction.restriction_card_leq_mon satisfies_def someE)
  from chops have clm_vd:"|restrict vd (clm ts) c| \<ge> 1" 
    by (metis cl_def restriction.restriction_card_leq_mon satisfies_def someE)
  from chops have clm_add:
    "|restrict v (clm ts) c | = |restrict vu (clm ts) c| + |restrict vd (clm ts) c|"
    using restriction_add_clm      by auto
  with clm_vu and clm_vd have "|restrict v (clm ts) c | \<ge> 2" 
    using add.commute add_eq_self_zero dual_order.antisym le_add1 less_one not_le
      restriction_res_leq_two
    by linarith
  with restriction_clm_leq_one show "ts,v \<Turnstile>\<^bold>\<bottom>"      
    by (metis One_nat_def not_less_eq_eq numeral_2_eq_2)
qed




lemma res_decompose: 
  includes spatial_rules
  shows "ts,v \<Turnstile>re(c)  \<Longrightarrow> ts,v \<Turnstile> re(c) \<^bold>\<frown> re(c)" 
proof -
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
  from 1 and 6 and 7 show "ts,v \<Turnstile>re(c) \<^bold>\<frown> re(c)"  by blast
qed

lemma res_compose: "ts,v \<Turnstile>re(c) \<^bold>\<frown> re(c)  \<Longrightarrow> ts,v \<Turnstile> re(c)"  
  by (metis (full_types) chop_add_length_ge_0 hchopE len_compose_hchop re_def restriction_stable1 satisfies_def view.hchop_def)

lemma res_dense:"(ts,v \<Turnstile>re(c)) = (ts,v \<Turnstile> re(c) \<^bold>\<frown> re(c))"
  using res_decompose res_compose unfolding valid_def satisfies_def by blast

lemma res_continuous :
includes spatial_rules
  shows "ts,v \<Turnstile>re(c) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown> ( \<^bold>\<not>re(c) \<^bold>\<and> \<^bold>\<l> > 0) \<^bold>\<frown> \<^bold>\<top>))" 
proof 
  assume 1:"ts,v \<Turnstile> re(c)" and 2:"ts,v \<Turnstile>  \<^bold>\<top> \<^bold>\<frown> ( \<^bold>\<not>re(c) \<^bold>\<and> \<^bold>\<l> > 0) \<^bold>\<frown> \<^bold>\<top>"
  then obtain v1 v2 v3 vF where "v=v1\<parallel>v2" and "v2=vF\<parallel>v3" and "ts,vF \<Turnstile>  \<^bold>\<not>re(c) \<^bold>\<and> \<^bold>\<l> > 0" by blast
  then have "\<parallel>ext vF\<parallel> \<noteq> \<parallel> len vF ts c\<parallel> " 
    by (metis "1" length_ge_def mconjunct1 mconjunct2 mnotE re_def restriction.restrict_def satisfies_def sensors.intro sensors.len_view_hchop_left sensors.len_view_hchop_right sensors_ge view.hchop_def) 
  then show "ts,v \<Turnstile>\<^bold>\<bottom>" using 1 
    by (metis \<open>v2=vF\<parallel>v3\<close> \<open>v=v1\<parallel>v2\<close> re_def satisfies_def sensors.len_view_hchop_left sensors.len_view_hchop_right sensors_axioms)
qed

lemma no_clm_before_res:"ts,v \<Turnstile>\<^bold>\<not>(cl(c) \<^bold>\<frown> re(c))"  
  by (metis cl_def hchop_def horizontal_chop_lanes_stable  inf.idem mnot_def nat_int.card_empty_zero one_neq_zero re_def restriction.restrict_def'  restriction_clm_res_disjoint  satisfies_def)

lemma no_clm_before_res2:
includes spatial_rules
  shows "ts,v \<Turnstile>\<^bold>\<not> (cl(c) \<^bold>\<frown> \<^bold>\<top> \<^bold>\<frown> re(c))" 
proof 
  assume 1:"ts,v \<Turnstile> cl(c) \<^bold>\<frown> \<^bold>\<top> \<^bold>\<frown> re(c)"
  then have "restrict v (clm ts) c = restrict v (res ts) c" 
    using cl_def hmlsl.re_def hmlsl_axioms restriction.restrict_def satisfies_def view.hchop_def by force
  then show "ts,v \<Turnstile> \<^bold>\<bottom>" 
    by (metis 1 cl_def hchopE inf.idem nat_int.card_empty_zero one_neq_zero restriction.restriction_stable1 restriction_clm_res_disjoint satisfies_def)
qed
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
lemma clm_decompose: 
includes spatial_rules
  shows "ts,v \<Turnstile>cl(c)  \<Longrightarrow> ts,v \<Turnstile> cl(c) \<^bold>\<frown> cl(c)" 
proof -
  assume assm:"ts,v \<Turnstile> cl(c)" 
  have restr:"restrict v (clm ts) c = lan v" using assm unfolding satisfies_def cl_def by simp
  have len_ge_zero:"\<parallel>len v ts c\<parallel> > 0" using assm unfolding satisfies_def cl_def by simp
  have len:"len v ts c = ext v" using assm unfolding satisfies_def cl_def by simp
  obtain v1 v2 where chop:"(v=v1\<parallel>v2) \<and> \<parallel>ext v1\<parallel> > 0 \<and> \<parallel>ext v2\<parallel> > 0 " 
    using assm view.horizontal_chop_non_empty    
    using length_split unfolding hchop_def satisfies_def cl_def by blast    
  then have 1:"ts,v1 \<Turnstile> cl(c)" 
    by (metis assm cl_def len_view_hchop_left  restriction_stable1 satisfies_def view.hchop_def)
  have 2:"ts,v2 \<Turnstile> cl(c)" using chop 
    by (metis assm cl_def  len_view_hchop_right restriction_stable2 satisfies_def view.hchop_def)
  show "ts,v \<Turnstile> cl(c) \<^bold>\<frown> cl(c) " using 1 2 chop by blast
(*  from chop and len have len_v1:"len v1 ts c = ext v1" 
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
*)
qed


lemma clm_compose: "ts,v \<Turnstile>cl(c) \<^bold>\<frown> cl(c)  \<Longrightarrow> ts,v \<Turnstile> cl(c)" 
  by (metis (full_types) chop_add_length_ge_0 cl_def hchopE len_compose_hchop restriction_stable1 satisfies_def view.hchop_def)


lemma clm_dense:"(ts,v \<Turnstile>cl(c)) = (ts,v \<Turnstile> cl(c) \<^bold>\<frown> cl(c))"
   using clm_decompose clm_compose  
   by meson

lemma clm_continuous :
includes spatial_rules
  shows "ts,v \<Turnstile> cl(c) \<Longrightarrow> ts,v \<Turnstile> (\<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( \<^bold>\<not>cl(c) \<^bold>\<and> \<^bold>\<l> > 0) \<^bold>\<frown> \<^bold>\<top>))"     
proof
  assume 1:"ts,v \<Turnstile> cl(c)" and 2:"ts,v \<Turnstile> \<^bold>\<top> \<^bold>\<frown>  ( \<^bold>\<not>cl(c) \<^bold>\<and> \<^bold>\<l> > 0) \<^bold>\<frown> \<^bold>\<top>" 
  then obtain v1 and v2 and  v3 and  vF where "v=v1\<parallel>v2" and "v2=vF\<parallel>v3" and "ts,vF \<Turnstile>  \<^bold>\<not>cl(c) \<^bold>\<and> \<^bold>\<l> > 0" by blast
  then have "\<parallel>ext vF\<parallel> \<noteq> \<parallel>len vF ts c\<parallel>" 
    by (metis "1" cl_def len_view_hchop_left len_view_hchop_right length_ge_def mconjunct1 mconjunct2 mnotE restriction.restrict_def satisfies_def view.hchop_def)
  then show "ts,v \<Turnstile> \<^bold>\<bottom>" using 1 
    by (metis \<open>v2=vF\<parallel>v3\<close> \<open>v=v1\<parallel>v2\<close> cl_def len_view_hchop_left len_view_hchop_right satisfies_def)
qed

lemma res_not_free: "ts,v \<Turnstile>\<^bold>\<exists> c. re(c) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<not>free" 
  by (metis (mono_tags, lifting) free_def card_non_empty_geq_one  hmlsl.re_def hmlsl_axioms  less_irrefl mccontr mexistsB_def mexists_def  order_refl satisfies_def) 

lemma clm_not_free: "ts,v \<Turnstile>\<^bold>\<exists> c. cl(c) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<not>free"
  by (metis (mono_tags, lifting) free_def card_non_empty_geq_one  hmlsl.cl_def hmlsl_axioms  less_irrefl mccontr mexistsB_def mexists_def  order_refl satisfies_def) 

lemma free_no_res:"ts,v \<Turnstile>free \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<not>(\<^bold>\<exists> c. re(c))" 
  by (metis (no_types, lifting) mclassical mnotE res_not_free)

lemma free_no_clm:"ts,v \<Turnstile> free \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<not>(\<^bold>\<exists> c. cl(c))" 
  by (metis (no_types, lifting) mclassical mnotE clm_not_free)

lemma free_no_clm2:"ts,v \<Turnstile>free \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<forall>c. \<^bold>\<not> cl(c)" using free_no_clm 
  by (metis mallI mclassical mexI mnotE)


lemma free_decompose:"ts,v \<Turnstile>free \<Longrightarrow> ts,v \<Turnstile> ( free \<^bold>\<frown> free)"
proof - 
  assume assm:"ts,v \<Turnstile>free"
  obtain v1 and v2 
    where non_empty_v1_v2:"(v=v1\<parallel>v2) \<and> \<parallel>ext v1\<parallel> > 0 \<and> \<parallel>ext v2\<parallel> > 0"
     using assm length_dense  
     using free_def satisfies_def view.horizontal_chop_non_empty by fastforce
  have one_lane:"|lan v1| = 1 \<and> |lan v2| = 1" 
    using assm view.hchop_def non_empty_v1_v2 
    using free_def satisfies_def by auto    
  have nothing_on_v1:
    " (\<forall>c. \<parallel>len v1 ts c\<parallel> = 0 
        \<or> (restrict v1 (clm ts) c = \<emptyset> \<and> restrict v1 (res ts) c = \<emptyset>))"  using assm 
    by (metis free_def len_empty_subview non_empty_v1_v2 restriction.restriction_stable1 satisfies_def view.horizontal_chop_leq1)
  have nothing_on_v2:
    " (\<forall>c. \<parallel>len v2 ts c\<parallel> = 0 
        \<or> (restrict v2 (clm ts) c = \<emptyset> \<and> restrict v2 (res ts) c = \<emptyset>))"   using assm 
    by (metis free_def len_empty_subview non_empty_v1_v2 restriction.restriction_stable2 satisfies_def view.horizontal_chop_leq2)
  have  
    "(v=v1\<parallel>v2) 
    \<and> 0 < \<parallel>ext v1\<parallel> \<and> |lan v1| = 1 
    \<and> (\<forall>c. \<parallel>len v1 ts c\<parallel> = 0 
        \<or>( restrict v1 (clm ts) c = \<emptyset> \<and> restrict v1 (res ts) c = \<emptyset>))
    \<and> 0 < \<parallel>ext v2\<parallel> \<and> |lan v2| = 1
    \<and> (\<forall>c. \<parallel>len v2 ts c\<parallel> = 0 
        \<or>( restrict v2 (clm ts) c = \<emptyset> \<and> restrict v2 (res ts) c = \<emptyset>))"
    using non_empty_v1_v2 nothing_on_v1 nothing_on_v2 one_lane by blast      
  then show "ts,v \<Turnstile>(free \<^bold>\<frown> free)" 
    using free_def hmlsl.hchop_def hmlsl_axioms satisfies_def by auto
qed

lemma free_compose:
includes spatial_rules
  shows "ts,v \<Turnstile>(free \<^bold>\<frown> free) \<Longrightarrow> ts,v \<Turnstile> free"
proof -
  assume assm:"ts,v \<Turnstile>free \<^bold>\<frown> free"
  have len_ge_0:"\<parallel>ext v\<parallel> > 0" 
     using assm length_meld  
     using free_def length_def rchop_def satisfies_def view.hchop_def by force
  have width_one:"|lan v| = 1" using assm 
    using free_def satisfies_def view.horizontal_chop_width_stable by force  
  obtain v1 and v2 where c:"v=v1\<parallel>v2" and f1:"ts,v1 \<Turnstile>free" and f2:"ts,v2 \<Turnstile>free" using assm by blast
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
    have 2:"\<parallel>len v1 ts c\<parallel> > 0 \<or> \<parallel>len v2 ts c\<parallel> > 0" using c 
      using "1" len_hchop_add by auto
    have "(restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)" using ex ..
    then show False
    proof
      assume a:"restrict v (clm ts) c \<noteq> \<emptyset>"
      then have a1:"restrict v1 (clm ts) c \<noteq> \<emptyset>"  
         using c restriction.restriction_stable1 by auto
      have a2: "restrict v2 (clm ts) c \<noteq> \<emptyset>" using a c restriction.restriction_stable2 by auto
      from 2 show False
      proof 
        assume b:"\<parallel>len v1 ts c\<parallel> > 0 "
        then show False using assm free_def  a1 
          by (metis f1  less_irrefl less_trans  satisfies_def)
      next
        assume b:"\<parallel>len v2 ts c\<parallel> > 0 "
        then show False using assm free_def  a2 
          by (metis f2  less_irrefl less_trans  satisfies_def)
      qed
    next
      assume a:"restrict v (res ts) c \<noteq> \<emptyset>"
      then have a1:"restrict v1 (res ts) c \<noteq> \<emptyset>"  
         using c restriction.restriction_stable1 by auto
      have a2: "restrict v2 (res ts) c \<noteq> \<emptyset>" using a c restriction.restriction_stable2 by auto
     from 2 show False
      proof 
        assume b:"\<parallel>len v1 ts c\<parallel> > 0 "
        then show False using assm free_def  a1 
          by (metis f1  less_irrefl less_trans  satisfies_def)
      next
        assume b:"\<parallel>len v2 ts c\<parallel> > 0 "
        then show False using assm free_def  a2 
          by (metis f2  less_irrefl less_trans  satisfies_def)
      qed
    qed
  qed
  show "ts,v \<Turnstile>free"
    using len_ge_0 width_one no_car  
    by (simp add: free_def satisfies_def)
qed


lemma free_dense:"(ts,v \<Turnstile>free) = (ts,v \<Turnstile> free \<^bold>\<frown> free)"
 using free_decompose free_compose unfolding valid_def satisfies_def by blast

lemma free_dense2:"ts,v \<Turnstile>free  \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<top> \<^bold>\<frown> free \<^bold>\<frown> \<^bold>\<top>"
  using hchop_weaken  by simp



text \<open>
The next lemmas show the connection between the spatial. In particular,
if the view consists of one lane and a non-zero extension, where neither
a reservation nor a car resides, the view satisfies free (and vice versa). 
\<close>


lemma no_cars_means_free:
  includes hmlsl_simps spatial_rules
  shows
  "ts,v \<Turnstile>((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))) \<Longrightarrow> ts,v \<Turnstile> free" 
proof -
  assume assm:
    "ts,v \<Turnstile> ((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))"
  have ge_0:"ts,v \<Turnstile> \<^bold>\<l> > 0" using assm  by best
  have one_lane:"ts,v \<Turnstile>\<^bold>\<omega> = 1" using assm   by auto  
  have no_car1:"ts,v \<Turnstile> \<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" using assm 
    by (meson mconjE)
  show "ts,v \<Turnstile> free"  
  proof (rule mccontr)
    have no_car: "ts,v \<Turnstile>\<^bold>\<not>( \<^bold>\<exists> c.  (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))"
      using no_car1  by (simp add: satisfies_def mnot_def mforall_def mexists_def mforallB_def mexistsB_def)     
    assume "ts,v \<Turnstile> \<^bold>\<not> free"
    hence contra:
      "\<not>(\<forall>c. \<parallel>len v ts c\<parallel> = 0 \<or> restrict v (clm ts) c = \<emptyset> \<and> restrict v (res ts) c = \<emptyset>)"
      using ge_0 one_lane unfolding satisfies_def  
      by (simp add: free_def length_ge_def mnot_def width_eq_def)
    hence ex_car:
      "\<exists>c. \<parallel>len v ts c\<parallel> > 0 \<and> (restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)" 
      using real_int.length_ge_zero dual_order.antisym not_le 
      by metis
    obtain c where c_def:
      "\<parallel>len v ts c\<parallel> > 0 \<and> (restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)"       
      using ex_car by blast
    hence "(restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq> \<emptyset>)" by best
    thus "ts,v \<Turnstile>\<^bold>\<bottom>"  
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
      have v3_one_lane:"|lan v3| = 1" using horizontal_chop_empty_left horizontal_chop_empty_right
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> hchop_def one_lane      
        by (metis hmlsl.width_eq_def hmlsl_axioms satisfies_def view.horizontal_chop_width_stable)
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
        by (simp add: len_eq cl_def satisfies_def)
      hence "ts,v \<Turnstile>  (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> by blast
      hence "ts,v \<Turnstile>\<^bold>\<exists> c. (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" 
        by (meson mexI)
      thus "ts,v \<Turnstile>\<^bold>\<bottom> " using no_car 
        by (meson mnotE)
    next
      assume "restrict v (res ts) c \<noteq> \<emptyset>"
      with one_lane have clm_one:"|restrict v (res ts) c| = 1" 
        using el_in_restriction_clm_singleton 
        by (metis card_non_empty_geq_one card_subset_le dual_order.antisym restriction.restrict_view satisfies_def width_eq_def)
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
        by (metis satisfies_def view.horizontal_chop_lanes_stable width_eq_def)
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
        by (simp add: len_eq re_def satisfies_def)
      hence "ts,v \<Turnstile>  (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" 
        using \<open>v2=v3\<parallel>v4\<close> \<open>v=v1\<parallel>v2\<close> 
        using hchopI mTrueI mor_def satisfies_def by auto
      hence "ts,v \<Turnstile>\<^bold>\<exists> c. (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" by (meson mexI) 
      thus "ts,v \<Turnstile> \<^bold>\<bottom>"  using no_car by (meson mnotE)
    qed
  qed
qed



lemma free_means_no_cars:
  includes hmlsl_simps spatial_rules
  shows "ts,v \<Turnstile>free \<Longrightarrow> ts,v \<Turnstile> ((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))" 
proof -
  assume assm:"ts,v \<Turnstile> free"
  have no_car:"ts,v \<Turnstile>(\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))"
  proof (rule mccontr)
    assume "(ts,v \<Turnstile>\<^bold>\<not>(\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))"
    then have "ts,v \<Turnstile>\<^bold>\<exists> c. \<^bold>\<not>\<^bold>\<not>(\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)" 
      by auto
    hence contra:"ts,v \<Turnstile> \<^bold>\<exists> c. \<^bold>\<top> \<^bold>\<frown> (cl(c) \<^bold>\<or> re(c)) \<^bold>\<frown> \<^bold>\<top>"  
      by (simp add: mnot_def)
    from this obtain c and v1 and v' and v2 and vc where 
      vc_def:"(v=v1\<parallel>v') \<and> (v'=vc\<parallel>v2) \<and> (ts,vc \<Turnstile> cl(c) \<^bold>\<or> re(c))" 
      by force
    hence len_ge_zero:"\<parallel>len v ts c\<parallel> > 0" 
      by (metis cl_def len_empty_subview length_ge_zero less_eq_real_def mdisjE re_def satisfies_def view.horizontal_chop_leq1 view.horizontal_chop_leq2) 
    from vc_def have vc_ex_car:
      "restrict vc (clm ts) c \<noteq> \<emptyset> \<or> restrict vc (res ts) c \<noteq>\<emptyset>" 
      using nat_int.card_empty_zero one_neq_zero 
      using cl_def re_def satisfies_def by fastforce
    have eq_lan:"lan v = lan vc" using vc_def hchop_def 
      using view.hchop_def by auto
    hence v_ex_car:"restrict v (clm ts) c \<noteq> \<emptyset> \<or> restrict v (res ts) c \<noteq>\<emptyset>" 
      using vc_ex_car by (simp add: restrict_def)
    from len_ge_zero and v_ex_car and assm show "ts,v \<Turnstile> \<^bold>\<bottom> " 
      by (metis free_def not_less order_refl satisfies_def)
  qed
  with assm show 
    "ts,v \<Turnstile>((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>)))"
    using free_ge_zero width_free 
    by blast
qed


lemma free_eq_no_cars:
  "(ts,v \<Turnstile>free) = (ts,v \<Turnstile>((\<^bold>\<l>>0) \<^bold>\<and> (\<^bold>\<omega> = 1) \<^bold>\<and> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))))" 
   using no_cars_means_free free_means_no_cars 
   by meson

lemma free_nowhere_res:
  includes hmlsl_simps
  assumes "ts,v \<Turnstile>free "
  shows " ts,v \<Turnstile> \<^bold>\<not>(\<^bold>\<top> \<^bold>\<frown> (re(c)) \<^bold>\<frown> \<^bold>\<top>)"
proof -
  from assms and free_means_no_cars have "ts,v \<Turnstile> (\<^bold>\<forall>c. \<^bold>\<not> (\<^bold>\<top> \<^bold>\<frown>  ( cl(c) \<^bold>\<or> re(c) ) \<^bold>\<frown> \<^bold>\<top>))" 
    by (meson mconjunct2)
  then have "ts,v \<Turnstile> \<^bold>\<not>(\<^bold>\<top> \<^bold>\<frown> (cl(c) \<^bold>\<or> re(c)) \<^bold>\<frown> \<^bold>\<top>)" 
    by (meson mallE)
  then show "ts,v \<Turnstile> \<^bold>\<not>(\<^bold>\<top> \<^bold>\<frown> (re(c)) \<^bold>\<frown> \<^bold>\<top>)"  
  proof -
    have "\<not> (ts , v \<Turnstile> \<^bold>\<top> \<^bold>\<frown> (cl(c) \<^bold>\<or> re(c)) \<^bold>\<frown> \<^bold>\<top>)"
      using \<open>ts , v \<Turnstile> \<^bold>\<not>\<^bold>\<top> \<^bold>\<frown> (cl(c) \<^bold>\<or> re(c)) \<^bold>\<frown> \<^bold>\<top>\<close> mnotE by blast
    then have "\<not> (ts , v \<Turnstile> \<^bold>\<top> \<^bold>\<frown> re(c) \<^bold>\<frown> \<^bold>\<top>)"
      by (meson hchopE hchopI mdisjI2)
    then show ?thesis
      by force
  qed
qed


lemma two_res_not_res: "ts,v \<Turnstile>re(c) \<^bold>\<smile> re(c) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<not>re(c)" 
  by (metis add_eq_self_zero mccontr one_add_one satisfies_def two_res_width width_eq_def width_res zero_neq_one)

lemma two_clm_width: "ts,v \<Turnstile>cl(c) \<^bold>\<smile> cl(c) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<omega> = 2" 
  using clm_sing mnotE by blast

lemma two_res_no_car: "ts,v \<Turnstile>re(c) \<^bold>\<smile> re(c) \<Longrightarrow> ts,v \<Turnstile> \<^bold>\<not>(\<^bold>\<exists> c. ( cl(c) \<^bold>\<or> re(c)) )" 
  by (metis (no_types, lifting) add_eq_self_zero cl_def mclassical mexE mor_def one_add_one one_neq_zero re_def satisfies_def two_res_width width_eq_def)

(*
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