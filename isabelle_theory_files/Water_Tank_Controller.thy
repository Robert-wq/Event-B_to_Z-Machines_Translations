section \<open> Water Tank Controller \<close>

theory Water_Tank_Controller
  imports "Z_Machines.Z_Machine"  
begin   

definition L :: nat where [z_defs]: "L = 0"
definition H :: nat where [z_defs]: "H = 10"

consts LEVELS :: "nat set"
(*Possible water levels for the tank*)
def_consts LEVELS = "{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}"
declare LEVELS_def [simp]
  
consts DELAYS :: "nat set"
def_consts DELAYS = "{0, 1, 2, 3}"
declare DELAYS_def [simp]

subsection \<open>Initial Abstraction\<close>

zstore Water_Tank_Controller =
  clk :: nat (*clock*)
  (*wl \<in> 0..clk \<rightarrow> \<nat> - Event-B implementation - however can't constrain dom(wl)
    to clk, so have to weaken. dom(wl) constrained in invariants*)
  wl :: "nat \<Zpfun> nat" (*time \<Zpfun> wl, history of the water levels*)
  n :: nat
  x :: "nat list" (*used for viewing progress of water level in animator*)
  where
  (*wl \<in> {0..clk} \<Zpfun> \<nat> - this is the event-B invariant. Below is an interpretation.
    ran(wl) is already constrained by the type system, therefore we just have to make sure
    that dom(wl) is constrained as so*)
  "\<forall>t \<in> dom(wl). t \<ge> 0 \<and> t \<le> clk"
  (*Show that there is no history where the tank has failed*)
  "\<forall>t. t\<in>dom(wl) \<longrightarrow> L \<le> wl(t)"
  "\<forall>t. t\<in>dom(wl) \<longrightarrow> wl(t) \<le> H" 


zinit Water_Tank_ControllerInit =
  over "Water_Tank_Controller"
  update 
    "[clk \<leadsto> 0, 
      wl \<leadsto> wl \<oplus> {0 \<mapsto> L}]"
                 
lemma Water_Tank_ControllerInit_correct [hoare_lemmas]: 
  "Water_Tank_ControllerInit establishes Water_Tank_Controller_inv"
  apply zpog_full
  oops

zoperation Level_Change =
  params
    l \<in> LEVELS
  pre
    "l \<ge> L \<and> l \<le> H"
  update
  "[wl \<leadsto> wl \<oplus> {(clk + 1) \<mapsto> l},
    clk \<leadsto> clk + 1]"

lemma Level_Change_correct [hoare_lemmas]: 
  "Level_Change p preserves Water_Tank_Controller_inv"
  apply zpog_full
   apply fastforce
  by fastforce
  
text \<open>The following two operations are a hack way of showing the history of the water
      tank levels. Essentially x is a list that is updated by CreateDataList to contain
      the value of wl(n) for all 0 < n < length(dom(wl)). x could have been updated in 
      the level change operation but i didn't want to change this operation.

      I am almost positive there is a better way of doing this, however this helped
      me translate the spec, so i have left it here. \<close> 
zoperation ShowLevel =
  emit x

zoperation CreateDataList =
  pre
    "wl \<noteq> {\<mapsto>}"
    "n < length(sorted_list_of_set(dom(wl)))"
  update
    "[x \<leadsto> x @ [wl(n)],
      n \<leadsto> n + 1]"
 

zmachine WTC0 =
  init Water_Tank_ControllerInit
  operations Level_Change ShowLevel CreateDataList

animate WTC0

subsection \<open>Refinement 1\<close>

consts
  LT :: nat (*Low threshold*)
  HT :: nat (*High threshold*)
  DU :: nat (*Increase in water level in one time unit*)
  DD :: nat (*Decrease in water level in one time unit*)
  C  :: nat (*Maximum time between successive control events*)
  A  :: nat (*Maximum time between sample time and control time*)

(*TODO - look at axioms for consts
         do these all need to be constants
*)

zstore Water_Tank_Controller1 = Water_Tank_Controller +
  ct :: nat (*timestamp of most recent control event*)
  wl1 :: nat
  wl2 :: nat
  where
  "wl1 \<ge> L"
  "wl2 \<le> H"
  "ct \<le> clk"
  "clk \<le> ct + C"

zinit Water_Tank_Controller1Init =
  over 
    "Water_Tank_Controller1"
  update
    "[clk \<leadsto> 0, 
      wl \<leadsto> wl \<oplus> {0 \<mapsto> L},
      ct \<leadsto> 0,
      wl1 \<leadsto> L,
      wl2 \<leadsto> H]"

zoperation Level_Change1 =
  params
    l \<in> LEVELS
  pre
    (*current clk value should be less than last 
      control time + maximum delay between control events*)
    "clk < ct + C"
    "wl1 \<le> l \<and> l \<le> wl2" 
  update
  "[wl \<leadsto> wl \<oplus> {(clk + 1) \<mapsto> l},
    clk \<leadsto> clk + 1]"

lemma Level_Change1_correct [hoare_lemmas]: 
  "Level_Change1 p preserves Water_Tank_Controller1_inv"
  apply zpog_full
   apply fastforce
  by fastforce

zoperation Control =
  params
    l1 \<in> LEVELS
    l2 \<in> LEVELS
    a \<in> DELAYS
  pre
    "clk \<ge> A"
    "0 \<le> a \<and> a \<le> A"
    "L \<le> l1 \<and> l1 \<le> wl(clk - a)"
    "wl(clk - a) \<le> l2 \<and> l2 \<le> H"
  update 
    "[ct \<leadsto> clk,
      wl1 \<leadsto> l1,
      wl2 \<leadsto> l2]"

lemma Control_correct [hoare_lemmas]: 
  "Control p preserves Water_Tank_Controller1_inv"
  by zpog_full

zoperation Show_A =
  emit A

zoperation Show_C =
  emit C

zmachine WTC1 =
  init Water_Tank_Controller1Init
  operations Level_Change1 Control Show_C Show_A ShowLevel CreateDataList

animate WTC1
  defines A = 2 C = 2

(*
check_deadlock WTC1
  defines A = 2 C = 2
*)

subsection \<open>Refinement 2 - Refines the inital abstraction not refinement 1\<close>

zstore Water_Tank_Controller2 = Water_Tank_Controller +
  ct :: nat (*timestamp of most recent control event*)
  pump :: bool (*controls whether or not the pump is on(True) or off(False)*)
  where
  "ct \<le> clk"
  "clk \<le> ct + C"
  "pump = False \<longrightarrow> (\<forall>i j . ct \<le> i \<and> i \<le> j \<and> j \<le> clk \<longrightarrow> wl(j) \<ge> wl(i) - (DD*(j - i)))"
  "pump = True \<longrightarrow> (\<forall>i j . ct \<le> i \<and> i \<le> j \<and> j \<le> clk \<longrightarrow> wl(j) \<ge> wl(i))"
  "pump = True \<longrightarrow> (\<forall>i j . ct \<le> i \<and> i \<le> j \<and> j \<le> clk \<longrightarrow> wl(j) \<le>  wl(i) + (DU*(j - i)))"
  "pump = False \<longrightarrow> (\<forall>i j . ct \<le> i \<and> i \<le> j \<and> j \<le> clk \<longrightarrow>  wl(j) \<le> wl(i))"
  "pump = True  \<longrightarrow>  wl(ct) \<le> (H - (DU*C) - DU)"

zinit Water_Tank_Controller2Init =
  over 
    "Water_Tank_Controller2"
  update
    "[clk \<leadsto> 0, 
      wl \<leadsto> wl \<oplus> {0 \<mapsto> L},
      ct \<leadsto> 0,
      pump \<leadsto> True]"

lemma Water_Tank_ControllerInit_correct [hoare_lemmas]: 
  "Water_Tank_Controller2Init establishes Water_Tank_Controller2_inv"
  apply zpog_full
  oops

zoperation Level_Decrease =
  params
    l \<in> LEVELS
  pre
    "clk < ct + C"
    "pump = False"
    "wl(clk)-DD \<le> l"
    "l \<le> wl(clk)"
  extends
    "Level_Change(l)"
  update
    "[wl \<leadsto> wl \<oplus> {(clk + 1) \<mapsto> l},
      clk \<leadsto> clk + 1]"

lemma Level_Decrease_correct [hoare_lemmas]: 
  "Level_Decrease p preserves Water_Tank_Controller2_inv"
  apply zpog_full
    apply fastforce
   apply (metis le_SucI)
  oops

zoperation Level_Increase =
  params
    l \<in> LEVELS
  pre
    "clk < ct + C"
    "pump = True"
    "wl(clk) \<le> l"
    "l \<le> wl(clk) + DU"
  extends
    "Level_Change(l)"
  update
    "[wl \<leadsto> wl \<oplus> {(clk + 1) \<mapsto> l},
      clk \<leadsto> clk + 1]"

lemma Level_Increase_correct [hoare_lemmas]: 
  "Level_Increase p preserves Water_Tank_Controller2_inv"
  apply zpog_full
    apply fastforce
   apply (metis le_SucI)
  oops

zoperation Control_Low =
  params
    a \<in> DELAYS
  pre
    "0 \<le> a \<and> a \<le> A"
    "a \<le> clk"
    "ct \<le> clk - a"
    "wl(clk - a) \<le> LT"
  update
    "[ct \<leadsto> clk,
      pump \<leadsto> True]"

lemma Control_Low_correct [hoare_lemmas]: 
  "Control_Low p preserves Water_Tank_Controller2_inv"
  apply zpog_full
    apply fastforce
   apply (metis le_trans)
  oops

zoperation Control_Med =
  params
    a \<in> DELAYS
  pre
    "0 \<le> a \<and> a \<le> A"
    "a \<le> clk"
    "ct \<le> clk - a"
    "pump = False \<longrightarrow> wl(clk - a) > LT"
    "pump = True \<longrightarrow> wl(clk - a) < HT"
  update
    "[ct \<leadsto> clk]"

lemma Control_Med_correct [hoare_lemmas]: 
  "Control_Med p preserves Water_Tank_Controller2_inv"
  apply zpog_full
  oops

zoperation Control_High =
  params
    a \<in> DELAYS
  pre
    "0 \<le> a \<and> a \<le> A"
    "a \<le> clk"
    "ct \<le> clk - a"
    "wl(clk - a) \<ge> HT"
  update
    "[ct \<leadsto> clk,
      pump \<leadsto> False]"

(*Interesting that sledgehammer can provide a proof for this but not the 
Low or Med operations*)
lemma Control_High_correct [hoare_lemmas]: 
  "Control_High p preserves Water_Tank_Controller2_inv"
  apply zpog_full
    apply fastforce
   apply (metis le_trans)
  by (metis le_trans)
  
zmachine WTC2 =
  init Water_Tank_Controller2Init
  operations Level_Decrease Level_Increase Control_Low Control_Med Control_High 
             ShowLevel CreateDataList

(*Interestingly it looks like there is a double update due to extension of event*)
animate WTC2
  defines A = 2 C = 2 LT = 2 HT = 8 DU = 3 DD = 3

subsection \<open>Refinement 3 - refines refinement 2\<close>

zstore Water_Tank_Controller3 = Water_Tank_Controller2 +
  wl_mch :: nat
  st :: nat
  sense_ev :: bool
  where
  "st \<in> {0..clk}"
  "sense_ev = True \<longrightarrow> wl_mch = wl(st)"
  "sense_ev = True \<longrightarrow> clk - st \<le> A"
  "sense_ev = True \<longrightarrow> ct \<le> st"
  "sense_ev = True \<longrightarrow> st - ct \<le> C - A"
  "sense_ev = False \<longrightarrow> clk-ct \<le> C - A"

zinit Water_Tank_Controller3Init =
  over Water_Tank_Controller3
  update
    "[wl_mch \<leadsto> 0,
      st \<leadsto> 0,
      sense_ev \<leadsto> False]"

zoperation Level_Decrease3 =
  params
    l \<in> LEVELS
  pre
    "pump = False"
    "wl(clk)-DD \<le> l"
    "l \<le> wl(clk)"
    "sense_ev = True \<longrightarrow> (clk + 1) - st \<le> A"
    "sense_ev = False \<longrightarrow> (clk + 1) - ct \<le> C - A"
  extends
    "Level_Decrease(l)"
  update
    "[wl \<leadsto> wl \<oplus> {(clk + 1) \<mapsto> l},
      clk \<leadsto> clk + 1]"

lemma Level_Decrease3_correct [hoare_lemmas]: 
  "Level_Decrease3 p preserves Water_Tank_Controller3_inv"
  apply zpog_full
    apply (metis le_SucI)
   apply (metis le_SucI)
  oops
  
zoperation Level_Increase3 =
  params
    l \<in> LEVELS
  pre
    "pump = True"
    "wl(clk) \<le> l"
    "l \<le> wl(clk) + DU"
    "sense_ev = True \<longrightarrow> (clk + 1) - st \<le> A"
    "sense_ev = False \<longrightarrow> (clk + 1) - ct \<le> C - A"
  extends
    "Level_Increase(l)"
  update
    "[wl \<leadsto> wl \<oplus> {(clk + 1) \<mapsto> l},
      clk \<leadsto> clk + 1]"

(*zpog_full causes big slowdown on this proof*)
lemma Level_Increase3_correct [hoare_lemmas]: 
  "Level_Increase3 p preserves Water_Tank_Controller3_inv"
  apply zpog_full
  apply (metis le_SucI)
   apply (metis le_SucI)
  oops

zoperation Sense =
  pre
    "sense_ev = False"
  update
    "[wl_mch \<leadsto> wl(clk),
      sense_ev \<leadsto> True,
      st \<leadsto> clk]"

lemma Sense_correct [hoare_lemmas]: 
  "Sense p preserves Water_Tank_Controller3_inv"
  by zpog_full

(*Unfortunately could not get the following operations to work *)

(*
zoperation Control_Low3 =
  pre
    "sense_ev = True"
    "wl_mech \<le> LT"
  update
    "[ct \<leadsto> clk,
      pump \<leadsto> True]"

lemma Control_Low_correct [hoare_lemmas]: 
  "Control_Low p preserves Water_Tank_Controller2_inv"
  apply zpog_full
    apply fastforce
   apply (metis le_trans)
  oops

zoperation Control_Med =
  params
    a \<in> DELAYS
  pre
    "0 \<le> a \<and> a \<le> A"
    "a \<le> clk"
    "ct \<le> clk - a"
    "pump = False \<longrightarrow> wl(clk - a) > LT"
    "pump = True \<longrightarrow> wl(clk - a) < HT"
  update
    "[ct \<leadsto> clk]"

zoperation Control_High =
  params
    a \<in> DELAYS
  pre
    "0 \<le> a \<and> a \<le> A"
    "a \<le> clk"
    "ct \<le> clk - a"
    "wl(clk - a) \<ge> HT"
  update
    "[ct \<leadsto> clk,
      pump \<leadsto> False]"
 *) 