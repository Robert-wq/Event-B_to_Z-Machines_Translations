section \<open> Bridge Controller \<close>

theory Bridge_Controller_Refine
  imports "Z_Machines.Z_Machine"
begin            

text \<open> This model shows an implementation of a Bridge Controller, it is an attempt at a 
direct translation of Abrial's Event-B example from the book "Modelling in Event-B" \<close>

subsection \<open>Constants\<close>

(*Constant that is equivalent to n in the Event-B spec*)
consts MAX_CARS :: "nat" 

(*MAX _CARS declared and set here in order to support deadlock freedom checks*)
def_consts MAX_CARS = 10

declare MAX_CARS_def [simp]

subsection \<open>Abstract model\<close>

zstore BridgeController =
  n :: nat \<comment> \<open> number of cars \<close>
  where 
  "n \<le> MAX_CARS"

zinit BridgeControllerInit =
  over BridgeController
  update 
    "[n \<leadsto> 0]"

lemma BridgeControllerInit_correct [hoare_lemmas]: 
  "BridgeControllerInit establishes BridgeController_inv"
  by zpog_full

zoperation ML_in =
  pre 
    "n > 0"
  update 
    "[n \<leadsto> n - 1]"

lemma ML_in_correct [hoare_lemmas]: "ML_in p preserves BridgeController_inv"
  apply zpog_full
  by linarith

zoperation ML_out = 
  pre 
    "n < MAX_CARS"
  update 
    "[n \<leadsto> n + 1]"

lemma ML_out_correct [hoare_lemmas]: "ML_out p preserves BridgeController_inv"
  apply zpog_full
  done

(*Note - adding the Show_cars operation to the machine, will mean that it will
never deadlock. This means that deadlock_freedom proofs will become trivial*)
zoperation Show_cars =
  emit n

zmachine BC0 = 
  init BridgeControllerInit
  invariant BridgeController_inv
  operations ML_in ML_out

animate BC0

check_deadlock BC0

lemma dlf_BC0: "deadlock_free BC0"
  apply deadlock_free
  by linarith

subsection \<open> First Refinement \<close>

zstore BridgeController1 = BridgeController +
  a :: nat
  b :: nat
  c :: nat
  where
  "a + b + c = n"
  "a = 0 \<or> c = 0"

zinit BridgeController1Init =
  over BridgeController1
  update 
    "[n \<leadsto> 0, 
      a \<leadsto> 0, 
      b \<leadsto> 0, 
      c \<leadsto> 0]"

lemma BridgeController1Init_correct [hoare_lemmas]: 
  "BridgeController1Init establishes BridgeController1_inv"
  by zpog_full

zoperation ML_in1 =
  pre 
    "c > 0  "
  extends 
    "ML_in()"
  update 
    "[c \<leadsto> c - 1]"

lemma ML_in1_correct [hoare_lemmas]: "ML_in1 p preserves BridgeController_inv"
  apply zpog_full
  by linarith

zoperation ML_out1 =
  pre 
    "a + b < MAX_CARS" 
    "c = 0"
  extends 
    "ML_out()"
  update 
    "[a \<leadsto> a + 1]"

lemma ML_out1_correct [hoare_lemmas]: "ML_out1 p preserves BridgeController_inv"
  apply zpog_full
  done

zoperation IL_in =
  pre 
    "0 < a"
  update 
    "[b \<leadsto> b + 1, 
      a \<leadsto> a - 1]"

lemma IL_in_correct [hoare_lemmas]: "IL_in p preserves BridgeController_inv"
  apply zpog_full
  done
  
zoperation IL_out =
  pre 
    "0 < b" 
    "a = 0"
  update 
    "[b \<leadsto> b - 1, 
      c \<leadsto> c + 1]"

lemma IL_out_correct [hoare_lemmas]: "IL_out p preserves BridgeController_inv"
  apply zpog_full
  done

zmachine BC1 =
  init BridgeController1Init
  invariant BridgeController_inv
  operations ML_out1 ML_in1 IL_in IL_out

animate BC1

check_deadlock BC1

lemma dlf_BC1: "deadlock_free BC1"
  apply deadlock_free
  by force
  
subsection \<open> Second Refinement \<close>

enumtype tl_color = green | red

zstore BridgeController2 = BridgeController1 +
  ml_tl :: tl_color
  il_tl :: tl_color
  ml_pass :: bool
  il_pass :: bool
  where
  "ml_tl = green \<longrightarrow> c = 0"
  "ml_tl = green \<longrightarrow> a + b < d"
  "il_tl = green \<longrightarrow> 0 < b"
  "il_tl = green \<longrightarrow> a = 0"
  "ml_tl = red \<or> il_tl = red"
  "ml_tl = red \<longrightarrow> ml_pass = True"
  "il_tl = red \<longrightarrow> il_pass = True"

zinit BridgeController2Init =
  over BridgeController2
  update "[n \<leadsto> 0, 
           a \<leadsto> 0, 
           b \<leadsto> 0, 
           c \<leadsto> 0, 
           ml_tl \<leadsto> red, 
           il_tl \<leadsto> red, 
           ml_pass \<leadsto> True, 
           il_pass \<leadsto> True]"

lemma BridgeController2Init_correct [hoare_lemmas]: 
  "BridgeController2Init establishes BridgeController2_inv"
  by zpog_full


zoperation ML_out2a =
  pre 
    "ml_tl = green" 
    "a + b + 1 < MAX_CARS"
  extends 
    "ML_out1()"
  update 
    "[a \<leadsto> a + 1,
      ml_pass \<leadsto> True]"

lemma ML_out2a_correct [hoare_lemmas]: "ML_out2a p preserves BridgeController2_inv"
  apply zpog_full
  by blast

(*
proof zpog_full
  fix a :: "\<nat>" and b :: "\<nat>" and il_pass :: "\<bool>" and x :: "\<nat>"
  assume 
    "green \<in> tl_color" and
    "red \<in> tl_color" and
    "All ((<) (a + b))" and
    il_pass and
    "a + b \<noteq> 9"
  show "Suc (a + b) < x"
    using \<open>All ((<) (a + b))\<close> by blast 
qed
*)

(*When number of cars equal to max cars, light changed to red so no more cars can get on bridge*)
zoperation ML_out2b =
  pre 
    "ml_tl = green" 
    "a + b + 1 = MAX_CARS"
  extends 
    "ML_out1()"
  update 
    "[a \<leadsto> a + 1,
      ml_pass \<leadsto> True, 
      ml_tl \<leadsto> red]"

lemma ML_out2b_correct [hoare_lemmas]: "ML_out2b p preserves BridgeController2_inv"
  by zpog_full

zoperation IL_out2a =
  pre 
    "il_tl = green" 
    "b > 1"
  extends 
    "IL_out()"
  update 
    "[b \<leadsto> b - 1,
      c \<leadsto> c + 1,
      il_pass \<leadsto> True]"

lemma IL_out2a_correct [hoare_lemmas]: "IL_out2a p preserves BridgeController2_inv"
  apply zpog_full
  oops

zoperation IL_out2b =
  pre 
    "il_tl = green" 
    "b = 1"
  extends 
    "IL_out()"
  update 
    "[b \<leadsto> b - 1,
      c \<leadsto> c + 1,
      il_tl \<leadsto> red, 
      il_pass \<leadsto> True]"

lemma IL_out2b_correct [hoare_lemmas]: "IL_out2b p preserves BridgeController2_inv"
  by zpog_full

zoperation ML_tl_green =
  pre 
    "ml_tl = red" 
    "a + b < MAX_CARS" 
    "c = 0" 
    "il_pass = True"
  update 
    "[ml_tl \<leadsto> green, 
      il_tl \<leadsto> red, 
      ml_pass \<leadsto> False]"

lemma ML_tl_green_correct [hoare_lemmas]: "ML_tl_green p preserves BridgeController2_inv"
  apply zpog_full
  oops
  
zoperation IL_tl_green =
  pre 
    "il_tl = red" 
    "0 < b" 
    "a = 0" 
    "ml_pass = True"
  update 
    "[il_tl \<leadsto> green, 
      ml_tl \<leadsto> red, 
      il_pass \<leadsto> False]"

lemma IL_tl_green_correct [hoare_lemmas]: "IL_tl_green p preserves BridgeController2_inv"
  by zpog_full


zmachine BC2 =
  init BridgeController2Init
  operations ML_out2a ML_out2b IL_out2a IL_out2b IL_in ML_in1 ML_tl_green IL_tl_green Show_cars

animate BC2

(*check_deadlock BC2*)

lemma dlf_BC2: "deadlock_free BC2"
  apply deadlock_free
  oops

subsection \<open> Third Refinement \<close>

enumtype sensor_state = working | off (*working equates to on, but the word on seems to break the enumtype*)

zstore BridgeController3 = BridgeController2 +
  ml_out_10 :: bool
  ml_in_10 :: bool
  il_in_10 :: bool
  il_out_10 :: bool
  A :: nat
  B :: nat
  C :: nat
  ML_OUT_SR :: sensor_state
  ML_IN_SR :: sensor_state
  IL_OUT_SR :: sensor_state
  IL_IN_SR :: sensor_state
  where
  "IL_IN_SR = working \<longrightarrow> A > 0"
  "IL_OUT_SR = working \<longrightarrow> B > 0"
  "ML_IN_SR = working \<longrightarrow> C > 0"
  "ml_out_10 = True \<longrightarrow> ml_tl = green"
  "il_out_10 = True \<longrightarrow> il_tl = green"
  "IL_IN_SR = working \<longrightarrow> il_in_10 = False"
  "IL_OUT_SR = working \<longrightarrow> il_out_10 = False"
  "ML_IN_SR = working \<longrightarrow> ml_in_10 = False"
  "ML_OUT_SR = working \<longrightarrow> ml_out_10 = False"
  "il_in_10 = True \<and> ml_out_10 = True \<longrightarrow> A = a"
  "il_in_10 = False \<and> ml_out_10 = True \<longrightarrow> A = a + 1"
  "il_in_10 = True \<and> ml_out_10 = False \<longrightarrow> A = a - 1"
  "il_in_10 = False \<and> ml_out_10 = False \<longrightarrow> A = a"
  "il_in_10 = True \<and> il_out_10 = True \<longrightarrow> B = b"
  "il_in_10 = True \<and> il_out_10 = False \<longrightarrow> B = b + 1"
  "il_in_10 = False \<and> il_out_10 = True \<longrightarrow> B = b - 1"
  "il_in_10 = False \<and> il_out_10 = False \<longrightarrow> B = b"
  "il_out_10 = True \<and> ml_in_10 = True \<longrightarrow> C = c"
  "il_out_10 = True \<and> ml_in_10 = False \<longrightarrow> C = c + 1"
  "il_out_10 = False \<and> ml_in_10 = True \<longrightarrow> C = c - 1"
  "il_out_10 = False \<and> ml_in_10 = False \<longrightarrow> C = c"
  "A = 0 \<or> C = 0"
  "A + B + C \<le> MAX_CARS"

zinit BridgeController3Init =
  over BridgeController3
  update "[n \<leadsto> 0, a \<leadsto> 0, b \<leadsto> 0, c \<leadsto> 0,
          ml_tl \<leadsto> red, il_tl \<leadsto> red, ml_pass \<leadsto> True, 
          il_pass \<leadsto> True, ml_out_10 \<leadsto> False, ml_in_10 \<leadsto> False, 
          il_out_10 \<leadsto> False, il_in_10 \<leadsto> False, A \<leadsto> 0, B \<leadsto> 0, 
          C \<leadsto> 0, ML_OUT_SR \<leadsto> off, ML_IN_SR \<leadsto> off, IL_OUT_SR \<leadsto> off, IL_IN_SR \<leadsto> off]"

lemma "BridgeController3Init establishes BridgeController3_inv"
  apply zpog_full
  done

zoperation ML_out3a =
  pre 
    "ml_out_10 = True"
    "a + b + 1 \<noteq> MAX_CARS"
  extends 
    "ML_out2a()"
  update 
    "[a \<leadsto> a + 1,
      ml_pass \<leadsto> True,
      ml_out_10 \<leadsto> False]"

lemma ML_out3a_correct [hoare_lemmas]: "ML_out3a p preserves BridgeController3_inv"
  apply zpog_full
   apply blast
  by blast

zoperation ML_out3b =
  pre 
    "ml_out_10 = True"
    "a + b + 1 = MAX_CARS"
  extends 
    "ML_out2b()"
  update
    "[a \<leadsto> a + 1, 
      ml_tl \<leadsto> red,
      ml_pass \<leadsto> True,
      ml_out_10 \<leadsto> False]"

lemma ML_out3b_correct [hoare_lemmas]: "ML_out3b p preserves BridgeController3_inv"
  by zpog_full
  
zoperation IL_out3a =
  pre 
    "il_out_10 = True"
    "b > 1"
  extends 
    "IL_out2a()"
  update 
    "[b \<leadsto> b - 1,
      c \<leadsto> c + 1,
      il_pass \<leadsto> True,
      il_out_10 \<leadsto> False]"

lemma IL_out3a_correct [hoare_lemmas]: "IL_out3a p preserves BridgeController3_inv"
  apply zpog_full
  oops
  
zoperation IL_out3b =
  pre 
    "il_out_10 = True"
    "b = 1"
  extends 
    "IL_out2b()"
  update 
     "[b \<leadsto> b - 1,
      il_tl \<leadsto> red,
      c \<leadsto> c + 1,
      il_pass \<leadsto> True,
      il_out_10 \<leadsto> False]"

lemma IL_out3b_correct [hoare_lemmas]: "IL_out3b p preserves BridgeController3_inv"
  by zpog_full

zoperation ML_in3 =
  pre 
    "ml_in_10 = True"
    "c > 0"
  extends 
    "ML_in1()"
  update 
    "[c \<leadsto> c - 1,
      ml_in_10 \<leadsto> False]"

lemma "ML_in3() preserves BridgeController3_inv"
  apply zpog_full
  apply linarith
    apply linarith
  by linarith
  
zoperation IL_in3 =
  pre 
    "il_in_10 = True"
    "a > 0"
  extends 
    "IL_in()"
  update 
    "[a \<leadsto> a - 1,
      b \<leadsto> b + 1,
      il_in_10 \<leadsto> False]"

lemma "IL_in3() preserves BridgeController3_inv"
  apply zpog_full
  oops
  
zoperation ML_tl_green3 =
  pre 
    "ml_tl = red" 
    "a + b < MAX_CARS" 
    "c = 0" 
    "il_pass = True"
    "il_out_10 = False" 
  extends "ML_tl_green()"
  

lemma "ML_tl_green3() preserves BridgeController3_inv"
  apply zpog_full
  apply (metis UNIV_I tl_color_def)
   apply (metis UNIV_I tl_color_def)
  oops
  
zoperation IL_tl_green3 =
  pre "il_tl = red" 
      "0 < b" "a = 0" 
      "ml_pass = True"
      "ml_out_10 = False"
  extends
      "IL_tl_green()"
(*  update "[il_tl \<leadsto> green, 
          ml_tl \<leadsto> red, 
          il_pass \<leadsto> False]" *)

lemma "IL_tl_green3() preserves BridgeController3_inv"
  apply zpog_full
   apply (simp add: tl_color_def)
  apply (simp add: tl_color_def)
  done

zoperation ML_out_arr3 =
  pre "ML_OUT_SR = off"
      "ml_out_10 = False"
  update "[ML_OUT_SR \<leadsto> working]"

lemma "ML_out_arr3() preserves BridgeController3_inv"
  by zpog_full
  
zoperation ML_in_arr3 =
  pre "ML_IN_SR = off"
      "ml_in_10 = False"
      "C > 0"
  update "[ML_IN_SR \<leadsto> working]"

lemma "ML_in_arr3() preserves BridgeController3_inv"
  by zpog_full

zoperation IL_out_arr3 =
  pre "IL_OUT_SR = off"
      "il_out_10 = False"
      "B > 0"
  update "[IL_OUT_SR \<leadsto> working]"

lemma "IL_out_arr3() preserves BridgeController3_inv"
  by zpog_full

zoperation IL_in_arr3 =
  pre "IL_IN_SR = off"
      "il_in_10 = False"
      "A > 0"
  update "[IL_IN_SR \<leadsto> working]"

lemma "IL_in_arr3() preserves BridgeController3_inv"
  by zpog_full

zoperation ML_out_dep3 =
  pre "ML_OUT_SR = working"
      "ml_tl = green"
  update "[ML_OUT_SR \<leadsto> off,
          ml_out_10 \<leadsto> True,
          A \<leadsto> A + 1]"

lemma "ML_out_dep3() preserves BridgeController3_inv"
  apply zpog_full
  apply blast
  apply blast
  by (metis not_add_less1)

zoperation ML_in_dep3 =
  pre "ML_IN_SR = working"
  update "[ML_IN_SR \<leadsto> off,
          ml_in_10 \<leadsto> True,
          C \<leadsto> C - 1]"

lemma "ML_in_dep3() preserves BridgeController3_inv"
  apply zpog_full
  apply linarith
  by linarith

zoperation IL_in_dep3 =
  pre "IL_IN_SR = working"
  update "[IL_IN_SR \<leadsto> off,
          il_in_10 \<leadsto> True,
          A \<leadsto> A - 1,
          B \<leadsto> B + 1]"

lemma "IL_in_dep3() preserves BridgeController3_inv"
  apply zpog_full
  oops
  

zoperation IL_out_dep3 =
  pre "IL_OUT_SR = working"
      "il_tl = green"
  update "[IL_OUT_SR \<leadsto> off,
          il_out_10 \<leadsto> True,
          B \<leadsto> B - 1,
          C \<leadsto> C + 1]"

lemma "ML_out_dep3() preserves BridgeController3_inv"
  apply zpog_full
  apply blast
  apply blast
  by (metis not_add_less1)


zmachine BC3 =
  init BridgeController3Init
  operations ML_out3a ML_out3b IL_out3a IL_out3b 
             ML_in3 IL_in3 ML_tl_green3 IL_tl_green3 
             ML_out_arr3 ML_in_arr3 IL_out_arr3 IL_in_arr3
             ML_out_dep3 ML_in_dep3 IL_out_dep3 IL_in_dep3 Show_cars

animate BC3

check_deadlock BC3

lemma dlf_BC3: "deadlock_free BC3"
  apply deadlock_free
  oops
  
  