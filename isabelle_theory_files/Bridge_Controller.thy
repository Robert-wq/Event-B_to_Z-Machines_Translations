section \<open> Bridge Controller \<close>

theory Bridge_Controller
  imports "Z_Machines.Z_Machine"
begin           

text \<open> This model shows an implementation of a Bridge Controller, it is an attempt at a 
direct translation of Abrial's Event-B example from the book "Modelling in Event-B" \<close>

text \<open>Abstract model\<close>

consts MAX_CARS :: "nat" 
def_consts MAX_CARS = 10
declare MAX_CARS_def [simp]

zstore BridgeController =
  n :: nat \<comment> \<open> number of cars \<close>
  where 
  "n \<le> MAX_CARS"

zinit BridgeControllerInit =
  over BridgeController
  update "[n \<leadsto> 3]"

lemma BridgeControllerInit_correct [hoare_lemmas]: 
  "BridgeControllerInit establishes BridgeController_inv"
  by zpog_full

zoperation ML_out = 
  pre 
    "n < MAX_CARS"
  update 
    "[n \<leadsto> n + 1]"

lemma ML_out_correct [hoare_lemmas]: "ML_out p preserves BridgeController_inv"
  apply zpog_full
  done

zoperation ML_in =
  pre 
    "n > 0"
  update 
    "[n \<leadsto> n - 1]"

lemma ML_in_correct [hoare_lemmas]: "ML_in p preserves BridgeController_inv"
  apply zpog_full
  by linarith

zoperation Show_cars =
  over 
    BridgeController
  emit 
    n

zmachine BC0 = 
  init BridgeControllerInit
  invariant BridgeController_inv
  operations ML_in ML_out

animate BC0

check_deadlock BC0

lemma dlf_BC0: "deadlock_free BC0"
  apply deadlock_free
  by linarith

text \<open> First Refinement \<close>

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

lemma "BridgeController1Init establishes BridgeController1_inv"
  by zpog_full

zoperation ML_in1 =
  pre 
    "n > 0" 
    "0 < c"
  update 
    "[n \<leadsto> n - 1, 
      c \<leadsto> c - 1]"

lemma "ML_in1() preserves BridgeController1_inv"
  apply zpog_full
  by simp

zoperation ML_out1 =
  pre 
    "n < MAX_CARS" 
    "a + b < MAX_CARS" 
    "c = 0"
  update 
    "[n \<leadsto> n + 1, 
      a \<leadsto> a + 1]"

lemma "ML_out1() preserves BridgeController1_inv"
  apply zpog_full
  done

zoperation IL_in =
  pre 
    "0 < a"
  update 
    "[b \<leadsto> b + 1, 
      a \<leadsto> a - 1]"

lemma "IL_in() preserves BridgeController1_inv"
  apply zpog_full
  done

zoperation IL_out =
  pre 
    "0 < b" 
    "a = 0"
  update 
    "[b \<leadsto> b - 1, 
      c \<leadsto> c + 1]"

lemma "IL_out() preserves BridgeController1_inv"
  by zpog_full

zoperation Show_cars1 =
  over BridgeController1
  emit n

zmachine BC1 =
  init BridgeController1Init
  operations ML_out1 ML_in1 IL_in IL_out Show_cars1

animate BC1
(*  defines MAX_CARS = 10 *)

check_deadlock BC1
(*  defines MAX_CARS = 10 *)

lemma dlf_BC1: "deadlock_free BC1"
  by deadlock_free

text \<open> Second Refinement \<close>

enumtype tl_color = green | red

zstore BridgeController2 = BridgeController1 +
  ml_tl :: tl_color
  il_tl :: tl_color
  ml_pass :: bool
  il_pass :: bool
  where
  "ml_tl \<in> tl_color"
  "il_tl \<in> tl_color"
  "ml_tl = green \<longrightarrow> a + b < d \<and> c = 0"
  "il_tl = green \<longrightarrow> 0 < b \<and> a = 0"
  "ml_tl = red \<or> il_tl = red"
  (*"ml_pass \<in> bool"*)
  (*"il_pass \<in> bool"*)
  "ml_tl = red \<longrightarrow> ml_pass = True"
  "il_tl = red \<longrightarrow> il_pass = True"

zinit BridgeController2Init =
  over BridgeController2
  update "[n\<Zprime> = 0, a\<Zprime> = 0, b\<Zprime> = 0, c\<Zprime> = 0, 
          ml_tl\<Zprime> = red, il_tl\<Zprime> = red, ml_pass\<Zprime> = True, il_pass\<Zprime> = True]"

lemma "BridgeController2Init establishes BridgeController2_inv"
  apply zpog_full
  by (simp add: tl_color_def)

zoperation ML_out2a =
  over BridgeController2
  pre "n < MAX_CARS" "a + b < MAX_CARS" "c = 0" "ml_tl = green" "a + b + 1 \<noteq> MAX_CARS" (*redundant guards*)
  update "[n \<leadsto> n + 1, a \<leadsto> a + 1, ml_pass \<leadsto> True]"

lemma "ML_out2a() preserves BridgeController2_inv"
  apply zpog_full
  by blast

zoperation ML_out2b =
  over BridgeController2
  pre "n < MAX_CARS" "a + b < MAX_CARS" "c = 0" "ml_tl = green" "a + b + 1 = MAX_CARS"  (*redundant guards*)
  update "[n\<leadsto> n + 1, a \<leadsto> a + 1, ml_pass \<leadsto> True, ml_tl \<leadsto> red]"

lemma "ML_out2b() preserves BridgeController2_inv"
  by zpog_full
  

zoperation IL_out2a =
  over BridgeController2
  pre "0 < b" "a = 0" "il_tl = green" "b \<noteq> 1"
  update "[b \<leadsto> b - 1, c \<leadsto> c + 1, il_pass \<leadsto> True]"

lemma "IL_out2a() preserves BridgeController2_inv"
  by zpog_full

zoperation IL_out2b =
  over BridgeController2
  pre "0 < b" "a = 0" "il_tl = green" "b = 1"
  update "[b \<leadsto> b - 1, c \<leadsto> c + 1, il_tl \<leadsto> red, il_pass \<leadsto> True]"

lemma "IL_out2b() preserves BridgeController2_inv"
  by zpog_full

zoperation ML_in2 =
  over BridgeController2
  pre "n > 0" "0 < c"
  update "[n \<leadsto> n - 1, c \<leadsto> c - 1]"

lemma "ML_in2() preserves BridgeController2_inv"
  apply zpog_full
  apply linarith
  by linarith
  
zoperation IL_in2 =
  over BridgeController2
  pre "0 < a"
  update "[b \<leadsto> b + 1, a \<leadsto> a - 1]"

lemma "IL_in2() preserves BridgeController2_inv"
  by zpog_full

zoperation ML_tl_green =
  over BridgeController2
  pre "ml_tl = red" "a + b < MAX_CARS" "c = 0" "il_pass = True"
  update "[ml_tl \<leadsto> green, il_tl \<leadsto> red, ml_pass \<leadsto> False]"

lemma "ML_tl_green() preserves BridgeController2_inv"
  apply zpog_full
  apply (simp add: tl_color_def)
  oops
  
zoperation IL_tl_green =
  over BridgeController2
  pre "il_tl = red" "0 < b" "a = 0" "ml_pass = True"
  update "[il_tl \<leadsto> green, ml_tl \<leadsto> red, il_pass \<leadsto> False]"

lemma "IL_tl_green() preserves BridgeController2_inv"
  apply zpog_full
  by (simp add: tl_color_def)

zoperation Show_cars2 =
  over BridgeController2
  emit n

zmachine BC2 =
  init BridgeController2Init
  operations ML_out2a ML_out2b IL_out2a IL_out2b ML_in2 IL_in2 ML_tl_green IL_tl_green Show_cars2

animate BC2
 (* defines MAX_CARS = 10*)

check_deadlock BC2
 (* defines MAX_CARS = 10 *)

lemma dlf_BC2: "deadlock_free BC2"
  by deadlock_free

text \<open> Third Refinement \<close>

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
  (*
  "ML_OUT_SR \<in> sensor_state"
  "ML_IN_SR \<in> sensor_state"
  "IL_OUT_SR \<in> sensor_state"
  "IL_IN_SR \<in> sensor_state"
  "A \<in> nat"
  "B \<in> nat"
  "C \<in> nat"
  "ml_out_10 \<in> bool"
  "ml_in_10 \<in> bool"
  "il_out_10 \<in> bool"
  "il_in_10 \<in> bool"
  *)
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
  update "[n\<Zprime> = 0, a\<Zprime> = 0, b\<Zprime> = 0, c\<Zprime> = 0,
          ml_tl\<Zprime> = red, il_tl\<Zprime> = red, ml_pass\<Zprime> = True, il_pass\<Zprime> = True,
          ml_out_10\<Zprime> = False, ml_in_10\<Zprime> = False, il_out_10\<Zprime> = False, il_in_10\<Zprime> = False,
          A\<Zprime> = 0, B\<Zprime> = 0, C\<Zprime> = 0, ML_OUT_SR\<Zprime> = off, ML_IN_SR\<Zprime> = off, IL_OUT_SR\<Zprime> = off, IL_IN_SR\<Zprime> = off]"

lemma "BridgeController3Init establishes BridgeController3_inv"
  apply zpog_full
  apply (simp add: tl_color_def)
  done

zoperation ML_out3a =
  over BridgeController3
  pre "n < MAX_CARS" 
      "a + b < MAX_CARS" 
      "c = 0" 
      "ml_tl = green" 
      "a + b + 1 \<noteq> MAX_CARS" 
      (*redundant guards*)
      "ml_out_10 = True"
  update "[n \<leadsto> n + 1, a \<leadsto> a + 1, ml_pass \<leadsto> True, ml_out_10 \<leadsto> False]"

lemma "ML_out3a() preserves BridgeController3_inv"
  apply zpog_full
   apply blast
  by blast
  
zoperation ML_out3b =
  over BridgeController3
  pre "n < MAX_CARS" 
      "a + b < MAX_CARS" 
      "c = 0" "ml_tl = green" 
      "a + b + 1 = MAX_CARS"  
      (*redundant guards*)
      "ml_out_10 = True"
  update "[n \<leadsto> n + 1, 
          a \<leadsto> a + 1, 
          ml_pass \<leadsto> True, 
          ml_tl \<leadsto> red, 
          ml_out_10 \<leadsto> False]"

lemma "ML_out3b() preserves BridgeController3_inv"
  by zpog_full
  
zoperation IL_out3a =
  over BridgeController3
  pre "0 < b" 
      "a = 0" 
      "il_tl = green" 
      "b \<noteq> 1"
      "il_out_10 = True"
  update "[b \<leadsto> b - 1, 
          c \<leadsto> c + 1, 
          il_pass \<leadsto> True,
          il_out_10 \<leadsto> False]"

lemma "IL_out3a() preserves BridgeController3_inv"
  by zpog_full
  

zoperation IL_out3b =
  over BridgeController3
  pre "0 < b" 
      "a = 0" 
      "il_tl = green" 
      "b = 1"
      "il_out_10 = True"
  update "[b \<leadsto> b - 1, 
          c \<leadsto> c + 1, 
          il_tl \<leadsto> red, 
          il_pass \<leadsto> True,
          il_out_10 \<leadsto> False]"

lemma "IL_out3b() preserves BridgeController3_inv"
  by zpog_full
  

zoperation ML_in3 =
  over BridgeController3
  pre "n > 0" 
      "0 < c"
      "ml_in_10 = True"
  update "[n \<leadsto> n - 1, 
          c \<leadsto> c - 1,
          ml_in_10 \<leadsto> False]"

lemma "ML_in3() preserves BridgeController3_inv"
  apply zpog_full
  apply linarith
   apply linarith
  by linarith
  
zoperation IL_in3 =
  over BridgeController3
  pre "0 < a"
      "il_in_10 = True"
  update "[b \<leadsto> b + 1, 
          a \<leadsto> a - 1,
          il_in_10 \<leadsto> False]"

lemma "IL_in3() preserves BridgeController3_inv"
  by zpog_full
  
zoperation ML_tl_green3 =
  over BridgeController3
  pre "ml_tl = red" 
      "a + b < MAX_CARS" 
      "c = 0" 
      "il_pass = True"
      "il_out_10 = False"
  update "[ml_tl \<leadsto> green, 
          il_tl \<leadsto> red, 
          ml_pass \<leadsto> False]"

lemma "ML_tl_green3() preserves BridgeController3_inv"
  apply zpog_full
  apply (metis UNIV_I tl_color_def)
  apply (metis UNIV_I tl_color_def)
  oops
  
zoperation IL_tl_green3 =
  over BridgeController3  
  pre "il_tl = red" 
      "0 < b" "a = 0" 
      "ml_pass = True"
      "ml_out_10 = False"
  update "[il_tl \<leadsto> green, 
          ml_tl \<leadsto> red, 
          il_pass \<leadsto> False]"

lemma "IL_tl_green3() preserves BridgeController3_inv"
  apply zpog_full
   apply (simp add: tl_color_def)
  apply (simp add: tl_color_def)
  done

zoperation ML_out_arr3 =
  over BridgeController3
  pre "ML_OUT_SR = off"
      "ml_out_10 = False"
  update "[ML_OUT_SR \<leadsto> working]"

lemma "ML_out_arr3() preserves BridgeController3_inv"
  by zpog_full
  
zoperation ML_in_arr3 =
  over BridgeController3
  pre "ML_IN_SR = off"
      "ml_in_10 = False"
      "C > 0"
  update "[ML_IN_SR \<leadsto> working]"

lemma "ML_in_arr3() preserves BridgeController3_inv"
  by zpog_full

zoperation IL_out_arr3 =
  over BridgeController3
  pre "IL_OUT_SR = off"
      "il_out_10 = False"
      "B > 0"
  update "[IL_OUT_SR \<leadsto> working]"

lemma "IL_out_arr3() preserves BridgeController3_inv"
  by zpog_full

zoperation IL_in_arr3 =
  over BridgeController3
  pre "IL_IN_SR = off"
      "il_in_10 = False"
      "A > 0"
  update "[IL_IN_SR \<leadsto> working]"

lemma "IL_in_arr3() preserves BridgeController3_inv"
  by zpog_full

zoperation ML_out_dep3 =
  over BridgeController3
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
  over BridgeController3
  pre "ML_IN_SR = working"
  update "[ML_IN_SR \<leadsto> off,
          ml_in_10 \<leadsto> True,
          C \<leadsto> C - 1]"

lemma "ML_in_dep3() preserves BridgeController3_inv"
  apply zpog_full
  apply linarith
  by linarith

zoperation IL_in_dep3 =
  over BridgeController3
  pre "IL_IN_SR = working"
  update "[IL_IN_SR \<leadsto> off,
          il_in_10 \<leadsto> True,
          A \<leadsto> A - 1,
          B \<leadsto> B + 1]"

lemma "IL_in_dep3() preserves BridgeController3_inv"
  by zpog_full
  

zoperation IL_out_dep3 =
  over BridgeController3
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
  
zoperation Show_cars3 =
  over BridgeController3
  emit n

zmachine BC3 =
  init BridgeController3Init
  operations ML_out3a ML_out3b IL_out3a IL_out3b 
             ML_in3 IL_in3 ML_tl_green3 IL_tl_green3 
             ML_out_arr3 ML_in_arr3 IL_out_arr3 IL_in_arr3
             ML_out_dep3 ML_in_dep3 IL_out_dep3 IL_in_dep3 Show_cars3

animate BC3
  (* defines MAX_CARS = 10 *)

check_deadlock BC3
 (* defines MAX_CARS = 10 *)

lemma dlf_BC3: "deadlock_free BC3"
  apply deadlock_free
  oops
  
  