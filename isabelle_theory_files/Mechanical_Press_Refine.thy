section \<open> Mechanical Press \<close>

theory Mechanical_Press_Refine
  imports "Z_Machines.Z_Machine"
begin      

text \<open> Mechanical Press Example from Abrial book Modelling in Event-B \<close>

enumtype STATUS = working | stopped

text \<open> Initial abstract model \<close>

subsection \<open> Initial Abstaction \<close>
zstore MechanicalPress0 =
  motor_actuator :: STATUS
  motor_sensor :: STATUS

zinit MechanicalPress0Init =
  over MechanicalPress0
  update 
    "[motor_actuator \<leadsto> stopped, 
      motor_sensor \<leadsto> stopped]"

lemma "MechanicalPress0Init establishes MechanicalPress0_inv"
  by zpog_full

zoperation Motor_start0 =
  pre 
    "motor_actuator = working"
    "motor_sensor = stopped"
  update 
    "[motor_sensor \<leadsto> working]"

lemma "Motor_start0() preserves MechanicalPress0_inv"
  by zpog_full

zoperation Motor_stop0 =
  pre 
    "motor_actuator = stopped"
    "motor_sensor = working"
  update 
    "[motor_sensor \<leadsto> stopped]"

lemma "Motor_stop0() preserves MechanicalPress0_inv"
  by zpog_full

zoperation Treat_start_motor0 =
  pre 
    "motor_actuator = stopped"
    "motor_sensor = stopped"
  update 
    "[motor_actuator \<leadsto> working]"

lemma "Treat_start_motor0() preserves MechanicalPress0_inv"
  by zpog_full

zoperation Treat_stop_motor0 =
  pre 
    "motor_actuator = working"
    "motor_sensor = working"
  update 
    "[motor_actuator \<leadsto> stopped]"

lemma "Treat_stop_motor0() preserves MechanicalPress0_inv"
  by zpog_full


zmachine MP0 =
  init MechanicalPress0Init
  operations Motor_start0 Motor_stop0 Treat_stop_motor0 Treat_start_motor0

animate MP0

check_deadlock MP0

lemma dlf_MP0: "deadlock_free MP0"
  apply deadlock_free
  by (metis STATUS.exhaust)

subsection \<open> Refinement 1, adding the controller \<close>

zstore MechanicalPress1 = MechanicalPress0 +
  start_motor_button :: bool
  stop_motor_button :: bool
  start_motor_impulse :: bool
  stop_motor_impulse :: bool

zinit MechanicalPress1Init =
  over MechanicalPress1
  update 
    "[motor_actuator \<leadsto> stopped, 
      motor_sensor \<leadsto> stopped,
      start_motor_button \<leadsto> False,
      stop_motor_button \<leadsto> False,
      start_motor_impulse \<leadsto> False,
      stop_motor_impulse \<leadsto> False]"


zoperation Motor_start1 =
  pre 
    "motor_actuator = working"
    "motor_sensor = stopped"
  extends
    "Motor_start0()"
  update 
    "[motor_sensor \<leadsto> working]"

lemma "Motor_start1() preserves MechanicalPress1_inv"
  by zpog_full

zoperation Motor_stop1 =
  pre 
    "motor_actuator = stopped"
    "motor_sensor = working"
  extends
    "Motor_stop0()"
  update 
    "[motor_sensor \<leadsto> stopped]"

lemma "Motor_stop1() preserves MechanicalPress1_inv"
  by zpog_full

zoperation Push_start_motor_button1 =
  pre 
    "start_motor_button = False"
  update 
    "[start_motor_button \<leadsto> True]"

lemma "Push_start_motor_button1() preserves MechanicalPress1_inv"
  by zpog_full

zoperation Release_start_motor_button1 =
  pre 
    "start_motor_button = True"
  update 
    "[start_motor_button \<leadsto> False]"

lemma "Release_start_motor_button1() preserves MechanicalPress1_inv"
  by zpog_full

zoperation Push_stop_motor_button1 =
  pre 
    "stop_motor_button = False"
  update 
    "[stop_motor_button \<leadsto> True]"

lemma "Push_stop_motor_button1() preserves MechanicalPress1_inv"
  by zpog_full

zoperation Release_stop_motor_button1 =
  pre 
    "stop_motor_button = True"
  update 
    "[stop_motor_button \<leadsto> False]"

lemma "Release_stop_motor_button1() preserves MechanicalPress1_inv"
  by zpog_full

zoperation Treat_start_motor1 =
  pre 
    "motor_actuator = stopped"
    "motor_sensor = stopped"
    "start_motor_impulse = False"
    "start_motor_button = True"

  update 
    "[motor_actuator \<leadsto> working,
      start_motor_impulse \<leadsto> True]"

lemma "Treat_start_motor1() preserves MechanicalPress1_inv"
  by zpog_full

zoperation Treat_start_motor_false1 =
  pre 
    "start_motor_impulse = False"
    "start_motor_button = True"
  update 
    "[start_motor_impulse \<leadsto> True]"

lemma "Treat_start_motor_false1() preserves MechanicalPress1_inv"
  by zpog_full

zoperation Treat_stop_motor1 =
  pre 
    "motor_actuator = working"
    "motor_sensor = working"
    "stop_motor_impulse = False"
    "stop_motor_button = True"
  extends
    "Treat_stop_motor0()"
  update 
    "[motor_actuator \<leadsto> stopped,
      stop_motor_impulse \<leadsto> True]"

lemma "Treat_stop_motor1() preserves MechanicalPress1_inv"
  by zpog_full

zoperation Treat_stop_motor_false1 =
  pre 
    "stop_motor_impulse = False"
    "stop_motor_button = True"
  update 
    "[stop_motor_impulse \<leadsto> True]"

lemma "Treat_start_motor_false1() preserves MechanicalPress1_inv"
  by zpog_full

zoperation Treat_release_start_motor_button1 =
  pre 
    "start_motor_impulse = True" 
    "start_motor_button = False"
  update 
    "[start_motor_impulse \<leadsto> False]"

lemma "Treat_release_start_motor_button1() preserves MechanicalPress1_inv"
  by zpog_full

zoperation Treat_release_stop_motor_button1 =
  pre 
    "stop_motor_impulse = True"
    "stop_motor_button = False"
  update 
    "[stop_motor_impulse \<leadsto> False]"

lemma "Treat_release_stop_motor_button1() preserves MechanicalPress1_inv"
  by zpog_full

zmachine MP1 =
  init MechanicalPress1Init
  operations 
             Motor_start1 Motor_stop1
             Push_start_motor_button1 
             Release_start_motor_button1
             Push_stop_motor_button1 
             Release_stop_motor_button1
             Treat_start_motor1
             Treat_start_motor_false1
             Treat_stop_motor1
             Treat_stop_motor_false1
             Treat_release_start_motor_button1    
             Treat_release_stop_motor_button1 

animate MP1

check_deadlock MP1

lemma dlf_MP1: "deadlock_free MP1"
  apply deadlock_free
  apply (simp add: dfp_output_return dlf_mk_zop)
  by (simp add: dfp_output_return dlf_mk_zop)

subsection \<open> Refinement 2 \<close>

text \<open> Refinement 2 adds the clutch, events and variables are the
       same as was used for the motor in the initial abstract model \<close>

zstore MechanicalPress2 = MechanicalPress1 +
  clutch_actuator :: STATUS
  clutch_sensor :: STATUS

zinit MechanicalPress2Init =
  over MechanicalPress2
  update "[clutch_actuator \<leadsto> stopped, 
           clutch_sensor \<leadsto> stopped]"

zoperation Treat_start_clutch =
  pre
    "clutch_actuator = stopped"
    "clutch_sensor = stopped"
  update
    "[clutch_actuator \<leadsto> working]"

zoperation Treat_stop_clutch =
  pre
    "clutch_actuator = working"
    "clutch_sensor = working"
  update
    "[clutch_actuator \<leadsto> stopped]"

zoperation Clutch_start =
  pre
    "clutch_sensor = stopped"
    "clutch_actuator = working"
  update
    "[clutch_sensor \<leadsto> working]"

zoperation Clutch_stop =
  pre
    "clutch_sensor = working"
    "clutch_actuator = stopped"
  update
    "[clutch_sensor \<leadsto> stopped]"

zmachine MP2 =
  init MechanicalPress2Init
  operations
             Push_start_motor_button1 Release_start_motor_button1
             Treat_push_start_motor_button1 Treat_release_start_motor_button1
             Push_stop_motor_button1 Release_stop_motor_button1
             Treat_push_stop_motor_button1 Treat_push_start_motor_button_false1
             Treat_start_clutch Treat_stop_clutch Clutch_start Clutch_stop

animate MP2

check_deadlock MP2

lemma dlf_MP2: "deadlock_free MP2"
  apply deadlock_free
   apply (simp add: dfp_output_return dlf_mk_zop)
  oops