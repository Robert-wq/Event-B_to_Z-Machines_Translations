section \<open> Mechanical Lung Ventilator \<close>

theory Mechanical_Lung_Ventilator
  imports "Z_Machines.Z_Machine"
begin      

text \<open> This theory file contains a Z-Machines representation of a mechanical
       lung ventilator. It is a direct translation of an Event-B implementation
       of the same specification from a paper by Silvia Bonfanti and Angelo Gargantini. 
      TODO - ADD REFERENCE HERE \<close>

text \<open>All of the different states\<close>
enumtype Modes = StartUp | Start | Menu | SelfTest | Settings | Off  | PCV | PSV

text \<open> The two different modes of the ventilator when it is operational\<close>
definition "Ventilation = {PCV, PSV}"

definition "ModesG = {StartUp, Start, Menu, SelfTest, Settings, Off} \<union> Ventilation"

(* BOOL --> \<bbbP>(ModesG x ModesG)*)
(*consts possTransG :: "ModesG \<Zpfun> ModesG"*)
consts batteryRange :: nat
(* \<times> *)

(* TODO - Still need to write invariants 4 and 5*)
zstore MechanicalVent0 =
  power :: bool (*power button*)
  onAC :: bool (*powered  by AC or not*)
  batLev :: nat
  switchover :: bool (*switchover between AC and backup battery*)
  crashed :: bool
  modeG :: Modes (*Current GUI state*)
  modeGP :: "Modes" (*Previous GUI state*)
  curTime :: nat
  batFail :: bool
  where
  "crashed = True \<or> power = False \<or> (onAC = False \<and> (switchover = False \<and> batLev =  0
   \<or> batFail = True)) \<longleftrightarrow> modeG=Off"

(*batLev arbitrarily set to 50 at the moment, may be better modelled as 
a const and defined on machine creation*)
zinit MechanicalVent0Init =
  over MechanicalVent0
  update "[power \<leadsto> False,
           batLev \<leadsto> 50, 
           onAC \<leadsto> True,
           switchover \<leadsto> True,
           crashed \<leadsto> False,
           modeG \<leadsto> Off,
           modeGP \<leadsto> Off,
           curTime \<leadsto> 0,
           batFail \<leadsto> False]"

zoperation PowerOn =
  pre 
      "power = False"
      (*Either has AC power or has battery power*)
      "(onAC = True) \<or> (switchover = True \<and> batLev > 0 \<and> batFail = False)"
  update
      "[power \<leadsto> True,
        modeG \<leadsto> {False \<mapsto> StartUp, True \<mapsto> Off}(crashed),
        modeGP \<leadsto> modeG]"

zoperation PowerOff =
  pre
    "power = True"
  update
    "[power \<leadsto> False,
      modeG \<leadsto> Off,
      modeGP \<leadsto> modeG]"

zoperation StartUpEndedGui =
  params 
    modeg \<in> ModesG
  pre
    "modeG = StartUp"
    (*The Event-B spec uses union {Start} U Ventilation
    to show this guard, this causes Isabelle to throw a type error
    due to typing modeg as ModesG*)
    "modeg \<in> {Start, Ventilation}"
  update
    "[modeG \<leadsto> modeg,
      modeGP \<leadsto> modeG]"

zoperation Crash =
  pre
    "crashed = False"
  update
    "[crashed \<leadsto> True,
      modeG \<leadsto> Off,
      modeGP \<leadsto> Off]"

zoperation Repare =
  params
    modeg \<in> ModesG
  pre
    "crashed = True"
    "power = False \<or> (onAC = False \<and> (switchover = False \<or> batLev = 0  \<or> batFail = True))
      \<longrightarrow>
      modeg=Off"
    "power = True \<or> (onAC = True \<and> (switchover = True \<or> batLev = 0  \<or> batFail = False))
      \<longrightarrow>
      modeg=StartUp"
  update
    "[crashed \<leadsto> False,
     modeG \<leadsto> modeg,
     modeGP \<leadsto> modeG]"

zoperation NewPatient =
  pre
    "modeG = Start"
  update
    "[modeG \<leadsto> SelfTest,
      modeGP \<leadsto> modeG]"

zoperation ResumeVent =
  pre
    "modeG = Start"
  update 
    "[modeG \<leadsto> Menu,
    modeGP \<leadsto> modeG]"

zoperation RunAbortSelfTest =
  pre
    "modeG = SelfTest"
  update
    "[modeG \<leadsto> SelfTest,
      modeGP \<leadsto> modeG]"

zoperation SelfTestPassed =
  pre
    "modeG = SelfTest"
  update
    "[modeG \<leadsto> Menu,
      modeGP \<leadsto> modeG]"

zoperation SetParam =
  pre
    (*TODO - Same issue here as with StartUpEndedGui*)
    "modeG \<in> {Menu, Ventilation}"
  update
    "[modeG \<leadsto> Settings,
      modeGP \<leadsto> modeG]"

zoperation SaveBackAbort =
  params
    modeg \<in> ModesG
  pre
    (*Event-B example has a type check here that modeg is in ModesG
    however in Z-Machines this is handles in params above*)
    "modeG = Settings"
    (*TODO - same issues as StartUpEndedGui*)
    "modeg \<in> {Ventilation, Menu}"
  update
    "[modeG \<leadsto> modeg,
     modeGP \<leadsto>  modeG]"

(*TODO - specify this operation*)
(*Can't specify this operation without dealing with the issue of the
union of ventilation set*)

(* Specification of this operation is completely different from
Event-B spec, due to not using the subset Ventilation *)
(*
zoperation StartStopPCVPSV =
  params
    modeg \<in> ModesG
  pre
    "modeG \<in> ModesG"
    "modeg \<in> ModesG"
    "modeG = Menu \<longrightarrow> modeg \<in> ModesG"
    "modeG \<in> Ventilation"
*)



zmachine MLV0 =
  init MechanicalVent0Init
  operations PowerOn PowerOff StartUpEndedGui Crash Repare NewPatient ResumeVent 
             RunAbortSelfTest SelfTestPassed SetParam SaveBackAbort

animate MLV0

