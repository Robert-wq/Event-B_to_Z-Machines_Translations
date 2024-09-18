section \<open>File Transfer Protocol \<close>

theory File_Transfer_Protocol
  imports "Z_Machines.Z_Machine"
begin   

text \<open>This theory file shows an implementation of the Simple File Transfer Protocol
      from J. R. Abrial's book Modelling in Event-B, System and Software Engineering.
      There are some implementation differences between this implementation and the
      Event-B implementation. However for an in depth overview of how the system should
      work, please see this source material. TODO - reference, with pg numbers\<close>

text \<open>The Simple File Transfer Protocol here is implemented in Z-Machines. It consists of 
      The initial model and the first two refinements of the system. There are some
      differences between the Event-B model and the Z-Machines model and these are mainly
      down to types and the way types are specified. There are comments throughout that
      explain the model and differences.\<close>

(*MAX _CARS declared and set here in order to support deadlock freedom checks*)
(*def_consts n = 2*)
(*declare n_def [simp]*)

(* n =  10 *)

(*Symbol for \<nat>1 would be helpfull *)
typedef n1 = "{n :: nat . n > 0}"
  by auto


(*this is where 10 is the upperbound*)
typedef test = "{n :: nat . n > 0 \<and> n \<le> 10}"
  by auto

(*Realistically the data would most likely be a 0 or 1, but it has been modelled
here as an int so that different numbers can be seen in the animation.*)
type_synonym data = "int set"
type_synonym f1 = "nat \<rightarrow> int"

text \<open>The Event-B implementation of this system used a generic carrier set to implement
      D. However implementing this in Z-Machines proved difficult. Therefore D has been
      implemented as a list of integers. It represents data on the data channel. This makes
      less realistic, however using integers to represent data transmission does make it 
      easier to observe how the transmission is progressing.\<close>

consts 
  D :: "int list"
  f :: "nat \<Zpfun> int" (*represents the data in the senders file*)
  n :: "nat" (*represents the size of the data in the file*)

text \<open>test_file contains a dummy data file, not an ideal way to set this up,
but makes it easier than defining data at initilisation for each machine.
The function is purposely injective, as displaying the outputs of events using 'emit',
meant displaying them as sets, which makes it difficult to observe the output if there are
duplicate values. \<close>
definition test_file :: "nat \<Zpfun> int" where
"test_file = {1\<mapsto>9, 2\<mapsto>3, 3\<mapsto>7, 4\<mapsto>4, 5\<mapsto>1, 6\<mapsto>-1}"
(*gets the length of the domain of test_file
This is a hack to avoid re-specifying the constants when initilizing the machine*)
def_consts n = "length(sorted_list_of_set(dom(test_file)))"

subsection \<open>Initial Abstraction\<close>

zstore FTP =
  g :: "nat \<Zpfun> int" (*g represents the receivers file*)
  b :: bool (*b is used to check if the file has been successfully tranfered or not*)
  where
  "b = False \<longrightarrow> g = {\<mapsto>}" 
  "b = True \<longrightarrow> g = f"

zinit FTPInit =
  over "FTP"
  update "[g \<leadsto> {\<mapsto>},
           b \<leadsto> False]"

(*Remember to talk about the fact that z-operations need to start with capital letter*)

(*In this initial abstraction, this event essentially simulates the entire file has been
copied.*)
zoperation Final =
  pre
    "b = False"
  update
    "[g \<leadsto> f,
      b \<leadsto> True]"

lemma Final_correct [hoare_lemmas]: "Final p preserves FTP_inv"
  by zpog_full
  
(*shows the data portion of f*)
zoperation Show_f =
  emit "ran(f)"

(*shows the data portion of g*)
zoperation Show_g =
  emit "ran(g)"

zmachine FTPMachine =
  init FTPInit
  operations Final Show_f Show_g

text \<open>No deadlock freedom proof as the machine is designed to deadlock at this point\<close>


text \<open>Without the Show_f and Show_g events, this machine would deadlock after applying
      operation Final, that is the intended functionality for this initial abstraction.
      Once the final command has been applied we can see that the contents of f have
      been successfully transferred to g. TODO - see if can fix range command and output
      a list instead\<close>
animate FTPMachine
  defines D = "[]" f = "test_file"

subsection \<open>Refinement 1\<close>

zstore FTP1 = FTP +
  r :: nat
  h :: "nat \<Zpfun> int"
  where 
  "r > 0 \<and> r \<le> n + 1"
  "h = {0..r} \<Zdres> f"
  "b = True \<longrightarrow> r = n + 1"

zinit FTPInit1 =
  over "FTP1"
  update "[b \<leadsto> False,
           h \<leadsto> {\<mapsto>},
           r \<leadsto> 1]"

zoperation Recieve =
  pre
    "r \<le> n"
  update
    "[h \<leadsto> h \<oplus> {r \<mapsto> f(r)},
      r \<leadsto> (r + 1)]"

zoperation Final1 =
  pre
    "b = False"
    "r = n + 1"
  update
    "[g \<leadsto> f,
      b \<leadsto> True]" 

zoperation Show_r =
 emit r

zoperation Show_h_dom =
  emit "dom(h)"

zoperation Show_h_ran =
  emit "ran(h)"

(*Idea - It would be good if the animator could show system state
perhaps in a seperate jedit tab*)
zmachine FTPMachine1 =
  init FTPInit1
  operations Recieve Final1 Show_f Show_g Show_r Show_h_dom Show_h_ran

animate FTPMachine1
  defines D = "[]" f = test_file


subsection \<open>Refinement 2\<close>

zstore FTP2 = FTP1 +
  s :: nat
  d :: int
  where 
  "d \<in> data"
  "s \<le> n + 1"
  "s \<ge> r \<and> s \<le> r + 1"
  "s = r + 1 \<longrightarrow>  d = f(r)"  

zinit FTPInit2 =
  over FTP2
  update
    "[b \<leadsto> False,
      h \<leadsto> {\<mapsto>},
      s \<leadsto> 1,
      r \<leadsto> 1,
      d \<leadsto> 0]"

zoperation Send =
  pre
    "s = r"
    "r \<noteq> n + 1"
  update
    "[d \<leadsto> f(s),
      s \<leadsto> s + 1]"

zoperation Recieve2 =
  pre
    "s = r + 1"
  update
    "[h \<leadsto> h \<oplus> {r \<mapsto> d},
      r \<leadsto> r + 1]"

zoperation Final2 =
  pre
    "b = False"
    "r = n + 1"
  update
    "[g \<leadsto> f,
      b \<leadsto> True]" 

zoperation Show_d =
  emit d

zmachine FTPMachine2 =
  init FTPInit2
  operations Recieve2 Final2 Send Show_f Show_d Show_g Show_h_ran

animate FTPMachine2
  defines D = "[]" f = test_file

subsection \<open>Refinement 3\<close>

fun parity :: "nat \<Rightarrow> nat" where
  "parity 0 = 0" |
  "parity (Suc x) = 1 - parity x"

(*lemma a:  "\<forall>x y. x \<in> {y..y+1} \<and> parity(x) = parity(y) \<turnstile> x = y"*)


zstore FTP3 = FTP2 +
    p :: nat
    q :: nat
  where
    "p = parity(s)"
    "q = parity(r)"

zinit FTPInit3 =
  over FTP3
  update
    "[b \<leadsto> False,
      h \<leadsto> {\<mapsto>},
      s \<leadsto> 1,
      r \<leadsto> 1,
      p \<leadsto> 1,
      q \<leadsto> 1,
      d \<leadsto> 0]"
    
zoperation Send2 =
  pre
    "p = q"
    "s \<noteq> n + 1"
  update
    "[d \<leadsto> f(s),
      s \<leadsto> s + 1,
      p \<leadsto> 1 - p]"

zoperation Recieve3 = 
  pre
    "p \<noteq> q"
  update
    "[h \<leadsto> h \<oplus> {r \<mapsto> d},
      r \<leadsto> r + 1,
      q \<leadsto> 1 - q]"

zoperation Final3 =
  pre
    "b = False"
    "r = n + 1"
  update
    "[b \<leadsto> True]"


zmachine FTPMachine3 =
  init FTPInit3
  operations Recieve3 Final3 Send2 Show_f Show_d Show_g Show_h_ran

animate FTPMachine3
  defines D = "[]" f = test_file


