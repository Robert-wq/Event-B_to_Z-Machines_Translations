section \<open>File Transfer Protocol Revisited \<close>

theory File_transfer_Protocol_Revisited
  imports "Z_Machines.Z_Machine"
begin   

text \<open>This theory file shows an implementation of the Simple File Transfer Protocol
      from J. R. Abrial's book Modelling in Event-B, System and Software Engineering.
      There are some implementation differences between this implementation and the
      Event-B implementation.\<close>

text \<open>The Simple File Transfer Protocol here is implemented in Z-Machines. It consists of 
      The initial model and three refinements of the system. There are some
      differences between the Event-B model and the Z-Machines model and these are mainly
      down to types and the way types are specified. There are comments throughout that
      explain the model and differences.\<close>

type_synonym data = "int set"

text \<open>The Event-B implementation of this system used a generic carrier set to implement
      D. However implementing this in Z-Machines proved difficult. Therefore D has been
      implemented as a list of integers. It represents data on the data channel. This makes
      less general, however using integers to represent data transmission does make it 
      easier to observe how the transmission is progressing.\<close>

consts 
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
  (*g represents the receivers file*)
  g :: "nat \<Zpfun> int" 
  where
  "\<forall> x \<in> dom(g) . x > 0"

zinit FTPInit =
  over "FTP"
  update "[g \<leadsto> {\<mapsto>}]"

(*In this initial abstraction, this event essentially simulates the entire file has been
copied.*)
zoperation Final =
  pre
    "g = f"

lemma Final_correct [hoare_lemmas]: "Final p preserves FTP_inv"
  by zpog_full

(*This operation is an aticipatory event. The definition here is somewhat confusing.
It is the update section of the operation should state that g is in the set "\<nat> \<longleftrightarrow> D"*)
zoperation Recieve =
  pre 
    "g \<noteq> f"
  update
    "[g \<leadsto> g \<oplus> {\<mapsto>}]"

(*shows the data portion of f*)
zoperation Show_f =
  emit "ran(f)"

(*shows the data portion of g*)
zoperation Show_g =
  emit "ran(g)"

zmachine FTPMachine =
  init FTPInit
  operations Final Show_f Show_g


text \<open>Without the Show_f and Show_g events, this machine would deadlock after applying
      operation Final, that is the intended functionality for this initial abstraction.
      Once the final command has been applied we can see that the contents of f have
      been successfully transferred to g. TODO - see if can fix range command and output
      a list instead\<close>
animate FTPMachine
  defines f = "test_file"

subsection \<open>Refinement 1\<close>

zstore FTP1 = FTP +
  r :: nat
  where 
  "r > 0 \<and> r \<le> n + 1"
  "g = {1..r - 1} \<Zdres> f"
  
zinit FTPInit1 =
  over "FTP1"
  update "[g \<leadsto> {\<mapsto>},
           r \<leadsto> 1]"

zoperation Recieve1 =
  pre
    "r \<le> n"
  extends "Recieve()"
  update
    "[g \<leadsto> g \<oplus> {r \<mapsto> f(r)},
      r \<leadsto> (r + 1)]"

zoperation Final1 =
  pre
    "r = n + 1"

zoperation Show_r =
 emit r

(*Idea - It would be good if the animator could show system state
perhaps in a seperate jedit tab*)
zmachine FTPMachine1 =
  init FTPInit1
  operations Recieve1 Final1 Show_f Show_g Show_r

animate FTPMachine1
  defines f = test_file

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
    "[g \<leadsto> {\<mapsto>},
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
    "[g \<leadsto> g \<oplus> {r \<mapsto> d},
      r \<leadsto> r + 1]"

zoperation Final2 =
  pre
    "r = n + 1"

zoperation Show_d =
  emit d

zmachine FTPMachine2 =
  init FTPInit2
  operations Recieve2 Final2 Send Show_f Show_d Show_g

animate FTPMachine2
  defines f = test_file


subsection \<open>Refinement 3\<close>

fun parity :: "nat \<Rightarrow> nat" where
  "parity 0 = 0" |
  "parity (Suc x) = 1 - parity x"

(*Proof for function in Event-B syntax*)
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
    "[g \<leadsto> {\<mapsto>},
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
    "[g \<leadsto> g \<oplus> {r \<mapsto> d},
      r \<leadsto> r + 1,
      q \<leadsto> 1 - q]"

zoperation Final3 =
  pre
    "r = n + 1"

zoperation Show_g_dom =
  emit "dom(g)"

zoperation Show_f_dom =
  emit "dom(f)"

zmachine FTPMachine3 =
  init FTPInit3
  operations Recieve3 Final3 Send2 Show_f_dom Show_f Show_d Show_g Show_g_dom 

animate FTPMachine3
  defines f = test_file