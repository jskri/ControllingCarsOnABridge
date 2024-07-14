theory cars_on_bridge_0
  imports Main cars_on_bridge_constants
begin

(* Cars that are not on mainland, i.e. that are on bridge or island. *)
datatype state0
  = State0 (nonMlCarCount: int)

(* Two events: 1. a car enters the mainland
               2. a car exits the mainland *)
datatype event0
  = MlIn0
  | MlOut0
  | Stutter0

(* State0 that results from an event0 applying to a given state0. *)
fun step0 :: "event0 \<Rightarrow> state0 \<Rightarrow> state0 option" where
  "step0 MlIn0   (State0 n) = (if n > 0       then Some (State0 (n - 1)) else None)" |
  "step0 MlOut0  (State0 n) = (if n < maxCars then Some (State0 (n + 1)) else None)" |
  "step0 Stutter0 s         = Some s"

(* A behavior0 is a sequence of states, where each state0 after the first is
obtained through the step0 function. *)
inductive behavior0 :: "state0 list \<Rightarrow> bool" where
  init: "behavior0 [State0 0]" | (* Initially, there's no car. *)
  succ: "\<lbrakk> behavior0 (states @ [s]);
           step0 ev s = Some s' \<rbrakk> \<Longrightarrow> behavior0 ((states @ [s]) @ [s'])"

lemma step0_n_nonneg:
  assumes "n \<ge> 0 \<and> Some (State0 n') = step0 ev (State0 n)"
  shows "n' \<ge> 0"
  by (smt (verit, best) assms option.distinct(1) option.inject state0.inject step0.elims)

fun last_n_nonneg :: "state0 list \<Rightarrow> bool" where
  "last_n_nonneg [] = False" |
  "last_n_nonneg states = (case last states of State0 n \<Rightarrow> n \<ge> 0)"

lemma typeOK0:
  assumes "behavior0 states"
  shows "last_n_nonneg states"
  using assms
proof (induction rule: behavior0.induct)
  case init
  then show ?case
    by simp
next
  case (succ ss last ev s')
  moreover obtain n where "last = State0 n"
    using state0.exhaust_sel by blast
  moreover have "n \<ge> 0"
    using \<open>last_n_nonneg (ss @ [last])\<close>
    by (metis calculation(4) last_n_nonneg.cases last_n_nonneg.simps(2) snoc_eq_iff_butlast state0.case)
  moreover obtain n' where "Some (State0 n') = step0 ev last" (* "step0 ev last" is the new state. *)
    by (metis state0.exhaust_sel succ.hyps(2))
  moreover have "n' \<ge> 0"
    using calculation step0_n_nonneg by blast
  ultimately show ?case
    by (metis last_n_nonneg.elims(3) snoc_eq_iff_butlast state0.case state0.exhaust_sel step0_n_nonneg)
qed

end