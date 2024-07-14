theory cars_on_bridge_1
  imports Main cars_on_bridge_0 cars_on_bridge_constants
begin

(* Cars that are not on mainland, i.e. that are on bridge or island. *)
datatype state1
  = State1 int (* Number of cars going to the island. *)
          int (* Number of cars on the island. *)
          int (* Number of cars going to the mainland. *)

(* Two events: 1. a car enters the mainland
               2. a car exits the mainland *)
datatype event1
  = MlIn1
  | MlOut1
  | IlIn1
  | IlOut1
  | Stutter1

(* State1 that results from an event1 applying to a given state1. *)
fun step1 :: "event1 \<Rightarrow> state1 \<Rightarrow> state1 option" where
  "step1 ev (State1 a b c) = (let s = State1 a b c in
   (case ev of
      MlIn1    \<Rightarrow> (if c > 0                       then Some (State1 a b (c - 1)) else None) |
      MlOut1   \<Rightarrow> (if a + b + c < maxCars \<and> c = 0 then Some (State1 (a + 1) b c) else None) |
      IlIn1    \<Rightarrow> (if a > 0                       then Some (State1 (a - 1) (b + 1) c) else None) |
      IlOut1   \<Rightarrow> (if a = 0 \<and> b > 0               then Some (State1 a (b - 1) (c + 1)) else None) |
      Stutter1 \<Rightarrow> Some s
   ))"

(* A behavior is a sequence of states, where each state after the first is
obtained through the step1 function. *)
inductive behavior1 :: "state1 list \<Rightarrow> bool" where
  init: "behavior1 [State1 0 0 0]" | (* Initially, there's no car. *)
  succ: "\<lbrakk> behavior1 (states @ [s]);
           Some s' = step1 ev s \<rbrakk>  \<Longrightarrow>
           behavior1 ((states @ [s]) @ [s'])"

lemma step_abc_nonneg:
  assumes "(a \<ge> 0 \<and> b \<ge> 0 \<and> c \<ge> 0) \<and> Some (State1 a' b' c') = step1 ev (State1 a b c)"
  shows "a' \<ge> 0 \<and> b' \<ge> 0 \<and> c' \<ge> 0"
  by (smt (verit, ccfv_threshold) assms event1.case event1.exhaust option.distinct(1)
      option.inject state1.inject step1.simps)

fun last_abc_nonneg :: "state1 list \<Rightarrow> bool" where
  "last_abc_nonneg [] = False" |
  "last_abc_nonneg states = (case last states of State1 a b c \<Rightarrow> (a \<ge> 0 \<and> b \<ge> 0 \<and> c \<ge> 0))"

theorem typeOK:
  assumes "behavior1 states"
  shows "last_abc_nonneg states"
  using assms
proof (induction rule: behavior1.induct)
  case init
  then show ?case
    by simp
next
  case (succ ss last s' ev)
  moreover obtain a b c where "last = State1 a b c"
    using state1.exhaust by blast
  moreover have "a \<ge> 0 \<and> b \<ge> 0 \<and> c \<ge> 0"
    by (metis calculation(4) last_abc_nonneg.elims(2) last_snoc local.succ(3) state1.case)
  moreover obtain a' b' c' where "Some (State1 a' b' c') = step1 ev last" (* "step1 ev last" is the new state. *)
    by (metis state1.exhaust succ.hyps(2))
  moreover have "a' \<ge> 0 \<and> b' \<ge> 0 \<and> c' \<ge> 0"
    using calculation(4) calculation(5) calculation(6) step_abc_nonneg by blast
  ultimately show ?case
    by (metis last_abc_nonneg.elims(3) option.inject snoc_eq_iff_butlast state1.case)
qed

lemma step_a_or_c_eq_0:
  assumes "(a = 0 \<or> c = 0) \<and> Some (State1 a' b' c') = step1 ev (State1 a b c)"
  shows "a' = 0 \<or> c' = 0"
  by (smt (verit, del_insts) assms event1.case event1.exhaust option.distinct(1)
      option.inject state1.inject step1.simps)

fun last_a_or_c_eq_0 :: "state1 list \<Rightarrow> bool" where
  "last_a_or_c_eq_0 [] = False" |
  "last_a_or_c_eq_0 states = (case last states of State1 a b c \<Rightarrow> (a = 0 \<or> c = 0))"

theorem oneWayBridge:
  assumes "behavior1 states"
  shows "last_a_or_c_eq_0 states"
  using assms
proof (induction rule: behavior1.induct)
  case init
  then show ?case
    by simp
next
  case (succ ss last s' ev)
  moreover obtain a b c where "last = State1 a b c"
    using state1.exhaust by blast
  moreover have "a = 0 \<or> c = 0"
    by (metis (mono_tags, lifting) calculation(4) last_a_or_c_eq_0.elims(2) last_snoc state1.case succ.IH)
  moreover obtain a' b' c' where "Some (State1 a' b' c') = step1 ev last" (* "step1 ev last" is the new state. *)
    by (metis state1.exhaust succ.hyps(2))
  moreover have "a' \<ge> 0 \<and> b' \<ge> 0 \<and> c' \<ge> 0"
    by (metis calculation(4) calculation(6) last_a_or_c_eq_0.elims(2) last_abc_nonneg.simps(2)
        last_snoc local.succ(1) local.succ(3) state1.case step_abc_nonneg typeOK)
  ultimately show ?case
    by (metis (mono_tags, lifting) last_a_or_c_eq_0.elims(3) option.inject snoc_eq_iff_butlast state1.case step_a_or_c_eq_0)
qed

(* The refinement mapping. *)
fun refine :: "state1 \<Rightarrow> state0" where
  "refine (State1 a b c) = State0 (a + b + c)"

fun to_ev0 :: "event1 \<Rightarrow> event0" where
  "to_ev0 MlIn1    = MlIn0" |
  "to_ev0 MlOut1   = MlOut0" |
  "to_ev0 IlIn1    = Stutter0" |
  "to_ev0 IlOut1   = Stutter0" |
  "to_ev0 Stutter1 = Stutter0"

lemma step_refinement:
  assumes "behavior1 (states @ [s])"
      and "step1 ev s = Some s'"
    shows "step0 (to_ev0 ev) (refine s) = Some (refine s')"
  using assms
proof (cases ev)
  case MlIn1
  moreover obtain a b c n where "(State1 a b c = s) \<and> (State0 n = refine s)"
    by (metis refine.elims)
  moreover have "(a \<ge> 0 \<and> b \<ge> 0 \<and> c \<ge> 0) \<and> (n \<ge> 0)"
    by (smt (verit, del_insts) assms calculation(2) last_abc_nonneg.elims(2) last_snoc
        refine.simps state0.sel state1.case typeOK)
  ultimately show ?thesis
    using assms by (smt (verit) event1.case(1) option.distinct(1) option.sel refine.simps
                    step0.simps(1) step1.simps to_ev0.simps(1))
next
  case MlOut1
  then show ?thesis
    using assms by (smt (verit) event0.distinct(1) event0.distinct(5) event1.case(2)
          option.distinct(1) option.sel refine.elims state0.inject state1.inject step0.elims
          step1.elims to_ev0.simps(2))
next
  case IlIn1
  then show ?thesis
    using assms by (smt (verit, del_insts) event1.case(3) option.distinct(1) option.sel
        refine.elims state1.inject step0.simps(3) step1.elims to_ev0.simps(3))
next
  case IlOut1
  then show ?thesis
    using assms by (smt (verit, ccfv_SIG) event1.case(4) option.distinct(1) option.sel
        refine.elims state1.inject step0.simps(3) step1.elims to_ev0.simps(4))
next
  case Stutter1
  then show ?thesis
    by (smt (verit, ccfv_SIG) assms(2) event1.case(5) option.sel step0.simps(3)
        step1.elims to_ev0.simps(5))
qed

theorem refinement:
  assumes "behavior1 states"
  shows "behavior0 (map refine states)"
  using assms
proof (induction rule: behavior1.induct)
  case init
  then show ?case
    by (simp add: behavior0.init)
next
  case (succ ss last ev)
  then show ?case
    by (metis (mono_tags, lifting) behavior0.succ list.simps(8) list.simps(9) map_append step_refinement)
qed

end