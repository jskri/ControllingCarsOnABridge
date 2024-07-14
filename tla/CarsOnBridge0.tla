--------------------------- MODULE CarsOnBridge0 ---------------------------
(***************************************************************************)
(* First model of course 02: Controlling cars on a bridge                  *)
(*                                                                         *)
(* This model is only concerned with limiting the number of cars on the    *)
(* island and brige.                                                       *)
(*                                                                         *)
(* See https://www.event-b.org/A_ch2.pdf                                   *)
(*                                                                         *)
(*                      ML_out                                             *)
(*  -----------------   <-----   ----------                                *)
(* | Island + Bridge |          | MainLand |                               *)
(*  -----------------   ----->   ----------                                *)
(*                      ML_in                                              *)
(*                                                                         *)
(***************************************************************************)

EXTENDS CarsOnBridgeConstants, TLAPS
VARIABLES n \* Number of cars on island + brige.

Init ==
  n = 0

Correct ==
  /\ n \in Nat \* type ok
  /\ n <= d  \* at most d cars

\* A car enters the mainland.
ML_in ==
  /\ n > 0
  /\ n' = n - 1

\* A car leaves the mainland.
ML_out ==
  /\ n < d
  /\ n' = n + 1

Next ==
  \/ ML_in
  \/ ML_out

Spec ==
  /\ Init
  /\ [][Next]_n

DeadlockFree ==
  \/ ENABLED ML_in
  \/ ENABLED ML_out
-----------------------------------------------------------------------------
THEOREM InvCorrect == Spec => []Correct
<1>1. Init => Correct
  BY AssumeD DEF Init, Correct
<1>2. Correct /\ [Next]_n => Correct'
  BY AssumeD DEF Correct, Next, ML_in, ML_out
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM InvDeadlockFree == Spec => []DeadlockFree
<1>1. Init => DeadlockFree
  BY AssumeD, ExpandENABLED, AutoUSE DEF Init, DeadlockFree
<1>2. Correct /\ DeadlockFree /\ [Next]_n => DeadlockFree'
  BY AssumeD, ExpandENABLED DEF Correct, DeadlockFree, Next, ML_in, ML_out
<1>3. QED
  BY InvCorrect, <1>1, <1>2, PTL DEF Spec
=============================================================================