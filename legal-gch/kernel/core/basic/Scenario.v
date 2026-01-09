(* Scenario.v - Definitions for dispute scenarios *)

Require Import Coq.Init.Nat.

(* Scenario record for breach notification example *)
Record scenario := mk_scenario {
  incident_time : nat;  (* time of incident *)
  awareness_time : option nat;  (* time vendor becomes aware *)
  notification_time : option nat;  (* time vendor notifies *)
  disclosure_time : option nat;  (* time confidential info disclosed *)
  breach_by_other_time : option nat;  (* time breach by other party *)
  claimed_damages : nat;  (* claimed damages amount *)
}.