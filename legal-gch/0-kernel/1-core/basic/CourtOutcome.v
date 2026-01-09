(* CourtOutcome.v - Definitions for Court Outcome Surface *)

Require Import Coq.Bool.Bool.

(* Remedies enum *)
Inductive remedies :=
  | DAMAGES
  | INJUNCTIVE_RELIEF
  | SPECIFIC_PERFORMANCE
  | NONE.

(* Defenses enum *)
Inductive defenses :=
  | EXCEPTION_APPLIES
  | DEFENSE_PRESERVED
  | DEFENSE_WAIVED.

(* Outcome record *)
Record outcome := mk_outcome {
  obligation_exists : bool;
  breach : bool;
  liability : bool;
  remedy : remedies;
  remedy_amount : nat;  (* effective remedy amount, considering caps *)
  defense : defenses;
}.