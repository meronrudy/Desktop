(* Evaluator.v - Court evaluator function *)

Require Import kernel.core.definitions.NormativeIR.
Require Import kernel.core.basic.CourtOutcome.
Require Import kernel.core.basic.Scenario.
Require Import kernel.core.definitions.GenericClauses.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Min.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

(* Helper to get hours from deadline *)
Definition deadline_hours (d : dead_type) : nat :=
  match d with
  | DURATION h => h
  | FIXED _ => 0  (* simplified, not handling fixed dates *)
  end.

(* Check if obligation exists *)
Definition obligation_exists (a : atom) (s : scenario) : bool :=
  match a.(modality), s.(awareness_time) with
  | MUST, Some _ => true
  | _, _ => false
  end.

(* Check if breach occurred *)
Definition breach_bool (a : atom) (s : scenario) : bool :=
  match s.(awareness_time) with
  | Some at => match s.(notification_time) with
               | Some nt => negb (Nat.leb nt (at + deadline_hours a.(deadline)))
               | None => true
               end
  | None => false
  end.

(* Check confidentiality breach *)
Definition confidentiality_breach (a : atom) (jur : jurisdiction_type) (s : scenario) : bool :=
  match a.(conf_info) with
  | Some conf => match s.(disclosure_time) with
                 | Some dt => negb (existsb (fun t => t = a.(trigger)) conf.(disclosure_triggers))
                 | None => false
                 end
  | None => false
  end.

(* Check indemnity obligation *)
Definition indemnity_obligation (a : atom) (s : scenario) : bool :=
  match a.(ind_info) with
  | Some ind => match s.(breach_by_other_time) with
                | Some _ => true  (* simplified: trigger is breach by other *)
                | None => false
                end
  | None => false
  end.

(* Compute limited damages *)
Definition limited_damages (a : atom) (jur : jurisdiction_type) (claimed : nat) : nat :=
  match a.(lim_info) with
  | Some lim =>
      let profile := get_jurisdiction_profile jur in
      if profile.(limitation_reasonable) then
        min claimed lim.(limitation_cap)
      else
        min claimed lim.(limitation_cap)  (* same for now *)
  | None => claimed
  end.

(* Evaluate single atom *)
Definition evaluate_single (a : atom) (jur : jurisdiction_type) (s : scenario) : outcome :=
  let ob_exists := obligation_exists a s in
  let conf_br := confidentiality_breach a jur s in
  let ind_ob := indemnity_obligation a s in
  let br := if ob_exists then breach_bool a s else conf_br in
  let liab := orb br ind_ob in
  let rem := if liab then if conf_br then INJUNCTIVE_RELIEF else if ind_ob then DAMAGES else DAMAGES else NONE in
  let raw_amt := if ind_ob then match a.(ind_info) with Some ind => ind.(payment_obligation) | None => 0 end else s.(claimed_damages) in
  let amt := limited_damages a jur raw_amt in
  let def := if br then DEFENSE_WAIVED else DEFENSE_PRESERVED in
  mk_outcome ob_exists br liab rem amt def.

(* Evaluate IR (simplified: take first atom) *)
Definition evaluate (ir : normative_ir) (s : scenario) : outcome :=
  match ir.(atoms) with
  | nil => mk_outcome false false false NONE 0 DEFENSE_PRESERVED
  | a :: _ => evaluate_single a ir.(jurisdiction) s
  end.