(* GenericClauses.v - Generic clause kinds for extensibility *)

Require Import Coq.Strings.String.
Require Import kernel.core.basic.Scenario.

(* Trigger enum *)
Inductive trig_type :=
  | AWARENESS
  | DISCOVERY
  | OCCURRENCE.

(* Equality for trig_type *)
Definition trig_eq (t1 t2 : trig_type) : bool :=
  match t1, t2 with
  | AWARENESS, AWARENESS => true
  | DISCOVERY, DISCOVERY => true
  | OCCURRENCE, OCCURRENCE => true
  | _, _ => false
  end.

(* Jurisdiction enum *)
Inductive jurisdiction_type :=
  | GENERAL
  | GDPR_EU
  | CONTRACT_NY.

(* Confidentiality info *)
Record confidentiality_info := mk_conf_info {
  confidentiality_object : string;  (* what is confidential *)
  disclosure_triggers : list trig_type;  (* allowed disclosure triggers *)
}.

(* Indemnity info *)
Record indemnity_info := mk_ind_info {
  indemnity_trigger : string;  (* event triggering indemnity *)
  payment_obligation : nat;  (* amount to pay *)
}.

(* Limitation info *)
Record limitation_info := mk_lim_info {
  limitation_cap : nat;  (* cap on liability *)
}.

(* Jurisdiction profile *)
Record jurisdiction_profile := mk_jur_profile {
  confidentiality_strict : bool;  (* stricter confidentiality rules *)
  limitation_reasonable : bool;  (* allows reasonable limitations *)
}.

(* Get jurisdiction profile *)
Definition get_jurisdiction_profile (j : jurisdiction_type) : jurisdiction_profile :=
  match j with
  | GENERAL => mk_jur_profile false false
  | GDPR_EU => mk_jur_profile true false  (* stricter confidentiality *)
  | CONTRACT_NY => mk_jur_profile false true  (* reasonable limitations *)
  end.

Require Import Coq.Arith.Min.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

(* Generic clause kind inductive *)
Inductive clause_kind :=
| Confidentiality : trig_type -> confidentiality_info -> clause_kind
| Indemnity : indemnity_info -> clause_kind
| Limitation : limitation_info -> clause_kind
| Future : unit -> clause_kind.  (* placeholder for future clauses *)

(* Clause contribution type *)
Record ClauseContribution := {
  breach_contrib : bool;
  obligation_contrib : bool;
  amount_contrib : nat;
  modifier_contrib : nat -> nat;
}.

(* Empty contribution *)
Definition empty_contrib : ClauseContribution := {|
  breach_contrib := false;
  obligation_contrib := false;
  amount_contrib := 0;
  modifier_contrib := fun x => x;
|}.

(* Merge contributions *)
Definition merge_contrib (c1 c2 : ClauseContribution) : ClauseContribution := {|
  breach_contrib := orb c1.(breach_contrib) c2.(breach_contrib);
  obligation_contrib := orb c1.(obligation_contrib) c2.(obligation_contrib);
  amount_contrib := c1.(amount_contrib) + c2.(amount_contrib);
  modifier_contrib := fun x => c1.(modifier_contrib) (c2.(modifier_contrib) x);
|}.

(* Evaluate clause function *)
Definition evaluate_clause (ck : clause_kind) (jur : jurisdiction_type) (s : scenario) : ClauseContribution :=
  match ck with
  | Confidentiality trig conf =>
      let breach := match s.(disclosure_time) with
                    | Some dt => negb (existsb (fun t => trig_eq t trig) conf.(disclosure_triggers))
                    | None => false
                    end in
      {| breach_contrib := breach; obligation_contrib := false; amount_contrib := 0; modifier_contrib := fun x => x |}
  | Indemnity ind =>
      let ob := match s.(breach_by_other_time) with
                | Some _ => true
                | None => false
                end in
      {| breach_contrib := false; obligation_contrib := ob; amount_contrib := ind.(payment_obligation); modifier_contrib := fun x => x |}
  | Limitation lim =>
      let mod_func := fun claimed : nat =>
                        let profile := get_jurisdiction_profile jur in
                        if profile.(limitation_reasonable) then
                          min claimed lim.(limitation_cap)
                        else
                          min claimed lim.(limitation_cap)
      in {| breach_contrib := false; obligation_contrib := false; amount_contrib := 0; modifier_contrib := mod_func |}
  | Future _ => empty_contrib
  end.