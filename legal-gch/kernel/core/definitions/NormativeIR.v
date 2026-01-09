(* NormativeIR.v - Definitions for Normative Intermediate Representation *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import kernel.core.definitions.GenericClauses.

(* Modality enum *)
Inductive mod_type :=
  | MUST
  | MUST_NOT
  | MAY
  | SHOULD.

(* Exceptions enum - simplified, add more as needed *)
Inductive exception :=
  | UNLESS_PROHIBITED_BY_LAW.

(* Deadline type *)
Inductive dead_type :=
  | DURATION (hours : nat)
  | FIXED (date : string).

(* Evidence type *)
Definition evidence := (string * (nat * nat))%type.  (* doc, span *)

(* Atom record *)
Record atom := mk_atom {
  id : string;
  actor : string;
  modality : mod_type;
  action : string;
  object : string;
  recipient : string;
  trigger : trig_type;
  deadline : dead_type;
  exceptions : list exception;
  scope_defined_terms : list string;
  evidence_list : list evidence;
  conf_info : option confidentiality_info;
  clauses : list clause_kind;
}.

(* Definitions *)
Definition definitions := list (string * string).  (* term * definition *)

(* Normative IR *)
Record normative_ir := mk_normative_ir {
  atoms : list atom;
  defs : definitions;
  jurisdiction : jurisdiction_type;
}.