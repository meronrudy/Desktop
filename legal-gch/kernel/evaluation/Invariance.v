(* Invariance.v - Proof of outcome invariance *)

Require Import kernel.core.definitions.NormativeIR.
Require Import kernel.core.basic.CourtOutcome.
Require Import kernel.core.basic.Scenario.
Require Import kernel.evaluation.Evaluator.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

(* Equivalence on IRs *)
Definition ir_equiv (ir1 ir2 : normative_ir) : Prop :=
  ir1.(atoms) = ir2.(atoms) /\
  ir1.(defs) = ir2.(defs) /\
  ir1.(jurisdiction) = ir2.(jurisdiction).

(* Theorem: equivalent IRs produce identical outcomes *)
Theorem evaluate_ir_equiv :
  forall ir1 ir2 s,
    ir_equiv ir1 ir2 ->
    evaluate ir1 s = evaluate ir2 s.
Proof.
  intros ir1 ir2 s [Hatoms [Hdefs Hjur]].
  unfold evaluate.
  rewrite Hatoms.
  reflexivity.
Qed.

(* Abstract renderer and parser *)
Parameter renderer : normative_ir -> list string.
Parameter parser : string -> option normative_ir.

(* Axiom: renderer preserves IR *)
Axiom renderer_preserves_ir :
  forall ir t, In t (renderer ir) -> parser t = Some ir.

(* Evaluate optional IR *)
Definition evaluate_opt (oir : option normative_ir) (s : scenario) : outcome :=
  match oir with
  | Some ir => evaluate ir s
  | None => mk_outcome false false false NONE 0 DEFENSE_PRESERVED
  end.

(* Theorem: invariance for renderer outputs *)
Theorem outcome_invariance :
  forall ir s t1 t2,
    In t1 (renderer ir) ->
    In t2 (renderer ir) ->
    evaluate_opt (parser t1) s = evaluate_opt (parser t2) s.
Proof.
  intros ir s t1 t2 H1 H2.
  apply renderer_preserves_ir in H1.
  apply renderer_preserves_ir in H2.
  rewrite H1, H2.
  reflexivity.
Qed.
(* Theorem: confidentiality breach determinism *)
Theorem confidentiality_breach_deterministic :
  forall a s1 s2,
    s1.(disclosure_time) = s2.(disclosure_time) ->
    confidentiality_breach a s1 = confidentiality_breach a s2.
Proof.
  intros a s1 s2 Hdiscl.
  unfold confidentiality_breach.
  destruct (conf_info a); auto.
  destruct (disclosure_time s1); destruct (disclosure_time s2); auto; congruence.
Qed.

(* Theorem: indemnity obligation determinism *)
Theorem indemnity_obligation_deterministic :
  forall a s1 s2,
    s1.(breach_by_other_time) = s2.(breach_by_other_time) ->
    indemnity_obligation a s1 = indemnity_obligation a s2.
Proof.
  intros a s1 s2 Hbreach.
  unfold indemnity_obligation.
  destruct (ind_info a); auto.
  destruct (breach_by_other_time s1); destruct (breach_by_other_time s2); auto; congruence.
Qed.

(* Theorem: limited damages is min *)
Theorem limited_damages_correct :
  forall a claimed,
    limited_damages a claimed = min claimed (match lim_info a with Some lim => lim.(limitation_cap) | None => claimed end).
Proof.
  intros a claimed.
  unfold limited_damages.
  destruct (lim_info a); auto.
  rewrite Nat.min_comm. reflexivity.
Qed.
