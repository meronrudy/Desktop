
Require Import kernel.core.definitions.NormativeIR.
Require Import kernel.core.basic.CourtOutcome.
Require Import kernel.core.basic.Scenario.
Require Import kernel.evaluation.Evaluator.
Require Import kernel.evaluation.Invariance.

(* Define the specific IR *)
Definition specific_ir : normative_ir := mk_normative_ir
  (* atoms: [] *)
  []  (* Placeholder: need to map atoms properly *)
  []  (* defs *)
  "general"
.

(* Theorem for this IR *)

Theorem outcome_invariance_for_ir_44136fa3 :
  forall s t1 t2,
    In t1 (renderer specific_ir) ->
    In t2 (renderer specific_ir) ->
    evaluate_opt (parser t1) s = evaluate_opt (parser t2) s.


Proof.

  intros s t1 t2 H1 H2.
  apply renderer_preserves_ir in H1.
  apply renderer_preserves_ir in H2.
  rewrite H1, H2.
  reflexivity.

Qed.
