"""
Outcome computation step for the legal inference pipeline.
Computes court outcomes from validated IR and scenario parameters.
"""

from .base import PipelineStep, PipelineContext, StepResult, StepStatus
from typing import Dict, Any, Optional
import logging
import asyncio

try:
    from catala_wrapper import CatalaWrapper
except ImportError:
    # Mock for testing without Catala dependencies
    class CatalaWrapper:
        async def compute_outcome(self, ir: dict, scenario: dict) -> dict:
            return {"mock": "outcome", "breach": scenario.get("breach_occurred", False)}


class OutcomeComputerStep(PipelineStep):
    """
    Pipeline step for computing court outcomes from IR and scenario.

    Uses Catala engine to evaluate legal outcomes based on the Normative IR
    and provided scenario parameters.
    """

    def __init__(self, config: Optional[Dict[str, Any]] = None):
        super().__init__("outcome_computer", config)
        self.wrapper = CatalaWrapper()

    def validate_input(self, context: PipelineContext) -> bool:
        """Validate that IR is available and valid."""
        return ("ir" in context.intermediate_results and
                context.intermediate_results["ir"] is not None and
                "ir_valid" in context.intermediate_results and
                context.intermediate_results["ir_valid"] is True)

    async def execute(self, context: PipelineContext) -> StepResult:
        """Compute outcome from IR and scenario."""
        ir = context.intermediate_results["ir"]
        scenario = context.scenario or {}

        try:
            # Compute outcome using Catala
            outcome = await self.wrapper.compute_outcome(ir, scenario)

            # Validate outcome structure
            if not isinstance(outcome, dict):
                raise ValueError("Outcome computation must return a dictionary")

            metadata = {
                "jurisdiction": context.jurisdiction,
                "scenario_keys": list(scenario.keys()) if scenario else [],
                "outcome_keys": list(outcome.keys()) if outcome else []
            }

            self.logger.info("Outcome computed successfully", extra=metadata)

            return StepResult(
                step_name=self.name,
                status=StepStatus.COMPLETED,
                output=outcome,
                metadata=metadata
            )

        except Exception as e:
            self.logger.error(f"Outcome computation failed: {str(e)}")
            return StepResult(
                step_name=self.name,
                status=StepStatus.FAILED,
                error=f"Outcome computation failed: {str(e)}"
            )

    def get_required_inputs(self) -> list[str]:
        """Required inputs for this step."""
        return ["ir", "ir_valid", "scenario"]

    def get_output_key(self) -> str:
        """Output key for storing results."""
        return "outcome"

    def can_retry(self) -> bool:
        """Outcome computation can be retried."""
        return True

    def get_retry_count(self) -> int:
        """Allow up to 1 retry for computation."""
        return 1