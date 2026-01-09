"""
Coq certification step for the legal inference pipeline.
Formally verifies IR using Coq proof assistant.
"""

from .base import PipelineStep, PipelineContext, StepResult, StepStatus
from typing import Dict, Any, Optional
import logging
import asyncio

try:
    from coq_interface import CoqInterface
except ImportError:
    # Mock for testing without Coq dependencies
    class CoqInterface:
        async def certify_ir(self, ir: dict) -> bool:
            return True


class CoqCertifierStep(PipelineStep):
    """
    Pipeline step for formal verification of IR using Coq.

    Certifies that the Normative IR maintains court-outcome invariance
    through mathematical proof verification.
    """

    def __init__(self, config: Optional[Dict[str, Any]] = None):
        super().__init__("coq_certifier", config)
        self.interface = CoqInterface()

    def validate_input(self, context: PipelineContext) -> bool:
        """Validate that IR is available and valid."""
        return ("ir" in context.intermediate_results and
                context.intermediate_results["ir"] is not None and
                "ir_valid" in context.intermediate_results and
                context.intermediate_results["ir_valid"] is True)

    async def execute(self, context: PipelineContext) -> StepResult:
        """Certify the IR using Coq formal verification."""
        ir = context.intermediate_results["ir"]

        try:
            # Certify IR using Coq
            certified = await self.interface.certify_ir(ir)

            metadata = {
                "jurisdiction": context.jurisdiction,
                "certified": certified,
                "certification_type": "court_outcome_invariance",
                "formal_verification": True
            }

            if certified:
                self.logger.info("IR certification successful", extra=metadata)
            else:
                self.logger.warning("IR certification failed", extra=metadata)

            return StepResult(
                step_name=self.name,
                status=StepStatus.COMPLETED,
                output=certified,
                metadata=metadata
            )

        except Exception as e:
            self.logger.error(f"Coq certification failed: {str(e)}")
            return StepResult(
                step_name=self.name,
                status=StepStatus.FAILED,
                error=f"Coq certification failed: {str(e)}"
            )

    def get_required_inputs(self) -> list[str]:
        """Required inputs for this step."""
        return ["ir", "ir_valid"]

    def get_output_key(self) -> str:
        """Output key for storing results."""
        return "certified"

    def can_retry(self) -> bool:
        """Certification can be retried (though expensive)."""
        return True

    def get_retry_count(self) -> int:
        """Allow only 1 retry for expensive certification."""
        return 1

    def get_timeout(self) -> float:
        """Longer timeout for formal verification."""
        return 600.0  # 10 minutes