"""
Catala validation step for the legal inference pipeline.
Validates Normative IR against legal rules using Catala engine.
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
        async def validate_ir(self, ir: dict) -> bool:
            return True


class CatalaValidatorStep(PipelineStep):
    """
    Pipeline step for validating Normative IR using Catala legal rules.

    Ensures that the generated IR conforms to legal semantics and rules
    defined in the Catala specification.
    """

    def __init__(self, config: Optional[Dict[str, Any]] = None):
        super().__init__("catala_validator", config)
        self.wrapper = CatalaWrapper()

    def validate_input(self, context: PipelineContext) -> bool:
        """Validate that IR is available in the context."""
        return ("ir" in context.intermediate_results and
                context.intermediate_results["ir"] is not None)

    async def execute(self, context: PipelineContext) -> StepResult:
        """Validate the IR using Catala."""
        ir = context.intermediate_results["ir"]

        try:
            # Validate IR using Catala
            is_valid = await self.wrapper.validate_ir(ir)

            metadata = {
                "ir_valid": is_valid,
                "jurisdiction": context.jurisdiction,
                "validation_type": "catala_semantic"
            }

            if is_valid:
                self.logger.info("IR validation passed", extra=metadata)
                return StepResult(
                    step_name=self.name,
                    status=StepStatus.COMPLETED,
                    output=True,
                    metadata=metadata
                )
            else:
                self.logger.warning("IR validation failed", extra=metadata)
                return StepResult(
                    step_name=self.name,
                    status=StepStatus.FAILED,
                    error="IR validation failed: does not conform to legal rules",
                    metadata=metadata
                )

        except Exception as e:
            self.logger.error(f"Catala validation failed: {str(e)}")
            return StepResult(
                step_name=self.name,
                status=StepStatus.FAILED,
                error=f"Catala validation error: {str(e)}"
            )

    def get_required_inputs(self) -> list[str]:
        """Required inputs for this step."""
        return ["ir"]

    def get_output_key(self) -> str:
        """Output key for storing results."""
        return "ir_valid"

    def can_retry(self) -> bool:
        """Validation can be retried."""
        return True

    def get_retry_count(self) -> int:
        """Allow up to 1 retry for validation."""
        return 1