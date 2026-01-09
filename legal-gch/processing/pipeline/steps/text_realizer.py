"""
Text realization step for the legal inference pipeline.
Converts validated IR back to natural language legal text.
"""

from .base import PipelineStep, PipelineContext, StepResult, StepStatus
from typing import Dict, Any, Optional
import logging

try:
    from neural_realizer import NeuralRealizer
except ImportError:
    # Mock for testing without neural dependencies
    class NeuralRealizer:
        def __init__(self, model_path: str):
            self.model_path = model_path

        def realize_text(self, ir: dict, template_key: str) -> str:
            return f"Mock realized text for {template_key} with IR keys: {list(ir.keys())}"


class TextRealizerStep(PipelineStep):
    """
    Pipeline step for realizing natural language text from Normative IR.

    Uses neural realizers to convert structured IR back into readable legal text,
    choosing appropriate templates based on legal clause types.
    """

    def __init__(self, config: Optional[Dict[str, Any]] = None):
        super().__init__("text_realizer", config)
        self.model_path = self.config.get("model_path", "./models/realizer_finetuned_extended")
        self.realizer = None

    def validate_input(self, context: PipelineContext) -> bool:
        """Validate that IR is available."""
        return ("ir" in context.intermediate_results and
                context.intermediate_results["ir"] is not None)

    async def execute(self, context: PipelineContext) -> StepResult:
        """Realize text from the IR."""
        ir = context.intermediate_results["ir"]

        try:
            # Lazy load the realizer
            if self.realizer is None:
                self.realizer = NeuralRealizer(self.model_path)

            # Choose template based on IR content
            template_key = self._select_template(ir)

            # Realize text using the selected template
            realized_text = self.realizer.realize_text(ir, template_key)

            metadata = {
                "jurisdiction": context.jurisdiction,
                "template_key": template_key,
                "model_path": self.model_path,
                "output_length": len(realized_text)
            }

            self.logger.info("Text realized successfully", extra=metadata)

            return StepResult(
                step_name=self.name,
                status=StepStatus.COMPLETED,
                output=realized_text,
                metadata=metadata
            )

        except Exception as e:
            self.logger.error(f"Text realization failed: {str(e)}")
            return StepResult(
                step_name=self.name,
                status=StepStatus.FAILED,
                error=f"Text realization failed: {str(e)}"
            )

    def _select_template(self, ir: dict) -> str:
        """
        Select appropriate template based on IR content.

        Args:
            ir: The Normative IR dictionary

        Returns:
            Template key for realization
        """
        rights = ir.get("rights", [])

        if "confidentiality" in rights:
            return "confidentiality_judgment"
        elif "indemnification" in rights or "indemnity" in rights:
            return "indemnity_judgment"
        elif "liability_limitation" in rights:
            return "limitation_judgment"
        else:
            return "judgment"  # Default template

    def get_required_inputs(self) -> list[str]:
        """Required inputs for this step."""
        return ["ir"]

    def get_output_key(self) -> str:
        """Output key for storing results."""
        return "realized_text"

    def can_retry(self) -> bool:
        """Text realization can be retried."""
        return True

    def get_retry_count(self) -> int:
        """Allow up to 2 retries."""
        return 2