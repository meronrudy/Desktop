"""
IR synthesis step for the legal inference pipeline.
Generates Normative Intermediate Representation from extracted entities.
"""

from .base import PipelineStep, PipelineContext, StepResult, StepStatus
from typing import Dict, Any, Optional
import logging

try:
    from neural_ir_synthesizer import NeuralIRSynthesizer
except ImportError:
    # Mock for testing without neural dependencies
    class NeuralIRSynthesizer:
        def __init__(self, model_path: str):
            self.model_path = model_path

        def generate_ir(self, text: str, jurisdiction: str) -> dict:
            return {"mock": "ir", "jurisdiction": jurisdiction, "text_length": len(text)}


class IRSynthesizerStep(PipelineStep):
    """
    Pipeline step for synthesizing Normative IR from input text.

    Uses a neural synthesizer model to convert natural language legal text
    into structured Normative Intermediate Representation.
    """

    def __init__(self, config: Optional[Dict[str, Any]] = None):
        super().__init__("ir_synthesizer", config)
        self.model_path = self.config.get("model_path", "./models/ir_synthesizer_finetuned_extended")
        self.synthesizer = None

    def validate_input(self, context: PipelineContext) -> bool:
        """Validate that input text and jurisdiction are available."""
        return (bool(context.input_text and context.input_text.strip()) and
                bool(context.jurisdiction))

    async def execute(self, context: PipelineContext) -> StepResult:
        """Synthesize IR from the input text."""
        try:
            # Lazy load the synthesizer
            if self.synthesizer is None:
                self.synthesizer = NeuralIRSynthesizer(self.model_path)

            # Generate IR with jurisdiction context
            ir = self.synthesizer.generate_ir(context.input_text, context.jurisdiction)

            # Validate basic IR structure
            if not isinstance(ir, dict):
                raise ValueError("IR synthesis must return a dictionary")

            metadata = {
                "jurisdiction": context.jurisdiction,
                "model_path": self.model_path,
                "ir_keys": list(ir.keys()) if ir else [],
                "input_length": len(context.input_text)
            }

            self.logger.info("IR synthesized successfully", extra=metadata)

            return StepResult(
                step_name=self.name,
                status=StepStatus.COMPLETED,
                output=ir,
                metadata=metadata
            )

        except Exception as e:
            self.logger.error(f"IR synthesis failed: {str(e)}")
            return StepResult(
                step_name=self.name,
                status=StepStatus.FAILED,
                error=f"IR synthesis failed: {str(e)}"
            )

    def get_required_inputs(self) -> list[str]:
        """Required inputs for this step."""
        return ["input_text", "jurisdiction"]

    def get_output_key(self) -> str:
        """Output key for storing results."""
        return "ir"

    def can_retry(self) -> bool:
        """IR synthesis can be retried."""
        return True

    def get_retry_count(self) -> int:
        """Allow up to 2 retries."""
        return 2