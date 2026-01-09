"""
Entity extraction step for the legal inference pipeline.
Extracts legal entities and intents from input text using LegalBERT.
"""

from .base import PipelineStep, PipelineContext, StepResult, StepStatus
from typing import Dict, Any, Optional
import logging
import os

try:
    from legal_bert_extraction import LegalBERTExtractor
except ImportError:
    # Mock for testing without neural dependencies
    class LegalBERTExtractor:
        def __init__(self, model_path: str):
            self.model_path = model_path

        def extract_entities_with_jurisdiction(self, text: str, jurisdiction: str) -> list:
            return [{"mock": "entity", "jurisdiction": jurisdiction}]


class EntityExtractorStep(PipelineStep):
    """
    Pipeline step for extracting legal entities from input text.

    Uses LegalBERT fine-tuned model to identify legal intents, entities,
    and jurisdiction-specific legal concepts.
    """

    def __init__(self, config: Optional[Dict[str, Any]] = None):
        super().__init__("entity_extractor", config)
        self.model_path = self.config.get("model_path", "./models/legal_bert_finetuned_extended")
        self.extractor = None

    def validate_input(self, context: PipelineContext) -> bool:
        """Validate that input text is available."""
        return bool(context.input_text and context.input_text.strip())

    async def execute(self, context: PipelineContext) -> StepResult:
        """Extract entities from the input text."""
        try:
            # Lazy load the extractor
            if self.extractor is None:
                self.extractor = LegalBERTExtractor(self.model_path)

            # Extract entities with jurisdiction context
            entities = self.extractor.extract_entities_with_jurisdiction(
                context.input_text,
                context.jurisdiction
            )

            metadata = {
                "entity_count": len(entities),
                "jurisdiction": context.jurisdiction,
                "model_path": self.model_path
            }

            self.logger.info(f"Extracted {len(entities)} entities", extra=metadata)

            return StepResult(
                step_name=self.name,
                status=StepStatus.COMPLETED,
                output=entities,
                metadata=metadata
            )

        except Exception as e:
            self.logger.error(f"Entity extraction failed: {str(e)}")
            return StepResult(
                step_name=self.name,
                status=StepStatus.FAILED,
                error=f"Entity extraction failed: {str(e)}"
            )

    def get_required_inputs(self) -> list[str]:
        """Required inputs for this step."""
        return ["input_text", "jurisdiction"]

    def get_output_key(self) -> str:
        """Output key for storing results."""
        return "entities"

    def can_retry(self) -> bool:
        """Entity extraction can be retried."""
        return True

    def get_retry_count(self) -> int:
        """Allow up to 2 retries."""
        return 2