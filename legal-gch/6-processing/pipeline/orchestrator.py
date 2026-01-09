"""
Pipeline orchestrator for managing the execution of inference pipeline steps.
"""

import asyncio
from typing import List, Dict, Any, Optional, Callable
from dataclasses import dataclass
from enum import Enum
import logging
import time

from .steps.base import PipelineContext, PipelineStep, StepResult, StepStatus, PipelineError
from .steps.entity_extractor import EntityExtractorStep
from .steps.ir_synthesizer import IRSynthesizerStep
from .steps.catala_validator import CatalaValidatorStep
from .steps.outcome_computer import OutcomeComputerStep
from .steps.text_realizer import TextRealizerStep
from .steps.coq_certifier import CoqCertifierStep
from .steps.certificate_generator import CertificateGeneratorStep

logger = logging.getLogger(__name__)


class PipelineExecutionError(PipelineError):
    """Error during pipeline execution."""
    pass


class PipelineTimeoutError(PipelineExecutionError):
    """Pipeline execution timed out."""
    pass


@dataclass
class PipelineResult:
    """Result of a complete pipeline execution."""
    success: bool
    context: PipelineContext
    step_results: List[StepResult]
    total_execution_time: float
    error: Optional[str] = None


class PipelineOrchestrator:
    """
    Orchestrates the execution of inference pipeline steps.

    Manages dependencies, error handling, retries, and parallel execution
    where possible. Provides configurable pipeline composition.
    """

    def __init__(self, config: Optional[Dict[str, Any]] = None):
        self.config = config or {}
        self.logger = logging.getLogger(f"{__name__}.{self.__class__.__name__}")

        # Initialize default pipeline steps
        self._init_default_pipeline()

        # Execution settings
        self.max_retries = self.config.get("max_retries", 3)
        self.timeout = self.config.get("timeout", 1800.0)  # 30 minutes
        self.fail_fast = self.config.get("fail_fast", True)

    def _init_default_pipeline(self):
        """Initialize the default pipeline steps in execution order."""
        self.pipeline_steps = [
            EntityExtractorStep(self.config.get("entity_extractor", {})),
            IRSynthesizerStep(self.config.get("ir_synthesizer", {})),
            CatalaValidatorStep(self.config.get("catala_validator", {})),
            OutcomeComputerStep(self.config.get("outcome_computer", {})),
            TextRealizerStep(self.config.get("text_realizer", {})),
            CoqCertifierStep(self.config.get("coq_certifier", {})),
            CertificateGeneratorStep(self.config.get("certificate_generator", {}))
        ]

    def add_step(self, step: PipelineStep, position: Optional[int] = None):
        """
        Add a custom pipeline step.

        Args:
            step: The pipeline step to add
            position: Position to insert (None for end)
        """
        if position is None:
            self.pipeline_steps.append(step)
        else:
            self.pipeline_steps.insert(position, step)

    def remove_step(self, step_name: str):
        """
        Remove a pipeline step by name.

        Args:
            step_name: Name of the step to remove
        """
        self.pipeline_steps = [s for s in self.pipeline_steps if s.name != step_name]

    async def execute_pipeline(
        self,
        input_text: str,
        jurisdiction: str = "GENERAL",
        scenario: Optional[Dict[str, Any]] = None,
        custom_config: Optional[Dict[str, Any]] = None
    ) -> PipelineResult:
        """
        Execute the complete inference pipeline.

        Args:
            input_text: Legal text to process
            jurisdiction: Jurisdiction for processing
            scenario: Scenario parameters
            custom_config: Additional configuration

        Returns:
            PipelineResult with execution outcomes
        """
        start_time = time.time()
        context = PipelineContext(
            input_text=input_text,
            jurisdiction=jurisdiction,
            scenario=scenario,
            config={**self.config, **(custom_config or {})}
        )

        step_results = []
        error_message = None

        try:
            for step in self.pipeline_steps:
                self.logger.info(f"Executing step: {step.name}")

                # Execute step with error handling
                result = await self._execute_step_with_retries(step, context)
                step_results.append(result)

                # Handle step failure
                if result.status == StepStatus.FAILED:
                    if self.fail_fast:
                        error_message = f"Step {step.name} failed: {result.error}"
                        break
                    else:
                        self.logger.warning(f"Step {step.name} failed, continuing: {result.error}")

                # Check for timeout
                if time.time() - start_time > self.timeout:
                    raise PipelineTimeoutError(f"Pipeline execution timed out after {self.timeout}s")

            success = error_message is None and all(
                r.status in [StepStatus.COMPLETED, StepStatus.SKIPPED]
                for r in step_results
            )

        except Exception as e:
            success = False
            error_message = f"Pipeline execution failed: {str(e)}"
            self.logger.error(error_message, exc_info=True)

        total_time = time.time() - start_time

        return PipelineResult(
            success=success,
            context=context,
            step_results=step_results,
            total_execution_time=total_time,
            error=error_message
        )

    async def _execute_step_with_retries(self, step: PipelineStep, context: PipelineContext) -> StepResult:
        """
        Execute a step with retry logic.

        Args:
            step: The pipeline step to execute
            context: Current pipeline context

        Returns:
            StepResult from execution
        """
        if not step.can_retry():
            return await step.run_with_error_handling(context)

        for attempt in range(step.get_retry_count() + 1):
            result = await step.run_with_error_handling(context)

            if result.status == StepStatus.COMPLETED:
                return result

            if attempt < step.get_retry_count():
                wait_time = min(2 ** attempt, 30)  # Exponential backoff, max 30s
                self.logger.warning(f"Step {step.name} failed (attempt {attempt + 1}), retrying in {wait_time}s")
                await asyncio.sleep(wait_time)

        return result

    def get_pipeline_summary(self) -> Dict[str, Any]:
        """Get a summary of the current pipeline configuration."""
        return {
            "steps": [step.name for step in self.pipeline_steps],
            "total_steps": len(self.pipeline_steps),
            "config": self.config
        }

    async def validate_pipeline(self) -> bool:
        """
        Validate that the pipeline is properly configured.

        Returns:
            True if pipeline is valid, False otherwise
        """
        if not self.pipeline_steps:
            self.logger.error("Pipeline has no steps")
            return False

        # Check for duplicate step names
        step_names = [s.name for s in self.pipeline_steps]
        if len(step_names) != len(set(step_names)):
            self.logger.error("Pipeline has duplicate step names")
            return False

        # Validate step dependencies
        for i, step in enumerate(self.pipeline_steps):
            required_inputs = set(step.get_required_inputs())
            available_outputs = set()

            # Check what outputs are available from previous steps
            for prev_step in self.pipeline_steps[:i]:
                available_outputs.add(prev_step.get_output_key())

            missing_inputs = required_inputs - available_outputs
            if missing_inputs:
                self.logger.error(f"Step {step.name} missing required inputs: {missing_inputs}")
                return False

        return True