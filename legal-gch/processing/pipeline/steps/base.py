"""
Base classes and interfaces for pipeline steps.
"""

from abc import ABC, abstractmethod
from typing import Dict, Any, Optional, Tuple
from dataclasses import dataclass
from enum import Enum
import time
import logging

logger = logging.getLogger(__name__)


class StepStatus(Enum):
    """Status of a pipeline step execution."""
    PENDING = "pending"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    SKIPPED = "skipped"


class PipelineError(Exception):
    """Base exception for pipeline errors."""
    pass


class StepExecutionError(PipelineError):
    """Error during step execution."""
    pass


class StepValidationError(PipelineError):
    """Error during step input validation."""
    pass


@dataclass
class StepResult:
    """Result of a pipeline step execution."""
    step_name: str
    status: StepStatus
    output: Optional[Any] = None
    error: Optional[str] = None
    execution_time: float = 0.0
    metadata: Optional[Dict[str, Any]] = None


@dataclass
class PipelineContext:
    """Context passed between pipeline steps."""
    input_text: str
    jurisdiction: str
    scenario: Optional[Dict[str, Any]] = None
    intermediate_results: Dict[str, Any] = None
    config: Dict[str, Any] = None

    def __post_init__(self):
        if self.intermediate_results is None:
            self.intermediate_results = {}
        if self.config is None:
            self.config = {}


class PipelineStep(ABC):
    """
    Abstract base class for all pipeline steps.

    Each step should be responsible for a single, well-defined operation
    in the inference pipeline.
    """

    def __init__(self, name: str, config: Optional[Dict[str, Any]] = None):
        self.name = name
        self.config = config or {}
        self.logger = logging.getLogger(f"{__name__}.{name}")

    @abstractmethod
    def validate_input(self, context: PipelineContext) -> bool:
        """
        Validate that the step can run with the given context.

        Args:
            context: The pipeline context containing inputs and state

        Returns:
            True if the step can proceed, False otherwise
        """
        pass

    @abstractmethod
    async def execute(self, context: PipelineContext) -> StepResult:
        """
        Execute the step's logic.

        Args:
            context: The pipeline context

        Returns:
            StepResult containing the execution outcome
        """
        pass

    @abstractmethod
    def get_required_inputs(self) -> list[str]:
        """
        Get the names of inputs required from the context.

        Returns:
            List of required input keys
        """
        pass

    @abstractmethod
    def get_output_key(self) -> str:
        """
        Get the key under which this step's output will be stored.

        Returns:
            Output key for storing results
        """
        pass

    def can_retry(self) -> bool:
        """Whether this step supports retry on failure."""
        return False

    def get_retry_count(self) -> int:
        """Maximum number of retry attempts."""
        return 0

    def get_timeout(self) -> float:
        """Timeout in seconds for step execution."""
        return 300.0  # 5 minutes default

    async def run_with_error_handling(self, context: PipelineContext) -> StepResult:
        """
        Run the step with built-in error handling and timing.

        Args:
            context: Pipeline context

        Returns:
            StepResult with execution details
        """
        start_time = time.time()

        try:
            # Validate inputs
            if not self.validate_input(context):
                return StepResult(
                    step_name=self.name,
                    status=StepStatus.FAILED,
                    error="Input validation failed",
                    execution_time=time.time() - start_time
                )

            # Execute step
            result = await self.execute(context)
            result.execution_time = time.time() - start_time

            if result.status == StepStatus.COMPLETED and result.output is not None:
                # Store output in context
                context.intermediate_results[self.get_output_key()] = result.output

            return result

        except Exception as e:
            self.logger.error(f"Step {self.name} failed: {str(e)}", exc_info=True)
            return StepResult(
                step_name=self.name,
                status=StepStatus.FAILED,
                error=str(e),
                execution_time=time.time() - start_time
            )