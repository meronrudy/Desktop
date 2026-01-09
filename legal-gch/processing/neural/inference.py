"""
Refactored inference script using the modular pipeline architecture.
Provides backward compatibility while using the new PipelineOrchestrator.
"""

# Import the new modular pipeline
from ..pipeline import PipelineOrchestrator

# Legacy imports for backward compatibility (will be removed in future versions)
try:
    from legal_bert_extraction import LegalBERTExtractor
    from neural_ir_synthesizer import NeuralIRSynthesizer
    from catala_wrapper import CatalaWrapper
    from neural_realizer import NeuralRealizer
    from coq_interface import CoqInterface
    from cert_gen import CertificateGenerator
    from cert_pack import package_certificate
    from cert_verify import encrypt_certificate
except ImportError:
    # Mock imports for testing without dependencies
    pass

import json
import asyncio
import logging
import os
import time
from cachetools import cached, TTLCache
from prometheus_client import Counter, Histogram
from logstash_async.handler import AsynchronousLogstashHandler

# Setup logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Add Logstash handler if LOGSTASH_HOST is set
logstash_host = os.getenv("LOGSTASH_HOST")
if logstash_host:
    logger.addHandler(AsynchronousLogstashHandler(logstash_host, 5000, database_path=None))

# Prometheus metrics
INFERENCE_COUNT = Counter('inference_requests_total', 'Total inference requests', ['status'])
INFERENCE_LATENCY = Histogram('inference_duration_seconds', 'Inference duration', ['step'])
INFERENCE_ERRORS = Counter('inference_errors_total', 'Total inference errors', ['type'])

# Cache for inference results
inference_cache = TTLCache(maxsize=50, ttl=600)  # 10 minutes TTL

# Global orchestrator instance (lazy loaded)
_orchestrator = None

def _get_orchestrator() -> PipelineOrchestrator:
    """Get or create the global pipeline orchestrator."""
    global _orchestrator
    if _orchestrator is None:
        # Configure orchestrator with default settings
        config = {
            "timeout": 1800.0,  # 30 minutes
            "fail_fast": True,
            "max_retries": 3
        }
        _orchestrator = PipelineOrchestrator(config)
    return _orchestrator


@cached(inference_cache, key=lambda text, jurisdiction, scenario: (text, jurisdiction, json.dumps(scenario or {}, sort_keys=True)))
async def main_async(text: str, jurisdiction: str = "GENERAL", scenario: dict = None):
    """
    Async version of the main inference function using the new pipeline architecture.

    Args:
        text: Legal text to process
        jurisdiction: Jurisdiction for processing
        scenario: Scenario parameters for outcome computation

    Returns:
        Dictionary with inference results
    """
    start_time = time.time()
    INFERENCE_COUNT.labels(status='started').inc()
    logger.info("Inference started", extra={'event': 'inference_start', 'jurisdiction': jurisdiction, 'text_length': len(text)})

    try:
        if scenario is None:
            scenario = {"breach_occurred": True, "damage_amount": 5000}

        # Get the pipeline orchestrator
        orchestrator = _get_orchestrator()

        # Execute the pipeline
        result = await orchestrator.execute_pipeline(text, jurisdiction, scenario)

        # Handle pipeline results
        if not result.success:
            INFERENCE_ERRORS.labels(type='pipeline_failed').inc()
            INFERENCE_COUNT.labels(status='pipeline_failed').inc()
            logger.error("Pipeline execution failed", extra={'event': 'pipeline_failed', 'error': result.error})
            return {
                "error": result.error,
                "ir": result.context.intermediate_results.get("ir"),
                "outcome": None,
                "realized_text": None,
                "certified": False,
                "certificate": None
            }

        # Extract final results
        total_time = time.time() - start_time
        INFERENCE_LATENCY.labels(step='total').observe(total_time)

        final_result = {
            "ir": result.context.intermediate_results.get("ir"),
            "outcome": result.context.intermediate_results.get("outcome"),
            "realized_text": result.context.intermediate_results.get("realized_text"),
            "certified": result.context.intermediate_results.get("certified", False),
            "certificate": result.context.intermediate_results.get("certificate")
        }

        logger.info("Inference completed successfully", extra={
            'event': 'inference_success',
            'total_time': total_time,
            'certified': final_result['certified'],
            'step_count': len(result.step_results)
        })

        INFERENCE_COUNT.labels(status='success').inc()
        return final_result

    except Exception as e:
        logger.error("Inference failed", extra={'event': 'inference_error', 'error': str(e)})
        INFERENCE_ERRORS.labels(type='general_error').inc()
        INFERENCE_COUNT.labels(status='error').inc()
        raise


# Backward compatibility synchronous wrapper
def main(text: str, jurisdiction: str = "GENERAL", scenario: dict = None):
    """
    Synchronous wrapper for backward compatibility.
    """
    import time
    try:
        # Try to run async version in new event loop
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        return loop.run_until_complete(main_async(text, jurisdiction, scenario))
    except RuntimeError:
        # If there's already an event loop, create a task
        return asyncio.create_task(main_async(text, jurisdiction, scenario))


if __name__ == "__main__":
    text = "The plaintiff has the right to compensation if the defendant breached the contract."
    result = main(text)
    with open("inference_output.json", "w") as f:
        json.dump(result, f)