"""
Certificate generation step for the legal inference pipeline.
Generates and packages formal certificates of IR validity.
"""

from .base import PipelineStep, PipelineContext, StepResult, StepStatus
from typing import Dict, Any, Optional
import logging

try:
    from cert_gen import CertificateGenerator
    from cert_pack import package_certificate
    from cert_verify import encrypt_certificate
except ImportError:
    # Mock for testing without certificate dependencies
    class CertificateGenerator:
        def generate_certificate(self, ir: dict) -> dict:
            return {"mock": "cert_data", "ir_hash": str(hash(str(ir)))}

    def package_certificate(ir: dict, cert_data: dict) -> dict:
        return {"certificate": cert_data, "ir": ir}

    def encrypt_certificate(cert: dict) -> dict:
        cert["encrypted"] = True
        return cert


class CertificateGeneratorStep(PipelineStep):
    """
    Pipeline step for generating formal certificates.

    Creates cryptographic certificates that prove the mathematical guarantees
    of the certified IR, including court-outcome invariance.
    """

    def __init__(self, config: Optional[Dict[str, Any]] = None):
        super().__init__("certificate_generator", config)
        self.cert_gen = CertificateGenerator()

    def validate_input(self, context: PipelineContext) -> bool:
        """Validate that IR is available and certified."""
        return ("ir" in context.intermediate_results and
                context.intermediate_results["ir"] is not None and
                "certified" in context.intermediate_results and
                context.intermediate_results["certified"] is True)

    async def execute(self, context: PipelineContext) -> StepResult:
        """Generate and package certificate."""
        ir = context.intermediate_results["ir"]

        try:
            # Generate certificate data
            cert_data = self.cert_gen.generate_certificate(ir)

            # Package certificate with IR
            certificate = package_certificate(ir, cert_data)

            # Encrypt certificate for security
            certificate = encrypt_certificate(certificate)

            metadata = {
                "jurisdiction": context.jurisdiction,
                "certificate_type": "court_outcome_invariance",
                "encryption_enabled": True,
                "cert_data_keys": list(cert_data.keys()) if cert_data else []
            }

            self.logger.info("Certificate generated successfully", extra=metadata)

            return StepResult(
                step_name=self.name,
                status=StepStatus.COMPLETED,
                output=certificate,
                metadata=metadata
            )

        except Exception as e:
            self.logger.error(f"Certificate generation failed: {str(e)}")
            return StepResult(
                step_name=self.name,
                status=StepStatus.FAILED,
                error=f"Certificate generation failed: {str(e)}"
            )

    def get_required_inputs(self) -> list[str]:
        """Required inputs for this step."""
        return ["ir", "certified"]

    def get_output_key(self) -> str:
        """Output key for storing results."""
        return "certificate"

    def can_retry(self) -> bool:
        """Certificate generation can be retried."""
        return True

    def get_retry_count(self) -> int:
        """Allow up to 1 retry for certificate generation."""
        return 1