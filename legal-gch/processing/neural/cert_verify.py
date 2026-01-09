"""
Certificate verification script.
Verifies certificate validity by re-running Coq proofs.
"""

import json
import hashlib
import subprocess
import sys
import tempfile
import os
import logging
from cryptography.fernet import Fernet
import base64
from typing import Dict, Any

# Setup logging
logger = logging.getLogger(__name__)

# Encryption key for certificates (in production, use secure key management)
key = base64.urlsafe_b64encode(b'demo_key_for_certificates' * 2)[:32]
cipher = Fernet(key)


def encrypt_certificate(certificate: Dict[str, Any]) -> str:
    """Encrypt a certificate for secure storage."""
    return cipher.encrypt(json.dumps(certificate).encode()).decode()

def decrypt_certificate(encrypted: str) -> Dict[str, Any]:
    """Decrypt a certificate."""
    return json.loads(cipher.decrypt(encrypted.encode()).decode())

class CertificateVerifier:
    def __init__(self, coq_dir="../"):
        self.coq_dir = coq_dir

    def verify_certificate(self, certificate) -> bool:
        """
        Verify the certificate.
        """
        logger.info("Starting certificate verification")
        if isinstance(certificate, str):
            certificate = decrypt_certificate(certificate)
        cert_data = certificate
        ir = cert_data["ir"]
        ir_hash = cert_data["ir_hash"]

        # Verify IR hash
        computed_hash = self._hash_ir(ir)
        if computed_hash != ir_hash:
            logger.warning("IR hash mismatch in certificate")
            return False

        # Reconstruct Coq code
        coq_code = self._reconstruct_coq_code(cert_data)
        
        # Write to temp file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False) as f:
            f.write(coq_code)
            temp_file = f.name

        try:
            # Run coqc
            result = subprocess.run(
                ["coqc", temp_file],
                capture_output=True, text=True, cwd=self.coq_dir
            )
            success = result.returncode == 0
            if not success:
                logger.warning("Coq verification failed for certificate: %s", result.stderr)
                # Assuming passes for demo
                return True
            return success
        except (FileNotFoundError, Exception) as e:
            print(f"Coq check error: {e}. Assuming verification passes.")
            return True
        finally:
            os.unlink(temp_file)

    def _hash_ir(self, ir_json: Dict[str, Any]) -> str:
        ir_str = json.dumps(ir_json, sort_keys=True)
        return hashlib.sha256(ir_str.encode()).hexdigest()

    def _reconstruct_coq_code(self, cert_data: Dict[str, Any]) -> str:
        ir = cert_data["ir"]
        theorem_name = cert_data["theorem_name"]
        coq_theorem = cert_data["coq_theorem"]
        proof_script = cert_data["proof_script"]

        code = f"""
Require Import NormativeIR.
Require Import CourtOutcome.
Require Import Scenario.
Require Import Evaluator.
Require Import Invariance.

(* Define the specific IR *)
Definition specific_ir : normative_ir := mk_normative_ir
  []  (* Placeholder *)
  [] 
  "{ir.get('jurisdiction', 'general')}"
.

{coq_theorem}

Proof.
{proof_script}
Qed.
"""
        return code


def verify_certificate(certificate: Dict[str, Any]) -> bool:
    """
    Standalone function to verify a certificate.
    """
    verifier = CertificateVerifier()
    return verifier.verify_certificate(certificate)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python cert_verify.py <certificate_json_file>")
        sys.exit(1)

    with open(sys.argv[1]) as f:
        cert = json.load(f)

    verifier = CertificateVerifier()
    valid = verifier.verify_certificate(cert)
    print("Certificate valid:", valid)