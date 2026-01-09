import json
import pytest
import os
from cert_gen import CertificateGenerator
from cert_verify import CertificateVerifier

@pytest.fixture
def sample_ir():
    return {
        "jurisdiction": "general",
        "atoms": [],
        "defs": []
    }

@pytest.fixture
def modified_ir():
    return {
        "jurisdiction": "modified",
        "atoms": [],
        "defs": []
    }

@pytest.fixture
def invalid_ir():
    return {
        "jurisdiction": "general",
        "atoms": "invalid"
    }

@pytest.fixture
def generator():
    return CertificateGenerator()

@pytest.fixture
def verifier():
    return CertificateVerifier()

def test_generate_and_verify_immediately(generator, verifier, sample_ir):
    cert = generator.generate_certificate(sample_ir)
    assert verifier.verify_certificate(cert) == True

def test_verify_after_ir_modification(generator, verifier, sample_ir, modified_ir):
    cert = generator.generate_certificate(sample_ir)
    # Modify the IR in the cert to simulate change
    cert["ir"] = modified_ir
    assert verifier.verify_certificate(cert) == False
    # Re-generate
    new_cert = generator.generate_certificate(modified_ir)
    assert verifier.verify_certificate(new_cert) == True

def test_hash_integrity(generator, sample_ir):
    cert = generator.generate_certificate(sample_ir)
    computed_hash = generator._hash_ir(sample_ir)
    assert cert["ir_hash"] == computed_hash

def test_re_generation(generator, verifier, sample_ir):
    cert1 = generator.generate_certificate(sample_ir)
    cert2 = generator.generate_certificate(sample_ir)
    # Should be identical except for generated_at
    assert cert1["ir_hash"] == cert2["ir_hash"]
    assert cert1["theorem_name"] == cert2["theorem_name"]
    assert verifier.verify_certificate(cert1) == True
    assert verifier.verify_certificate(cert2) == True

def test_tampered_certificate(verifier):
    with open("cert_tampered.json") as f:
        cert = json.load(f)
    assert verifier.verify_certificate(cert) == False

def test_invalid_ir_generation(generator, invalid_ir):
    # Should not raise, but in demo mode it might
    cert = generator.generate_certificate(invalid_ir)
    # Since demo assumes pass, but hash is computed
    assert "ir_hash" in cert

def test_multi_version_certificate(verifier):
    with open("cert_multi_version.json") as f:
        cert = json.load(f)
    # Since version is different, but code doesn't check version, it verifies
    # In real, might check version compatibility
    assert verifier.verify_certificate(cert) == True

def test_simulated_coq_version_update(verifier, sample_ir, generator):
    cert = generator.generate_certificate(sample_ir)
    # Simulate Coq version update
    cert["coq_version"] = "8.18"
    # Still verifies as code doesn't check coq_version
    assert verifier.verify_certificate(cert) == True

def test_edge_case_empty_ir(generator, verifier):
    empty_ir = {}
    cert = generator.generate_certificate(empty_ir)
    assert verifier.verify_certificate(cert) == True

if __name__ == "__main__":
    pytest.main([__file__])