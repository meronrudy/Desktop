"""
Integration tests for the neural components pipeline.
"""

import pytest
from legal_bert_extraction import LegalBERTExtractor
from neural_ir_synthesizer import NeuralIRSynthesizer
from catala_wrapper import CatalaWrapper
from neural_realizer import NeuralRealizer
import json


def test_full_pipeline():
    text = "The plaintiff has the right to compensation if the defendant breached the contract."
    scenario = {"breach_occurred": True, "damage_amount": 5000}

    # Extract
    extractor = LegalBERTExtractor()
    entities = extractor.extract_entities(text)
    assert isinstance(entities, list)

    # Synthesize
    synthesizer = NeuralIRSynthesizer()
    ir = synthesizer.generate_ir(text)
    assert isinstance(ir, dict)
    assert "parties" in ir

    # Validate
    wrapper = CatalaWrapper()
    valid = wrapper.validate_ir(ir)
    assert valid  # Assuming it passes

    # Outcome
    outcome = wrapper.compute_outcome(ir, scenario)
    assert isinstance(outcome, dict)

    # Realize
    realizer = NeuralRealizer()
    realized = realizer.realize_text(ir)
    assert isinstance(realized, str)
    assert len(realized) > 0


def test_ir_validation():
    wrapper = CatalaWrapper()
    valid_ir = {"parties": ["a"], "rights": ["b"], "obligations": [], "conditions": []}
    invalid_ir = {"parties": "not list"}
    assert wrapper.validate_ir(valid_ir)
    assert not wrapper.validate_ir(invalid_ir)


if __name__ == "__main__":
    pytest.main([__file__])