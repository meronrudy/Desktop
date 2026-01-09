"""
Script to generate synthetic datasets for fine-tuning neural components on new domains.
Includes confidentiality, indemnity, limitation of liability clauses, and jurisdiction-specific examples.
"""

import json
from datasets import Dataset
import random

def generate_ner_dataset():
    """
    Generate NER dataset for Legal-BERT extractor.
    Includes new clause types and jurisdiction entities.
    """
    samples = []

    # Confidentiality examples
    confidentiality_texts = [
        "The Recipient shall maintain confidentiality of all trade secrets under GDPR_EU regulations.",
        "Confidential information must not be disclosed without written consent in CONTRACT_NY jurisdiction.",
        "Party A agrees to keep proprietary data confidential pursuant to EU GDPR.",
        "Information marked as confidential shall remain undisclosed in New York contract law."
    ]

    for text in confidentiality_texts:
        # Simple tokenization and labeling (simplified)
        tokens = text.split()
        ner_tags = []
        for token in tokens:
            if token in ["Confidentiality", "confidential"]:
                ner_tags.append("B-CONFIDENTIALITY")
            elif token in ["GDPR_EU", "GDPR"]:
                ner_tags.append("B-JURISDICTION")
            elif token in ["CONTRACT_NY", "New York"]:
                ner_tags.append("B-JURISDICTION")
            elif token in ["Recipient", "Party A"]:
                ner_tags.append("B-PARTY")
            else:
                ner_tags.append("O")
        samples.append({"tokens": tokens, "ner_tags": ner_tags})

    # Indemnity examples
    indemnity_texts = [
        "The Seller shall indemnify Buyer for any losses arising from product defects under CONTRACT_NY.",
        "Indemnitor agrees to compensate Indemnitee for third-party claims in GDPR_EU context.",
        "Party B will indemnify Party A against intellectual property infringement claims."
    ]

    for text in indemnity_texts:
        tokens = text.split()
        ner_tags = []
        for token in tokens:
            if token in ["indemnify", "Indemnitor"]:
                ner_tags.append("B-INDEMNITY")
            elif token in ["GDPR_EU"]:
                ner_tags.append("B-JURISDICTION")
            elif token in ["CONTRACT_NY"]:
                ner_tags.append("B-JURISDICTION")
            elif token in ["Seller", "Buyer", "Party A", "Party B"]:
                ner_tags.append("B-PARTY")
            else:
                ner_tags.append("O")
        samples.append({"tokens": tokens, "ner_tags": ner_tags})

    # Limitation of liability examples
    limitation_texts = [
        "Liability is limited to the contract price under GDPR_EU regulations.",
        "The total liability shall not exceed $100,000 pursuant to CONTRACT_NY law.",
        "Limitation of liability clause caps damages at twice the fees paid."
    ]

    for text in limitation_texts:
        tokens = text.split()
        ner_tags = []
        for token in tokens:
            if token in ["Liability", "limitation"]:
                ner_tags.append("B-LIMITATION")
            elif token in ["GDPR_EU"]:
                ner_tags.append("B-JURISDICTION")
            elif token in ["CONTRACT_NY"]:
                ner_tags.append("B-JURISDICTION")
            else:
                ner_tags.append("O")
        samples.append({"tokens": tokens, "ner_tags": ner_tags})

    # Extend with jurisdiction-specific examples
    jurisdiction_texts = [
        "Under GDPR_EU, data processing requires explicit consent.",
        "CONTRACT_NY governs the interpretation of this agreement.",
        "Jurisdiction is established in EU for data protection matters.",
        "New York law applies to this contractual arrangement."
    ]

    for text in jurisdiction_texts:
        tokens = text.split()
        ner_tags = []
        for token in tokens:
            if token in ["GDPR_EU", "EU"]:
                ner_tags.append("B-JURISDICTION")
            elif token in ["CONTRACT_NY", "New York"]:
                ner_tags.append("B-JURISDICTION")
            else:
                ner_tags.append("O")
        samples.append({"tokens": tokens, "ner_tags": ner_tags})

    return Dataset.from_list(samples)

def generate_ir_synth_dataset():
    """
    Generate dataset for IR synthesizer training.
    Input: text with jurisdiction, Output: IR JSON
    """
    samples = []

    # Confidentiality IR examples
    confidentiality_examples = [
        {
            "input_text": "The Recipient shall maintain confidentiality of trade secrets under GDPR_EU.",
            "target_json": json.dumps({
                "parties": ["Recipient"],
                "rights": ["confidentiality"],
                "obligations": ["maintain secrecy"],
                "conditions": ["trade secrets"],
                "jurisdiction": "GDPR_EU"
            })
        },
        {
            "input_text": "Party A must keep proprietary information confidential in CONTRACT_NY.",
            "target_json": json.dumps({
                "parties": ["Party A"],
                "rights": ["confidentiality"],
                "obligations": ["keep proprietary information"],
                "conditions": ["confidential"],
                "jurisdiction": "CONTRACT_NY"
            })
        }
    ]

    # Indemnity IR examples
    indemnity_examples = [
        {
            "input_text": "Seller shall indemnify Buyer for product defects under CONTRACT_NY.",
            "target_json": json.dumps({
                "parties": ["Seller", "Buyer"],
                "rights": ["indemnification"],
                "obligations": ["compensate for defects"],
                "conditions": ["product defects"],
                "jurisdiction": "CONTRACT_NY"
            })
        },
        {
            "input_text": "Indemnitor agrees to compensate Indemnitee for claims in GDPR_EU.",
            "target_json": json.dumps({
                "parties": ["Indemnitor", "Indemnitee"],
                "rights": ["compensation"],
                "obligations": ["pay for claims"],
                "conditions": ["third-party claims"],
                "jurisdiction": "GDPR_EU"
            })
        }
    ]

    # Limitation of liability IR examples
    limitation_examples = [
        {
            "input_text": "Liability limited to contract price under GDPR_EU.",
            "target_json": json.dumps({
                "parties": [],
                "rights": ["liability limitation"],
                "obligations": ["cap damages"],
                "conditions": ["contract price"],
                "jurisdiction": "GDPR_EU"
            })
        },
        {
            "input_text": "Total liability shall not exceed $100,000 per CONTRACT_NY.",
            "target_json": json.dumps({
                "parties": [],
                "rights": ["liability cap"],
                "obligations": ["limit to $100,000"],
                "conditions": ["liability claims"],
                "jurisdiction": "CONTRACT_NY"
            })
        }
    ]

    samples.extend(confidentiality_examples)
    samples.extend(indemnity_examples)
    samples.extend(limitation_examples)

    return Dataset.from_list(samples)

def generate_realizer_dataset():
    """
    Generate dataset for realizer training.
    Input: IR JSON, Output: natural language text
    """
    samples = []

    # Confidentiality realization examples
    confidentiality_examples = [
        {
            "ir_json": json.dumps({
                "parties": ["Recipient"],
                "rights": ["confidentiality"],
                "obligations": ["maintain secrecy"],
                "conditions": ["trade secrets"],
                "jurisdiction": "GDPR_EU"
            }),
            "target_text": "The Recipient has the right to maintain confidentiality of trade secrets under GDPR_EU regulations."
        },
        {
            "ir_json": json.dumps({
                "parties": ["Party A"],
                "rights": ["confidentiality"],
                "obligations": ["keep proprietary information"],
                "conditions": ["confidential"],
                "jurisdiction": "CONTRACT_NY"
            }),
            "target_text": "Party A is obligated to keep proprietary information confidential under CONTRACT_NY jurisdiction."
        }
    ]

    # Indemnity realization examples
    indemnity_examples = [
        {
            "ir_json": json.dumps({
                "parties": ["Seller", "Buyer"],
                "rights": ["indemnification"],
                "obligations": ["compensate for defects"],
                "conditions": ["product defects"],
                "jurisdiction": "CONTRACT_NY"
            }),
            "target_text": "The Seller shall indemnify the Buyer for any losses arising from product defects under CONTRACT_NY law."
        },
        {
            "ir_json": json.dumps({
                "parties": ["Indemnitor", "Indemnitee"],
                "rights": ["compensation"],
                "obligations": ["pay for claims"],
                "conditions": ["third-party claims"],
                "jurisdiction": "GDPR_EU"
            }),
            "target_text": "The Indemnitor agrees to compensate the Indemnitee for third-party claims under GDPR_EU."
        }
    ]

    # Limitation realization examples
    limitation_examples = [
        {
            "ir_json": json.dumps({
                "parties": [],
                "rights": ["liability limitation"],
                "obligations": ["cap damages"],
                "conditions": ["contract price"],
                "jurisdiction": "GDPR_EU"
            }),
            "target_text": "Liability is limited to the contract price under GDPR_EU regulations."
        },
        {
            "ir_json": json.dumps({
                "parties": [],
                "rights": ["liability cap"],
                "obligations": ["limit to $100,000"],
                "conditions": ["liability claims"],
                "jurisdiction": "CONTRACT_NY"
            }),
            "target_text": "The total liability shall not exceed $100,000 pursuant to CONTRACT_NY law."
        }
    ]

    samples.extend(confidentiality_examples)
    samples.extend(indemnity_examples)
    samples.extend(limitation_examples)

    return Dataset.from_list(samples)

if __name__ == "__main__":
    # Generate and save datasets
    ner_dataset = generate_ner_dataset()
    ner_dataset.save_to_disk("./datasets/legal_ner_extended")

    ir_dataset = generate_ir_synth_dataset()
    ir_dataset.save_to_disk("./datasets/ir_synth_extended")

    realizer_dataset = generate_realizer_dataset()
    realizer_dataset.save_to_disk("./datasets/realizer_extended")

    print("Datasets generated and saved.")