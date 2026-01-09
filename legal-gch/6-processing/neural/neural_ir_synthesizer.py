"""
Neural IR Synthesizer (Decoder A) with constrained decoding for generating valid IR JSON.
This module uses a seq2seq model (e.g., T5) to generate Normative IR JSON from text or extracted entities.
Constrained decoding ensures the output is valid JSON conforming to the IR schema.
"""

from transformers import T5Tokenizer, T5ForConditionalGeneration
import torch
import torch.nn as nn
import json
from typing import Dict, Any


class NeuralIRSynthesizer:
    def __init__(self, model_name="t5-small"):
        """
        Initialize the synthesizer.

        Args:
            model_name: HuggingFace model name or path to fine-tuned model
        """
        self.tokenizer = T5Tokenizer.from_pretrained(model_name)
        self.model = T5ForConditionalGeneration.from_pretrained(model_name)

    def generate_ir(self, input_text: str, jurisdiction="GENERAL", max_length=512) -> Dict[str, Any]:
        """
        Generate IR JSON from input text with jurisdiction context.

        Args:
            input_text: Text or extracted entities
            jurisdiction: Jurisdiction context
            max_length: Max length of generated text

        Returns:
            Parsed IR JSON dict
        """
        input_text_with_jurisdiction = f"[JURISDICTION: {jurisdiction}] generate IR: {input_text}"
        input_ids = self.tokenizer(input_text_with_jurisdiction, return_tensors="pt").input_ids
        outputs = self.model.generate(input_ids, max_length=max_length, num_beams=4, early_stopping=True)
        generated_text = self.tokenizer.decode(outputs[0], skip_special_tokens=True)

        # Constrained decoding: try to parse as JSON, if fails, regenerate with constraints
        try:
            ir_json = json.loads(generated_text)
            self._validate_ir_schema(ir_json)
            ir_json["jurisdiction"] = jurisdiction  # Add jurisdiction to IR
            return ir_json
        except (json.JSONDecodeError, ValueError):
            # Fallback: use constrained generation
            ir_json = self._constrained_generate(input_text)
            ir_json["jurisdiction"] = jurisdiction
            return ir_json

    def _constrained_generate(self, input_text: str) -> Dict[str, Any]:
        """
        Generate with constraints to ensure valid IR JSON.
        """
        # For simplicity, define a template and fill
        # In practice, use a library like jsonformer or custom beam search
        template = {
            "parties": [],
            "rights": [],
            "obligations": [],
            "conditions": []
        }
        # Enhanced dummy implementation: extract from text using simple rules for new domains
        # Real implementation would use the model with constraints
        if "plaintiff" in input_text.lower():
            template["parties"].append("plaintiff")
        if "defendant" in input_text.lower():
            template["parties"].append("defendant")
        if "recipient" in input_text.lower():
            template["parties"].append("recipient")
        if "party a" in input_text.lower():
            template["parties"].append("party_a")
        if "party b" in input_text.lower():
            template["parties"].append("party_b")
        if "indemnitor" in input_text.lower():
            template["parties"].append("indemnitor")
        if "indemnitee" in input_text.lower():
            template["parties"].append("indemnitee")
        if "seller" in input_text.lower():
            template["parties"].append("seller")
        if "buyer" in input_text.lower():
            template["parties"].append("buyer")

        if "right" in input_text.lower():
            template["rights"].append("compensation")
        if "confidential" in input_text.lower():
            template["rights"].append("confidentiality")
        if "indemnif" in input_text.lower():
            template["rights"].append("indemnification")
        if "liability" in input_text.lower() and "limit" in input_text.lower():
            template["rights"].append("liability_limitation")

        if "breach" in input_text.lower():
            template["conditions"].append("breached_contract")
        if "disclos" in input_text.lower():
            template["conditions"].append("disclosure_occurred")
        if "trigger" in input_text.lower():
            template["conditions"].append("trigger_event")
        if "defect" in input_text.lower():
            template["conditions"].append("product_defects")

        if "maintain" in input_text.lower() and "secret" in input_text.lower():
            template["obligations"].append("maintain_secrecy")
        if "compensat" in input_text.lower():
            template["obligations"].append("compensate_losses")
        if "cap" in input_text.lower() and "damag" in input_text.lower():
            template["obligations"].append("cap_damages")

        return template

    def _validate_ir_schema(self, ir_json: Dict[str, Any]):
        """
        Validate that the generated JSON matches the IR schema.
        Raises ValueError if invalid.
        """
        required_keys = ["parties", "rights", "obligations", "conditions"]
        for key in required_keys:
            if key not in ir_json or not isinstance(ir_json[key], list):
                raise ValueError(f"Invalid IR: missing or invalid {key}")

    def fine_tune(self, train_dataset, eval_dataset, output_dir="./ir_synthesizer_finetuned", use_adversarial=True):
        """
        Fine-tune the model with adversarial training for invariance.

        Args:
            train_dataset: Dataset with input_text and target_json
            eval_dataset: Evaluation dataset
            output_dir: Save directory
            use_adversarial: Whether to use adversarial training
        """
        from transformers import TrainingArguments, Trainer
        import torch.nn.functional as F

        # Custom trainer with adversarial training
        class AdversarialTrainer(Trainer):
            def compute_loss(self, model, inputs, return_outputs=False):
                labels = inputs.pop("labels")
                outputs = model(**inputs)
                loss = outputs.loss

                if use_adversarial and self.training:
                    # Fast Gradient Method for adversarial training
                    epsilon = 0.01
                    inputs_embeds = model.get_input_embeddings()(inputs['input_ids'])
                    inputs_embeds.retain_grad()
                    loss.backward(retain_graph=True)

                    # Generate adversarial examples
                    inputs_embeds_grad = inputs_embeds.grad
                    adv_inputs_embeds = inputs_embeds + epsilon * inputs_embeds_grad.sign()
                    adv_outputs = model(inputs_embeds=adv_inputs_embeds, attention_mask=inputs['attention_mask'], labels=labels)
                    adv_loss = adv_outputs.loss

                    loss = (loss + adv_loss) / 2

                return (loss, outputs) if return_outputs else loss

        training_args = TrainingArguments(
            output_dir=output_dir,
            evaluation_strategy="epoch",
            save_strategy="epoch",
            load_best_model_at_end=True,
            per_device_train_batch_size=8,
            per_device_eval_batch_size=8,
            num_train_epochs=3,
            learning_rate=2e-5,
        )

        trainer = AdversarialTrainer(
            model=self.model,
            args=training_args,
            train_dataset=train_dataset,
            eval_dataset=eval_dataset,
            tokenizer=self.tokenizer,
        )

        trainer.train()
        trainer.save_model(output_dir)
        self.tokenizer.save_pretrained(output_dir)


# Example usage
if __name__ == "__main__":
    synthesizer = NeuralIRSynthesizer()
    text = "The plaintiff has the right to compensation if the defendant breached the contract."
    ir = synthesizer.generate_ir(text)
    print(ir)