"""
Neural Realizer (Decoder B) with templates and constraints for generating text from IR.
This module generates natural language text (e.g., court judgments) from Normative IR JSON.
"""

from transformers import T5Tokenizer, T5ForConditionalGeneration
import torch
import torch.nn as nn
from typing import Dict, Any


class NeuralRealizer:
    def __init__(self, model_name="t5-small"):
        """
        Initialize the realizer.

        Args:
            model_name: HuggingFace model name or path to fine-tuned model
        """
        self.tokenizer = T5Tokenizer.from_pretrained(model_name)
        self.model = T5ForConditionalGeneration.from_pretrained(model_name)
        self.templates = {
            "judgment": "The court finds that {parties[0]} has the right to {rights[0]} because {conditions[0]}.",
            "summary": "Case involving {parties[0]} and {parties[1]} regarding {rights[0]}.",
            "confidentiality_judgment": "Under {jurisdiction}, {parties[0]} must maintain confidentiality of {confidential_object} as the obligation exists and no breach has occurred.",
            "indemnity_judgment": "Under {jurisdiction}, {indemnitor} shall indemnify {indemnitee} for losses arising from {trigger_event}.",
            "limitation_judgment": "Under {jurisdiction}, liability is limited to {amount_limit} pursuant to the limitation of liability clause."
        }

    def realize_text(self, ir_json: Dict[str, Any], template_key="judgment", max_length=512) -> str:
        """
        Generate text from IR with jurisdiction context.

        Args:
            ir_json: IR dict
            template_key: Key for the template to use
            max_length: Max length of generated text

        Returns:
            Generated text
        """
        jurisdiction = ir_json.get("jurisdiction", "GENERAL")

        # Use template or model
        if template_key in self.templates:
            return self._fill_template(ir_json, template_key)
        else:
            # Use model for generation with jurisdiction context
            input_text = f"[JURISDICTION: {jurisdiction}] generate text from IR: {json.dumps(ir_json)}"
            input_ids = self.tokenizer(input_text, return_tensors="pt").input_ids
            outputs = self.model.generate(input_ids, max_length=max_length, num_beams=4, early_stopping=True)
            return self.tokenizer.decode(outputs[0], skip_special_tokens=True)

    def _fill_template(self, ir_json: Dict[str, Any], template_key: str) -> str:
        """
        Fill the template with IR data, including jurisdiction.
        """
        template = self.templates[template_key]
        # Simple string formatting, assuming lists have at least one element
        filled = template
        for key, value in ir_json.items():
            if key == "jurisdiction":
                filled = filled.replace("{jurisdiction}", str(value))
            elif isinstance(value, list) and value:
                filled = filled.replace(f"{{{key}[0]}}", str(value[0]))
                if len(value) > 1:
                    filled = filled.replace(f"{{{key}[1]}}", str(value[1]))
            elif isinstance(value, str):
                filled = filled.replace(f"{{{key}}}", str(value))
        return filled

    def fine_tune(self, train_dataset, eval_dataset, output_dir="./realizer_finetuned", use_adversarial=True):
        """
        Fine-tune the model with adversarial training for invariance.

        Args:
            train_dataset: Dataset with ir_json and target_text
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
                outputs = model(**inputs, labels=labels)
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
    import json
    realizer = NeuralRealizer()
    ir = {"parties": ["plaintiff", "defendant"], "rights": ["compensation"], "obligations": [], "conditions": ["breach occurred"]}
    text = realizer.realize_text(ir, "judgment")
    print(text)