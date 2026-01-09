"""
Fine-tuned Legal-BERT for extracting IR candidates from legal text.
This module implements Named Entity Recognition (NER) to identify entities like parties, rights, obligations, etc.
that can be used to construct Normative IR candidates.
"""

from transformers import AutoTokenizer, AutoModelForTokenClassification, pipeline
import torch
import torch.nn as nn


class LegalBERTExtractor:
    def __init__(self, model_name="nlpaueb/legal-bert-base-uncased", labels=None):
        """
        Initialize the Legal-BERT extractor.

        Args:
            model_name: HuggingFace model name or path to fine-tuned model
            labels: List of NER labels, e.g., ['PARTY', 'RIGHT', 'OBLIGATION', 'CONDITION']
        """
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)
        self.model = AutoModelForTokenClassification.from_pretrained(model_name, num_labels=len(labels) if labels else 13)
        self.labels = labels or ['O', 'B-PARTY', 'I-PARTY', 'B-RIGHT', 'I-RIGHT', 'B-OBLIGATION', 'I-OBLIGATION', 'B-CONDITION', 'I-CONDITION', 'B-CONFIDENTIALITY', 'B-INDEMNITY', 'B-LIMITATION', 'B-JURISDICTION']
        self.id2label = {i: label for i, label in enumerate(self.labels)}
        self.label2id = {label: i for i, label in enumerate(self.labels)}
        self.model.config.id2label = self.id2label
        self.model.config.label2id = self.label2id
        self.pipeline = pipeline("ner", model=self.model, tokenizer=self.tokenizer, aggregation_strategy="simple")

    def extract_entities_with_jurisdiction(self, text, jurisdiction="GENERAL"):
        """
        Extract entities with jurisdiction context.

        Args:
            text: Legal text
            jurisdiction: Jurisdiction context (e.g., 'GDPR_EU', 'CONTRACT_NY')

        Returns:
            List of extracted entities
        """
        # Prepend jurisdiction to input for context
        input_text = f"[JURISDICTION: {jurisdiction}] {text}"
        return self.pipeline(input_text)

    def extract_entities(self, text):
        """
        Extract IR candidate entities from text.

        Args:
            text: Legal text string

        Returns:
            List of extracted entities with labels
        """
        return self.pipeline(text)

    def fine_tune(self, train_dataset, eval_dataset, output_dir="./legal_bert_finetuned", use_adversarial=True):
        """
        Fine-tune the model on training data with adversarial training for invariance.

        Args:
            train_dataset: HuggingFace Dataset for training
            eval_dataset: HuggingFace Dataset for evaluation
            output_dir: Directory to save the fine-tuned model
            use_adversarial: Whether to use adversarial training for invariance
        """
        from transformers import TrainingArguments, Trainer
        import torch.nn.functional as F

        # Custom trainer with adversarial training
        class AdversarialTrainer(Trainer):
            def compute_loss(self, model, inputs, return_outputs=False):
                labels = inputs.pop("labels")
                outputs = model(**inputs)
                loss = F.cross_entropy(outputs.logits.view(-1, self.model.config.num_labels), labels.view(-1))

                if use_adversarial and self.training:
                    # Fast Gradient Method for adversarial training
                    epsilon = 0.01
                    inputs_embeds = model.get_input_embeddings()(inputs['input_ids'])
                    inputs_embeds.retain_grad()
                    loss.backward(retain_graph=True)

                    # Generate adversarial examples
                    inputs_embeds_grad = inputs_embeds.grad
                    adv_inputs_embeds = inputs_embeds + epsilon * inputs_embeds_grad.sign()
                    adv_outputs = model(inputs_embeds=adv_inputs_embeds, attention_mask=inputs['attention_mask'])
                    adv_loss = F.cross_entropy(adv_outputs.logits.view(-1, self.model.config.num_labels), labels.view(-1))

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
            weight_decay=0.01,
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
        self.pipeline = pipeline("ner", model=output_dir, tokenizer=self.tokenizer, aggregation_strategy="simple")


# Example usage
if __name__ == "__main__":
    extractor = LegalBERTExtractor()
    text = "The plaintiff has the right to compensation if the defendant breached the contract."
    entities = extractor.extract_entities(text)
    print(entities)