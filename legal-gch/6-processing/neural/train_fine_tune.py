"""
Script for training and fine-tuning the neural components on new domains.
Includes adversarial training for invariance and jurisdiction-specific datasets.
"""

from legal_bert_extraction import LegalBERTExtractor
from neural_ir_synthesizer import NeuralIRSynthesizer
from neural_realizer import NeuralRealizer
from datasets import load_dataset
import os


def main():
    # Create directories for models and datasets
    os.makedirs("./models", exist_ok=True)
    os.makedirs("./datasets", exist_ok=True)

    # Load datasets for new domains
    print("Loading NER dataset for extended legal domains...")
    from datasets import load_from_disk
    ner_dataset = load_from_disk("./datasets/legal_ner_extended")
    ner_train = ner_dataset
    ner_eval = ner_dataset  # Using same for demo; in practice split properly

    print("Loading IR synthesis dataset...")
    ir_dataset = load_from_disk("./datasets/ir_synth_extended")
    ir_train = ir_dataset
    ir_eval = ir_dataset

    print("Loading realizer dataset...")
    realizer_dataset = load_from_disk("./datasets/realizer_extended")
    realizer_train = realizer_dataset
    realizer_eval = realizer_dataset

    # Preprocess NER dataset
    def tokenize_and_align_labels(examples):
        tokenizer = extractor.tokenizer
        tokenized_inputs = tokenizer(examples["tokens"], truncation=True, is_split_into_words=True)
        labels = []
        for i, label in enumerate(examples[f"ner_tags"]):
            word_ids = tokenized_inputs.word_ids(batch_index=i)
            previous_word_idx = None
            label_ids = []
            for word_idx in word_ids:
                if word_idx is None:
                    label_ids.append(-100)
                elif word_idx != previous_word_idx:
                    label_ids.append(label[word_idx])
                else:
                    label_ids.append(-100)
                previous_word_idx = word_idx
            labels.append(label_ids)
        tokenized_inputs["labels"] = labels
        return tokenized_inputs

    ner_train = ner_train.map(tokenize_and_align_labels, batched=True)
    ner_eval = ner_eval.map(tokenize_and_align_labels, batched=True)

    # Fine-tune Legal-BERT for extraction with adversarial training
    print("Fine-tuning Legal-BERT extractor...")
    extractor.fine_tune(ner_train, ner_eval, "./models/legal_bert_finetuned_extended", use_adversarial=True)

    # Fine-tune IR Synthesizer with adversarial training
    print("Fine-tuning IR synthesizer...")
    synthesizer = NeuralIRSynthesizer()
    synthesizer.fine_tune(ir_train, ir_eval, "./models/ir_synthesizer_finetuned_extended", use_adversarial=True)

    # Fine-tune Realizer with adversarial training
    print("Fine-tuning realizer...")
    realizer = NeuralRealizer()
    realizer.fine_tune(realizer_train, realizer_eval, "./models/realizer_finetuned_extended", use_adversarial=True)

    print("Fine-tuning completed with adversarial training for invariance.")


if __name__ == "__main__":
    main()