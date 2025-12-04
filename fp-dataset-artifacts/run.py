import datasets
from transformers import AutoTokenizer, AutoModelForSequenceClassification, \
    AutoModelForQuestionAnswering, Trainer, TrainingArguments, HfArgumentParser
import evaluate
from helpers import prepare_dataset_nli, prepare_train_dataset_qa, \
    prepare_validation_dataset_qa, QuestionAnsweringTrainer, compute_accuracy
import os
import json
import glob
import numpy as np
from datetime import datetime

NUM_PREPROCESSING_WORKERS = 4

def encode_label(example):
    """ Handle label string to integer conversion, ignore the case."""
    label = example.get('label', None)

    # Treat None as invalid -2
    if label is None:
        example['label'] = -2
        return example

    # String labels: normalize case and map
    if isinstance(label, str):
        # some files have 'Neutral', 'CONTRADICTION', etc.
        label_norm = label.strip().lower()
        label2id = {
            "entailment": 0,
            "neutral": 1,
            "contradiction": 2,
        }
        # Treat unknown label string as invalid -1
        example["label"] = label2id.get(label_norm, -1)
        return example

    # Int labels: keep 0/1/2, anything else -> -3
    if isinstance(label, int):
        if label in (0, 1, 2):
            example["label"] = label
        else:
            example["label"] = -3
        return example

    # Fallback for other unexpected types as -4
    example['label'] = -4
    return example

def encode_label_sanitized(example):
    """
    Map all labels into {0: entailment, 1: neutral, 2: contradiction}.
    Anything invalid/unknown/else is forced to 1 (neutral).
    This is intentionally lossy but guarantees no weird labels reach
    the model, avoiding CUDA/HIP crashes.
    """
    label = example.get('label', None)

    # String labels: normalize case
    if isinstance(label, str):
        # some files have 'Neutral', 'CONTRADICTION', etc.
        label_norm = label.strip().lower()
        label2id = {
            "entailment": 0,
            "neutral": 1,
            "contradiction": 2,
        }
        # Unknown string -> neutral
        example["label"] = label2id.get(label_norm, 1)
        return example

    # Integer labels
    if isinstance(label, int):
        if label in (0, 1, 2):
            example["label"] = label
        else:
            # Other integer -> neutral
            example["label"] = 1
        return example

    # None, missing, floats, whatever else -> neutral
    example["label"] = 1
    return example

def main():
    argp = HfArgumentParser(TrainingArguments)
    # The HfArgumentParser object collects command-line arguments into an object (and provides default values for unspecified arguments).
    # In particular, TrainingArguments has several keys that you'll need/want to specify (when you call run.py from the command line):
    # --do_train
    #     When included, this argument tells the script to train a model.
    #     See docstrings for "--task" and "--dataset" for how the training dataset is selected.
    # --do_eval
    #     When included, this argument tells the script to evaluate the trained/loaded model on the validation split of the selected dataset.
    # --per_device_train_batch_size <int, default=8>
    #     This is the training batch size.
    #     If you're running on GPU, you should try to make this as large as you can without getting CUDA out-of-memory errors.
    #     For reference, with --max_length=128 and the default ELECTRA-small model, a batch size of 32 should fit in 4gb of GPU memory.
    # --num_train_epochs <float, default=3.0>
    #     How many passes to do through the training data.
    # --output_dir <path>
    #     Where to put the trained model checkpoint(s) and any eval predictions.
    #     *This argument is required*.

    # dataset artifacts options
    argp.add_argument('--model', type=str,
                      default='google/electra-small-discriminator',
                      help="""This argument specifies the base model to fine-tune.
        This should either be a HuggingFace model ID (see https://huggingface.co/models)
        or a path to a saved model checkpoint (a folder containing config.json and pytorch_model.bin).""")
    argp.add_argument('--task', type=str, choices=['nli', 'qa'], required=True,
                      help="""This argument specifies which task to train/evaluate on.
        Pass "nli" for natural language inference or "qa" for question answering.
        By default, "nli" will use the SNLI dataset, and "qa" will use the SQuAD dataset.""")
    argp.add_argument('--dataset', type=str, default=None,
                      help="""This argument overrides the default dataset used for the specified task.""")
    argp.add_argument('--max_length', type=int, default=128,
                      help="""This argument limits the maximum sequence length used during training/evaluation.
        Shorter sequence lengths need less memory and computation time, but some examples may end up getting truncated.""")
    argp.add_argument('--max_train_samples', type=int, default=None,
                      help='Limit the number of examples to train on.')
    argp.add_argument('--max_eval_samples', type=int, default=None,
                      help='Limit the number of examples to evaluate on.')
    # custom dataset options
    argp.add_argument('--use_custom_dataset', action='store_true',
                      help="""This argument overrides the default dataset used for the specified task.""")
    argp.add_argument('--train_dataset_path', type=str, default=None,
                      help="""Custom train dataset. Can be a path or a quoted glob pattern.""")
    argp.add_argument('--dev_dataset_path', type=str, default=None,
                      help="""Custom validation or dev dataset. Can be a path or a quoted glob pattern.""")
    argp.add_argument('--test_dataset_path', type=str, default=None,
                      help="""Custom evaluation or test dataset. Can be a path or a quoted glob pattern.""")
    argp.add_argument('--force_nli_label_mapping', action='store_true',
                      help="""If SNLI dataset label uses string not integer, we have to force mapping.""")
    # dataset cartography options
    argp.add_argument('--compute_training_dynamics', action='store_true',
                      help="""Load all checkpoints in output_dir and compute training-dynamics-based
        cartography metrics on the train split. Requires that checkpoints already exist in output_dir.""")
    argp.add_argument('--cartography_metrics_output_dir', type=str, default=None,
                      help="""Optional output directory to write cartography metrics jsonl.
                      Default: <output_dir>/cartography_metrics_snli/""")
    argp.add_argument('--cartography_filter_output_dir', type=str, default=None,
                      help="""Optional output directory for a filtered train input jsonl produced using
                      cartography metrics. Only supported when using --use_custom_dataset and
                      --train_dataset_path. Default: None (no filtering).""")
    argp.add_argument('--drop_easy_ratio', type=float, default=0.4,
                      help="""Fraction of easiest (highest-confidence, high-correctness) examples
                      to drop when filtering (cartography).""")
    argp.add_argument('--drop_hard_ratio', type=float, default=0.1,
                      help="""Fraction of hardest (lowest-confidence, low-correctness) examples
                      to drop as likely noise (cartography).""")
    argp.add_argument('--top_ambiguous_ratio', type=float, default=0.7,
                      help="""Among remaining examples after dropping easy/hard, keep this
                      fraction with highest variability (ambiguous region).""")

    training_args, args = argp.parse_args_into_dataclasses()

    # --------------------------------------------------------------------------
    # Dataset Artifacts: load augmented dataset and do training and evaluation
    # --------------------------------------------------------------------------
    # Dataset selection
    # IMPORTANT: this code path allows you to load custom datasets different from the standard SQuAD or SNLI ones.
    # You need to format the dataset appropriately. For SNLI, you can prepare a file with each line containing one
    # example as follows:
    # {"premise": "Two women are embracing.", "hypothesis": "The sisters are hugging.", "label": 1}
    all_datasets = []
    if args.use_custom_dataset:
        # Load from local json/jsonl file
        data_files = {}
        if args.train_dataset_path is not None:
            data_files['train'] = args.train_dataset_path
        if args.dev_dataset_path is not None:
            data_files['dev'] = args.dev_dataset_path
        if args.test_dataset_path is not None:
            data_files['test'] = args.test_dataset_path
        if not data_files:
            raise ValueError("use_custom_dataset is set, but train/dev/test dataset paths were not provided.")

        # Load raw dataset all at once, need multple GB of memory
        dataset = datasets.load_dataset('json', data_files=data_files)

        # Indicate that we're using a custom dataset not huggingface dataset
        dataset_id = None

        # Default eval split: prefer dev, then test, otherwise fall back to train
        if 'dev' in dataset:
            eval_split = 'dev'
        elif 'test' in dataset:
            eval_split = 'test'
        else:
            eval_split = 'train'

        # SNLI dataset uses string labels and needs mapping, only map what we need
        if args.task == 'nli':
            if args.force_nli_label_mapping:
                print("Mapping NLI dataset label from string to integer...")
                if training_args.do_train or args.compute_training_dynamics or (args.cartography_filter_output_dir is not None):
                    if 'train' in dataset: dataset['train'] = dataset['train'].map(encode_label_sanitized)
                if training_args.do_eval:
                    if 'dev' in dataset: dataset['dev'] = dataset['dev'].map(encode_label_sanitized)
                    if 'test' in dataset: dataset['test'] = dataset['test'].map(encode_label_sanitized)

    else:
        default_datasets = {'qa': ('squad',), 'nli': ('snli',)}
        dataset_id = tuple(args.dataset.split(':')) if args.dataset is not None else \
            default_datasets[args.task]

        # MNLI has two validation splits (one with matched domains and one with mismatched domains). Most datasets just have one "validation" split
        eval_split = 'validation_matched' if dataset_id == ('glue', 'mnli') else 'validation'
        # Load the raw data
        # if dataset_id == ("merged_anli_snli",):
        #     ps1 = tuple("facebook/anli",)
        #     ps2 = tuple("snli",)
        #     ds1 = datasets.load_dataset(*ps1)
        #     ds2 = datasets.load_dataset(*ps2)
        #     dataset = datasets.concatenate_datasets(ds1, ds2)
        #     # dataset = datasets.load_dataset(("facebook/anli")
        # else:
        #     dataset = datasets.load_dataset(*dataset_id)
        dataset = datasets.load_dataset(*dataset_id)

    # NLI models need to have the output label count specified (label 0 is "entailed", 1 is "neutral", and 2 is "contradiction")
    task_kwargs = {'num_labels': 3} if args.task == 'nli' else {}

    # Here we select the right model fine-tuning head
    model_classes = {'qa': AutoModelForQuestionAnswering,
                     'nli': AutoModelForSequenceClassification}
    model_class = model_classes[args.task]
    # Initialize the model and tokenizer from the specified pretrained model/checkpoint
    model = model_class.from_pretrained(args.model, **task_kwargs)
    # Make tensor contiguous if needed https://github.com/huggingface/transformers/issues/28293
    if hasattr(model, 'electra'):
        for param in model.electra.parameters():
            if not param.is_contiguous():
                param.data = param.data.contiguous()
    tokenizer = AutoTokenizer.from_pretrained(args.model, use_fast=True)

    # Select the dataset preprocessing function (these functions are defined in helpers.py)
    if args.task == 'qa':
        prepare_train_dataset = lambda exs: prepare_train_dataset_qa(exs, tokenizer)
        prepare_eval_dataset = lambda exs: prepare_validation_dataset_qa(exs, tokenizer)
    elif args.task == 'nli':
        prepare_train_dataset = prepare_eval_dataset = \
            lambda exs: prepare_dataset_nli(exs, tokenizer, args.max_length)
        # prepare_eval_dataset = prepare_dataset_nli
    else:
        raise ValueError('Unrecognized task name: {}'.format(args.task))

    print("Preprocessing data... (this takes a little bit, should only happen once per dataset)")
    if dataset_id == ('snli',):
        # remove SNLI examples with no label
        dataset = dataset.filter(lambda ex: ex['label'] != -1)

    train_dataset = None
    eval_dataset = None
    train_dataset_featurized = None
    eval_dataset_featurized = None

    # Besides finetuning using LIT augmented dataset, new dataset cartography also needs train dataset
    if training_args.do_train or args.compute_training_dynamics or (args.cartography_filter_output_dir is not None):
        if dataset_id is not None and any(item in ("anli","facebook/anli") for item in dataset_id):
            # anli_r1_train = datasets.load_dataset("anli", split="train_r1")
            # anli_r2_train = datasets.load_dataset("anli", split="train_r2")
            # anli_r3_train = datasets.load_dataset("anli", split="train_r3")
            anli_r1_train = dataset["train_r1"]
            anli_r2_train = dataset["train_r2"]
            anli_r3_train = dataset["train_r3"]
            train_dataset = datasets.concatenate_datasets([anli_r1_train, anli_r2_train, anli_r3_train])
            train_dataset = train_dataset.filter(lambda ex: ex['label'] != -1)
        # train_split = 'train_r3' if (any(item in ("anli","facebook/anli") for item in dataset_id))  else 'train'
        # elif dataset_id == "merged_anli_snli":
        #     anli_r1_train = datasets.load_dataset("anli", split="train_r1")
        #     anli_r2_train = datasets.load_dataset("anli", split="train_r2")
        #     anli_r3_train = datasets.load_dataset("anli", split="train_r3")
        #     snli_train = datasets.load_dataset("snli", split="train")
        #     train_dataset = datasets.concatenate_datasets([anli_r1_train, anli_r2_train, anli_r3_train, snli_train])
        #     train_dataset = train_dataset.filter(lambda ex: ex['label'] != -1)
        else:
            # print(f"{train_split=}")
            # print(f"{dataset=}")
            train_dataset = dataset["train"]

        if args.max_train_samples:
            train_dataset = train_dataset.select(range(args.max_train_samples))

        train_dataset_featurized = train_dataset.map(
            prepare_train_dataset,
            batched=True,
            num_proc=NUM_PREPROCESSING_WORKERS,
            remove_columns=[c for c in train_dataset.column_names if c not in ('label', 'id')]
        )

    if training_args.do_eval:
        # print(f"{dataset_id=}")
        # eval_split = 'test_r1' if "anli" in dataset_id else eval_split

        # eval_split = 'test_r3' if (any(item in ("anli","facebook/anli") for item in dataset_id))  else eval_split
        if dataset_id is not None and any(item in ("anli","facebook/anli") for item in dataset_id):
            anli_r1_train = dataset["test_r1"]
            anli_r2_train = dataset["test_r2"]
            anli_r3_train = dataset["test_r3"]
            eval_dataset = datasets.concatenate_datasets([anli_r1_train, anli_r2_train, anli_r3_train])
            eval_dataset = eval_dataset.filter(lambda ex: ex['label'] != -1)
        # train_split = 'train_r3' if (any(item in ("anli","facebook/anli") for item in dataset_id))  else 'train'
        else:
            eval_dataset = dataset[eval_split]

        if args.max_eval_samples:
            eval_dataset = eval_dataset.select(range(args.max_eval_samples))

        eval_dataset_featurized = eval_dataset.map(
            prepare_eval_dataset,
            batched=True,
            num_proc=NUM_PREPROCESSING_WORKERS,
            remove_columns=eval_dataset.column_names
        )

    # Select the training configuration
    trainer_class = Trainer
    eval_kwargs = {}
    # If you want to use custom metrics, you should define your own "compute_metrics" function.
    # For an example of a valid compute_metrics function, see compute_accuracy in helpers.py.
    compute_metrics = None
    if args.task == 'qa':
        # For QA, we need to use a tweaked version of the Trainer (defined in helpers.py)
        # to enable the question-answering specific evaluation metrics
        trainer_class = QuestionAnsweringTrainer
        eval_kwargs['eval_examples'] = eval_dataset
        metric = evaluate.load('squad')   # datasets.load_metric() deprecated
        compute_metrics = lambda eval_preds: metric.compute(
            predictions=eval_preds.predictions, references=eval_preds.label_ids)
    elif args.task == 'nli':
        compute_metrics = compute_accuracy

    # This function wraps the compute_metrics function, storing the model's predictions
    # so that they can be dumped along with the computed metrics
    eval_predictions = None
    def compute_metrics_and_store_predictions(eval_preds):
        nonlocal eval_predictions
        eval_predictions = eval_preds
        return compute_metrics(eval_preds)

    # Initialize the Trainer object with the specified arguments and the model and dataset we loaded above
    trainer = trainer_class(
        model=model,
        args=training_args,
        train_dataset=train_dataset_featurized,
        eval_dataset=eval_dataset_featurized,
        tokenizer=tokenizer,
        compute_metrics=compute_metrics_and_store_predictions
    )
    # Train and/or evaluate
    if training_args.do_train:
        trainer.train()
        trainer.save_model()
        # If you want to customize the way the loss is computed, you should subclass Trainer and override the "compute_loss"
        # method (see https://huggingface.co/transformers/_modules/transformers/trainer.html#Trainer.compute_loss).
        #
        # You can also add training hooks using Trainer.add_callback:
        #   See https://huggingface.co/transformers/main_classes/trainer.html#transformers.Trainer.add_callback
        #   and https://huggingface.co/transformers/main_classes/callback.html#transformers.TrainerCallback

    if training_args.do_eval:
        results = trainer.evaluate(**eval_kwargs)

        # To add custom metrics, you should replace the "compute_metrics" function (see comments above).
        #
        # If you want to change how predictions are computed, you should subclass Trainer and override the "prediction_step"
        # method (see https://huggingface.co/transformers/_modules/transformers/trainer.html#Trainer.prediction_step).
        # If you do this your custom prediction_step should probably start by calling super().prediction_step and modifying the
        # values that it returns.

        print('Evaluation results:')
        print(results)

        os.makedirs(training_args.output_dir, exist_ok=True)

        with open(os.path.join(training_args.output_dir, 'eval_metrics.json'), encoding='utf-8', mode='w') as f:
            json.dump(results, f)

        with open(os.path.join(training_args.output_dir, 'eval_predictions.jsonl'), encoding='utf-8', mode='w') as f:
            if args.task == 'qa':
                predictions_by_id = {pred['id']: pred['prediction_text'] for pred in eval_predictions.predictions}
                eval_dataset_with_prediction = []
                for example in eval_dataset:
                    example_with_prediction = dict(example)
                    example_with_prediction['predicted_answer'] = predictions_by_id[example['id']]
                    eval_dataset_with_prediction.append(example_with_prediction)
                    # f.write(json.dumps(example_with_prediction))
                    # f.write(',\n')
                json.dump(eval_dataset_with_prediction, f)
            else:
                eval_dataset_with_prediction = []
                for i, example in enumerate(eval_dataset):
                    example_with_prediction = dict(example)
                    example_with_prediction['predicted_scores'] = eval_predictions.predictions[i].tolist()
                    pred = int(eval_predictions.predictions[i].argmax())

                    example_with_prediction['predicted_label'] = pred
                    label = example['label']
                    if pred == example['label']:
                        if label == 0:
                            example_with_prediction['status'] = 'True Entailment'
                        elif label == 1:
                            example_with_prediction['status'] = 'True Neutral'
                        else:
                            example_with_prediction['status'] = 'True Contradict'
                    if pred != example['label']:
                        if label == 0 and pred == 1:
                            example_with_prediction['status'] = 'False Neutral - Entailment'
                        elif label == 0 and pred == 2:
                            example_with_prediction['status'] = 'False Contradict'
                        elif label == 1 and pred == 0:
                            example_with_prediction['status'] = ' False Entailment - Neutral'
                        elif label == 1 and pred == 2:
                            example_with_prediction['status'] = ' False Contradict - Neutral'
                        elif label == 2 and pred == 0:
                            example_with_prediction['status'] = ' False Entailment'
                        elif label == 2 and pred == 2:
                            example_with_prediction['status'] = ' False Neutral - Contradict'

                    eval_dataset_with_prediction.append(example_with_prediction)
                    # f.write(json.dumps(example_with_prediction))
                    # f.write('\n')
                json.dump(eval_dataset_with_prediction, f, indent=2)

    # --------------------------------------------------------------------------
    # Dataset Cartography: compute training dynamics then do optional filtering
    # --------------------------------------------------------------------------
    if args.task == 'nli' and args.compute_training_dynamics:
        print(f"[Dataset Cartography] Calculating training dynamics...")
        if train_dataset_featurized is None or train_dataset is None:
            raise ValueError(
                "[Cartography] compute_training_dynamics is set, but train_dataset/train_dataset_featurized "
                "were not prepared. Make sure you are using a dataset with a 'train' split "
                "and that --use_custom_dataset/--train_dataset_path are set correctly."
            )

        # Find all checkpoints in output_dir; these correspond to epochs if you trained
        # with --save_strategy epoch. This matches the behavior in Dataset Cartography, where
        # training dynamics are recorded across multiple epochs.
        checkpoint_paths = sorted(
            glob.glob(os.path.join(training_args.output_dir, "checkpoint-*")),
            key=lambda p: int(os.path.basename(p).split("-")[-1])
        )
        if not checkpoint_paths:
            print(
                f"[Cartography] No checkpoints found in {training_args.output_dir}. "
                f"To compute training dynamics, first train with --do_train and "
                f"--save_strategy epoch or --save_strategy steps --save_steps 10000"
            )
        else:
            print(f"[Cartography] Found {len(checkpoint_paths)} checkpoints for training dynamics:")
            for ck in checkpoint_paths:
                print("   ", ck)

            # We'll compute, for each training example i:
            #   - confidence: mean p(gold | x_i) across epochs
            #   - variability: stddev of p(gold | x_i) across epochs
            #   - correctness: fraction of epochs where argmax == gold label
            # These correspond to the coordinates used in Data Maps.

            # Gold label (as numpy)
            if 'label' in train_dataset_featurized.column_names:
                gold_labels = np.array(train_dataset_featurized['label'], dtype=np.int64)
            else:
                raise ValueError(
                    "[Cartography] Could not find 'label' column in train_dataset_featurized which is "
                    "needed for training dynamics."
                )

            num_examples = gold_labels.shape[0]
            num_labels = int(max(gold_labels)) + 1
            print(f"[Cartography] Computing training dynamics for {num_examples} examples each with one of {num_labels} labels.")

            # Also capture example IDs from the raw train_dataset for sanity-check later
            if 'id' in train_dataset.column_names:
                example_ids = list(train_dataset['id'])
                if len(example_ids) != num_examples:
                    raise ValueError(
                        "[Cartography] Length mismatch between train_dataset['id'] and train_dataset_featurized."
                    )
            else:
                example_ids = [str(i) for i in range(num_examples)]

            def _softmax(x):
                x = x - x.max(axis=-1, keepdims=True)
                e = np.exp(x)
                return e / e.sum(axis=-1, keepdims=True)

            gold_probs_per_epoch = []
            correct_per_epoch = []

            for epoch_idx, ckpt_path in enumerate(checkpoint_paths, start=1):
                print(f"[Cartography] Epoch {epoch_idx}: loading {ckpt_path}")
                epoch_model = model_class.from_pretrained(ckpt_path, **task_kwargs)

                # Make tensor contiguous if needed (ELECTRA quirk)
                if hasattr(epoch_model, 'electra'):
                    for param in epoch_model.electra.parameters():
                        if not param.is_contiguous():
                            param.data = param.data.contiguous()

                # Use a lightweight TrainingArguments config for prediction only.
                eval_args = TrainingArguments(
                    output_dir=os.path.join(training_args.output_dir, f"td_epoch_{epoch_idx}"),
                    per_device_eval_batch_size=training_args.per_device_eval_batch_size,
                    do_train=False,
                    do_eval=False,
                    logging_strategy="no",
                    save_strategy="no"
                )

                td_trainer = trainer_class(
                    model=epoch_model,
                    args=eval_args,
                    train_dataset=None,
                    eval_dataset=train_dataset_featurized,
                    tokenizer=tokenizer,
                    compute_metrics=None
                )

                print(f"[Cartography] Predicting on train set for epoch {epoch_idx}...")
                td_output = td_trainer.predict(train_dataset_featurized)
                logits = td_output.predictions  # [N, num_labels]
                if logits.shape[0] != num_examples:
                    raise ValueError("Prediction size mismatch in training dynamics.")

                probs = _softmax(logits)
                gold_prob_vec = probs[np.arange(num_examples), gold_labels]
                preds = probs.argmax(axis=-1)
                is_correct_vec = (preds == gold_labels).astype(np.float32)

                gold_probs_per_epoch.append(gold_prob_vec)
                correct_per_epoch.append(is_correct_vec)

            # Stack into [N, T]
            gold_probs_stack = np.stack(gold_probs_per_epoch, axis=1)
            correct_stack = np.stack(correct_per_epoch, axis=1)
            T = gold_probs_stack.shape[1]

            confidence = gold_probs_stack.mean(axis=1)
            variability = gold_probs_stack.std(axis=1)
            correctness = correct_stack.mean(axis=1)

            # Where to store metrics
            if args.cartography_metrics_output_dir is None:
                metrics_output_dir = os.path.join(os.path.join(training_args.output_dir, "cartography_metrics_snli"))
            else:
                metrics_output_dir = args.cartography_metrics_output_dir
            os.makedirs(metrics_output_dir, exist_ok=True)
            metrics_output_path = os.path.join(metrics_output_dir, f"cartography_metrics_snli_{datetime.now().strftime('%Y%m%d_%H%M%S')}.jsonl")
            print(f"[Cartography] Writing metrics to {metrics_output_path}")

            with open(metrics_output_path, 'w', encoding='utf-8') as f:
                for idx in range(num_examples):
                    rec = {
                        "index": int(idx),
                        "id": example_ids[idx],
                        "gold": int(gold_labels[idx]),
                        "confidence": float(confidence[idx]),
                        "variability": float(variability[idx]),
                        "correctness": float(correctness[idx]),
                        "num_epochs": int(T)
                    }
                    f.write(json.dumps(rec))
                    f.write('\n')

            # Immediately filter train dataset using the metrics we just computed
            if not os.path.exists(metrics_output_dir):
                os.makedirs(metrics_output_dir, exist_ok=True)
            metrics_output_path = os.path.join(metrics_output_dir, f"cartography_metrics_snli_{datetime.now().strftime('%Y%m%d_%H%M%S')}.jsonl")
            print(f"[Cartography] Writing metrics to {metrics_output_path}")

            if args.cartography_filter_output_dir is not None:
                if not args.use_custom_dataset or args.train_dataset_path is None:
                    print(
                        "[Cartography] cartography_filter_output_dir was set, but either "
                        "--use_custom_dataset or --train_dataset_path is missing. "
                        "Filtering is currently only supported for custom JSON/JSONL train datasets."
                    )
                else:
                    print("[Cartography] Applying cartography-based filtering to the train set...")

                    drop_easy_ratio = args.drop_easy_ratio
                    drop_hard_ratio= args.drop_hard_ratio
                    top_ambiguous_ratio = args.top_ambiguous_ratio

                    # Quantile thresholds on confidence
                    if 0.0 < drop_easy_ratio < 1.0:
                        easy_threshold = np.quantile(confidence, 1.0 - drop_easy_ratio)
                    else:
                        easy_threshold = 1.1  # effectively disables easy-dropping

                    if 0.0 < drop_hard_ratio < 1.0:
                        hard_threshold = np.quantile(confidence, drop_hard_ratio)
                    else:
                        hard_threshold = -0.1  # effectively disables hard-dropping

                    print(f"[Cartography] Hard (low-confidence) threshold: {hard_threshold:.4f}")
                    print(f"[Cartography] Easy (high-confidence) threshold: {easy_threshold:.4f}")

                    # First pass: drop very easy (high-conf + high-correct) and very hard (low-conf + low-correct).
                    selected_indices = []
                    for idx in range(num_examples):
                        c = confidence[idx]
                        v = variability[idx]
                        corr_i = correctness[idx]

                        # Drop "too easy" examples likely dominated by artifacts.
                        if drop_easy_ratio > 0.0 and c >= easy_threshold and corr_i >= 0.9:
                            continue

                        # Drop "too hard" / noisy examples (very low confidence and correctness).
                        if drop_hard_ratio > 0.0 and c <= hard_threshold and corr_i <= 0.34:
                            continue

                        selected_indices.append(idx)

                    print(f"[Cartography] After easy/hard filtering: {len(selected_indices)} / {num_examples} examples remain.")

                    final_indices = selected_indices
                    if 0.0 < top_ambiguous_ratio < 1.0 and len(selected_indices) > 0:
                        vars_selected = np.array([variability[i] for i in selected_indices], dtype=np.float32)
                        var_threshold = np.quantile(vars_selected, 1.0 - top_ambiguous_ratio)
                        print(f"[Cartography] Variability threshold for ambiguous region: {var_threshold:.4f}")
                        final_indices = [i for i in selected_indices if variability[i] >= var_threshold]

                    print(f"[Cartography] Final selected examples: {len(final_indices)}")

                    # Streaming over original train jsonl files to write filtered subset using glob
                    # Assumes each JSONL line corresponds to one training example in the same order
                    # as load_dataset('json', data_files=...), double check with "id" field if present.

                    # Prepare filter output directory
                    filter_output_dir = args.cartography_filter_output_dir
                    os.makedirs(filter_output_dir, exist_ok=True)

                    # Expand glob for train_dataset_path as file list
                    train_paths = sorted(glob.glob(args.train_dataset_path))
                    if not train_paths:
                        raise ValueError(
                            f"[Cartography] No training files matched pattern: {args.train_dataset_path}"
                        )

                    print("[Cartography] Implementing one-to-one filtering for each train shard...")
                    for p in train_paths:
                        print("   [input shard]", p)

                    keep_set = set(final_indices)
                    global_idx = 0  # index into HF train_dataset / metrics arrays
                    kept_total = 0
                    warn_mismatch_printed = False

                    # One output file per input shard, same basename, in filter_output_dir
                    for in_path in train_paths:
                        shard_name = os.path.basename(in_path)
                        out_path = os.path.join(filter_output_dir, shard_name)

                        print(f"[Cartography]  Filtering shard:")
                        print(f"   Input : {in_path}")
                        print(f"   Output: {out_path}")

                        with open(in_path, 'r', encoding='utf-8') as fin, \
                             open(out_path, 'w', encoding='utf-8') as fout:
                            for line in fin:
                                # Parse to get the id
                                try:
                                    obj = json.loads(line)
                                except json.JSONDecodeError:
                                    # If something is malformed, just skip it
                                    global_idx += 1
                                    continue

                                line_id = obj.get("id", None)

                                # Sanity check: if we have an expected id for this index, verify it matches.
                                if global_idx < len(example_ids) and line_id is not None:
                                    expected_id = example_ids[global_idx]
                                    if line_id != expected_id and not warn_mismatch_printed:
                                        print(
                                            "[Cartography] WARNING: ID mismatch between raw JSONL and "
                                            "HF dataset order at global index {}: JSONL id='{}', dataset id='{}'. "
                                            "Check that train_dataset_path matches the dataset used for "
                                            "training/carto.".format(global_idx, line_id, expected_id)
                                        )
                                        warn_mismatch_printed = True  # only print once

                                # Index-based filtering as before
                                if global_idx in keep_set:
                                    fout.write(line)
                                    kept_total += 1

                                # Advance global index across ALL shards, to stay aligned
                                # with train_dataset / metrics (which are concatenated).
                                global_idx += 1

                    print(
                        f"[Cartography] Wrote {kept_total} filtered training examples "
                        f"across {len(train_paths)} shards into directory: {filter_output_dir}"
                    )


if __name__ == "__main__":
    main()
