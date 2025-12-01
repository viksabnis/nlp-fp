import datasets
from transformers import AutoTokenizer, AutoModelForSequenceClassification, \
    AutoModelForQuestionAnswering, Trainer, TrainingArguments, HfArgumentParser
import evaluate
from helpers import prepare_dataset_nli, prepare_train_dataset_qa, \
    prepare_validation_dataset_qa, QuestionAnsweringTrainer, compute_accuracy
import os
import json

NUM_PREPROCESSING_WORKERS = 2


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

    training_args, args = argp.parse_args_into_dataclasses()

    # Dataset selection
    # IMPORTANT: this code path allows you to load custom datasets different from the standard SQuAD or SNLI ones.
    # You need to format the dataset appropriately. For SNLI, you can prepare a file with each line containing one
    # example as follows:
    # {"premise": "Two women are embracing.", "hypothesis": "The sisters are hugging.", "label": 1}
    all_datasets = []
    if args.dataset.endswith('.json') or args.dataset.endswith('.jsonl'):
        dataset_id = None
        # Load from local json/jsonl file
        dataset = datasets.load_dataset('json', data_files=args.dataset)
        # By default, the "json" dataset loader places all examples in the train split,
        # so if we want to use a jsonl file for evaluation we need to get the "train" split
        # from the loaded dataset
        eval_split = 'train'
        # Map string labels to integers for NLI
        if args.task == 'nli':
            label2id = {'entailment': 0, 'neutral': 1, 'contradiction': 2}
            def encode_label(example):
                example['label'] = label2id[example['label']]
                return example
            dataset = dataset.map(encode_label)
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
    if training_args.do_train:
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
            print(f"{dataset=}")
            train_dataset = dataset["train"]

        if args.max_train_samples:
            train_dataset = train_dataset.select(range(args.max_train_samples))
        train_dataset_featurized = train_dataset.map(
            prepare_train_dataset,
            batched=True,
            num_proc=NUM_PREPROCESSING_WORKERS,
            remove_columns=train_dataset.column_names
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


        # eval_dataset = dataset[eval_split]
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


if __name__ == "__main__":
    main()
