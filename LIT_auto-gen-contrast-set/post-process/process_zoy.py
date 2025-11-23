import pickle
import json
import os
import sys
import argparse
import numpy as np
from collections import defaultdict
import torch
import random
from copy import deepcopy
os.environ['TF_CPP_MIN_LOG_LEVEL'] = '2'
from transformers import (
    AutoModelForCausalLM, AutoModelForMaskedLM, AutoTokenizer,
    OpenAIGPTLMHeadModel, OpenAIGPTTokenizer,
    GPT2LMHeadModel, GPT2Tokenizer,
    BertForMaskedLM, BertTokenizer,
    RobertaForMaskedLM, RobertaTokenizer,
    XLNetLMHeadModel, XLNetTokenizer,
)
from delphin.codecs import simplemrs, mrsjson
from llama_cpp import Llama
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from transfer.ergtransfer import get_tense
from making_sense_zoy import uni_predict, bert_predict, ro_predict, xlnet_predict
from making_sense_zoy import score_causal_lm, score_masked_lm, score_gguf
os.environ['TF_CPP_MIN_LOG_LEVEL'] = '0'
ORI = "original"

# Key: orig_label;1st_trans;2nd_trans, value: index of the rule
# * means the rule could apply to all orig_label, and final_label is the same
snli_rules = {
            "entailment;past simple;future simple": "1a",
            "contradiction;future simple;past simple": "1b",
            f"entailment;may;{ORI}": "2a",
            f"contradiction;may;{ORI}": "2b",
            "entailment;may;may": "3a",
            "contradiction;may;may": "3b",
            "*;passive: ARG2;passive: ARG2": "4",
            "*;it cleft: ARG1;it cleft: ARG1": "5",
            # compositional rules (so far we only consider combination of two phenomena)
            "entailment;past simple+it cleft: ARG1;future simple+it cleft: ARG1": "7a",
            "contradiction;future simple+it cleft: ARG1;past simple+it cleft: ARG1": "7b",
            "entailment;past simple+passive: ARG2;future simple+passive: ARG2": "8a",
            "contradiction;future simple+passive: ARG2;past simple+passive: ARG2": "8b",
            "entailment;modality: may+passive: ARG2;modality: may+passive: ARG2": "9a",
            "contradiction;modality: may+passive: ARG2;modality: may+passive: ARG2": "9b"
}

mnli_rules = {
    # basic rules
    "entailment;past simple;future simple": "1a",
    "contradiction;future simple;past simple": "1b",
    f"entailment;may;{ORI}": "2a",
    f"contradiction;may;{ORI}": "2b",
    "entailment;may;may": "3a",
    "contradiction;may;may": "3b",
    "*;passive: ARG2;passive: ARG2": "4",
    "*;it cleft: ARG1;it cleft: ARG1": "5",
    # compositional rules (so far we only consider combination of two phenomena)
    "entailment;past simple+it cleft: ARG1;future simple+it cleft: ARG1": "7a",
    "contradiction;future simple+it cleft: ARG1;past simple+it cleft: ARG1": "7b",
    "entailment;past simple+passive: ARG2;future simple+passive: ARG2": "8a",
    "contradiction;future simple+passive: ARG2;past simple+passive: ARG2": "8b",
    "entailment;modality: may+passive: ARG2;modality: may+passive: ARG2": "9a",
    "contradiction;modality: may+passive: ARG2;modality: may+passive: ARG2": "9b"
}

preserving_rule_types = ["cleft", "passive"]
changing_rule_type = ["past", "future", "may"]

sts_rules = {}

tc_rules = {}

ALL_RULES = {
            "snli": snli_rules,
            "mnli": mnli_rules,
            "sts": sts_rules,
            "tc": tc_rules,
}

MODEL_CLASSES = {
            "gpt": (OpenAIGPTLMHeadModel, OpenAIGPTTokenizer, uni_predict),
            "gpt2": (GPT2LMHeadModel, GPT2Tokenizer, uni_predict),
            "bert": (BertForMaskedLM, BertTokenizer, bert_predict),
            "roberta": (RobertaForMaskedLM, RobertaTokenizer, ro_predict),
            "xlnet": (XLNetLMHeadModel, XLNetTokenizer, xlnet_predict),
}

# Modern way of loading models
MODEL_CONFIGS = {
    # Causal LMs
    "mistral": (AutoModelForCausalLM, score_causal_lm),
    "llama":   (AutoModelForCausalLM, score_causal_lm),
    "gpt2":    (AutoModelForCausalLM, score_causal_lm),
    # Masked LMs
    "bert":    (AutoModelForMaskedLM, score_masked_lm),
    "roberta": (AutoModelForMaskedLM, score_masked_lm),
    "modernbert": (AutoModelForMaskedLM, score_masked_lm),
    # GGUF LMs
    "gguf":    (Llama, score_gguf),
}

def sample(data, sample):
    if sample <= 0 or sample > len(data):
        return data
    random.shuffle(data)
    return data[:sample]

def select_best(data, model, tokenizer, predictor):
    cleaned_data = []
    for idx, entry in enumerate(data):
        cleaned_entry = defaultdict(lambda: defaultdict(str))
        cleaned_entry["gold_label"] = entry["gold_label"]

        for sent in ["sentence1", "sentence2"]:
            if sent not in entry: continue

            # Handle legacy string inputs (no variations)
            if isinstance(entry[sent], str):
                cleaned_entry[sent][ORI] = {'surface': entry[sent]}
                continue

            for form, results in entry[sent].items():
                if not results: continue

                if form == ORI:
                    # Case 1: It's a list containing a dict (Ideal case from generator)
                    if isinstance(results, list) and len(results) > 0 and isinstance(results[0], dict):
                        cleaned_entry[sent][ORI] = results[0]
                    # Case 2: It's already a dict
                    elif isinstance(results, dict):
                        cleaned_entry[sent][ORI] = results
                    # Case 3: It's a list of strings (Backup: we lost MRS, but keep surface)
                    elif isinstance(results, list) and len(results) > 0:
                         cleaned_entry[sent][ORI] = {'surface': str(results[0])}
                    # Case 4: It's a simple string
                    elif isinstance(results, str):
                         cleaned_entry[sent][ORI] = {'surface': results}
                    continue

                candidates = []
                if isinstance(results, list):
                    # Extract string from dict if needed
                    candidates = [r["surface"] if isinstance(r, dict) else str(r) for r in results]
                elif isinstance(results, dict) and "surface" in results:
                     candidates = [results["surface"]]
                elif isinstance(results, str):
                     candidates = [results]

                if not candidates: continue

                if len(candidates) > 1:
                    scores = [predictor(r, model, tokenizer) for r in candidates]
                    best_str = candidates[np.argmax(scores)]
                else:
                    best_str = candidates[0]

                cleaned_entry[sent][form] = best_str

        cleaned_data.append(cleaned_entry)
        print("processed " + str(idx) + "/" + str(len(data)), end="\r")
    return cleaned_data

def wirte_readable_text(cleaned_data, output_dir):
    with open(os.path.join(output_dir, "samples.txt"), "w") as file:
        for i, d in enumerate(cleaned_data):
            file.write("data: " + str(i) + "\n")
            for sent in ["sentence1", "sentence2"]:
                file.write(sent + "\n" + d[sent][ORI] + "\n\n")
                for k, v in d[sent].items():
                    if k != ORI:
                        file.write(k + ": \n" + v + "\n\n")

def apply_rules(cleaned_data, rules):
    final_data = []
    for idx, entry in enumerate(cleaned_data):
        final_entry = {}
        label = entry["gold_label"]
        sent1 = entry["sentence1"]
        sent2 = entry["sentence2"]

        if not isinstance(sent1, dict) or not isinstance(sent2, dict): continue
        if ORI not in sent1 or ORI not in sent2: continue

        # Robust extraction of surface text
        s1_obj = sent1[ORI]
        s2_obj = sent2[ORI]

        s1_orig = s1_obj['surface'] if isinstance(s1_obj, dict) else str(s1_obj)
        s2_orig = s2_obj['surface'] if isinstance(s2_obj, dict) else str(s2_obj)

        if not isinstance(s1_orig, str) or not isinstance(s2_orig, str):
            continue

        final_entry["0"] = "\t".join([label, s1_orig, s2_orig])
        if "genre" in entry:
            final_entry["genre"] = entry["genre"]

        # Attempt to load MRS for tense rules
        mrs1, mrs2 = None, None
        try:
            if isinstance(s1_obj, dict) and 'mrs' in s1_obj:
                mrs1 = simplemrs.decode(s1_obj['mrs'])
            if isinstance(s2_obj, dict) and 'mrs' in s2_obj:
                mrs2 = simplemrs.decode(s2_obj['mrs'])
        except Exception:
            pass # Just ignore MRS errors

        for rule_str, ridx in rules.items():
            parts = rule_str.split(";")
            if len(parts) != 3: continue
            orig_label_req, trans1_req, trans2_req = parts

            # 1. Check Label Constraint
            new_label = label
            if orig_label_req == "*":
                pass
            elif orig_label_req == label:
                new_label = "neutral"
            else:
                continue

            # 2. Check Tense Constraint (Only if MRS is available)
            if ridx in ["1a", "1b"]:
                # If we don't have MRS, we MUST skip this rule to be safe
                if not mrs1 or not mrs2: continue
                if get_tense(mrs1) != "present" or get_tense(mrs2) != "present":
                    continue

            # 3. Find Matching Transformations
            match1 = None
            if trans1_req == ORI:
                match1 = ORI
            else:
                reqs = trans1_req.split("+")
                for k1 in sent1.keys():
                    if k1 != ORI and all(r in k1 for r in reqs):
                        match1 = k1
                        break

            match2 = None
            if trans2_req == ORI:
                match2 = ORI
            else:
                reqs = trans2_req.split("+")
                for k2 in sent2.keys():
                    if k2 != ORI and all(r in k2 for r in reqs):
                        match2 = k2
                        break

            # 4. If both found, add to entry
            if match1 and match2:
                s1_text = sent1[match1] if match1 != ORI else s1_orig
                s2_text = sent2[match2] if match2 != ORI else s2_orig

                # Ensure we aren't adding empty strings
                if s1_text and s2_text:
                    final_entry[ridx] = "\t".join([new_label, s1_text, s2_text])

        # Only save if we actually generated a contrast set (more than just "0")
        if len(final_entry) > (2 if "genre" in final_entry else 1):
            final_data.append(final_entry)

    return final_data

def read_jsonl(filepath: str):
    ret = []
    assert ".jsonl" in filepath
    print(f"Reading from: {filepath}")
    with open(filepath, "r") as f:
        for line in f:
            if line == "":
                continue
            ret.append(json.loads(line))
    return ret

def write_to_file(final_data, output_dir, divide_data):
    random.shuffle(final_data)
    if divide_data == "train":
        pickle.dump(final_data, open(os.path.join(output_dir, "train"), "wb"))
    elif divide_data == "dev":
        pickle.dump(final_data[:int(0.8 * len(final_data))], open(os.path.join(output_dir, "train"), "wb"))
        pickle.dump(final_data[int(0.8 * len(final_data)):], open(os.path.join(output_dir, "dev"), "wb"))
    elif divide_data == "test":
        pickle.dump(final_data[:int(0.8 * len(final_data))], open(os.path.join(output_dir, "train"), "wb"))
        pickle.dump(final_data[int(0.8 * len(final_data)):int(0.9 * len(final_data))], open(os.path.join(output_dir, "dev"), "wb"))
        pickle.dump(final_data[int(0.9 * len(final_data)):], open(os.path.join(output_dir, "test"), "wb"))

def main():
    parser = argparse.ArgumentParser()

    # Required parameters
    parser.add_argument(
        "--data_path",
        default=None,
        type=str,
        required=True,
        help="The path to the .pkl file containing original data and possible transformations.",
    )
    parser.add_argument(
        "--output_dir",
        default=None,
        type=str,
        required=True,
        help="The output directory to put processed data files.",
    )
    
    # Other parameters
    parser.add_argument(
        "--model_type",
        default="gpt2",
        type=str,
        help="Type of the model used to select best sentence in a category, choose from gpt, gpt2, bert, roberta, xlnet.",
    )
    parser.add_argument(
        "--model_name",
        default="gpt2",
        type=str,
        help="Name of the model used to select best sentence in a category.",
    )
    parser.add_argument(
        "--divide_data",
        default="train",
        type=str,
        help="Select from [train, dev, test]. If train, generate train only. If dev, train+dev. If test, all three.",
    )
    parser.add_argument(
        "--sample",
        default=-1,
        type=int,
        help="If true, generate train, dev and test. Else, generate only the first two.",
    )
    parser.add_argument(
        "--write_text",
        default=False,
        type=bool,
        help="Whether to write a readable text file of selected sentences.",
    )
    parser.add_argument(
        "--task",
        default="snli",
        type=str,
        help="One of snli, sts, tc, mnli",
    )
    SPLITS = ["test", "dev", "train"]

    args = parser.parse_args()

    if args.model_type not in MODEL_CONFIGS:
        raise ValueError(f"Model type {args.model_type} not found in MODEL_CONFIGS")

    model_class, predictor = MODEL_CONFIGS[args.model_type]

    if args.model_type == "gguf":
        tokenizer = None # GGUF has internal tokenizer
        model = model_class(
            model_path=args.model_name,
            n_gpu_layers=-1, # all layers on GPU
            n_ctx=8192, # limit memory usage by reducing context to 8k instead of 128k
            logits_all=True, # calculating log-likelihood score of the tokens needs full logit extraction
            verbose=False
        )
    else:
        tokenizer = AutoTokenizer.from_pretrained(args.model_name)
        # Fix padding token issues for Llama/Mistral
        if tokenizer.pad_token is None: tokenizer.pad_token = tokenizer.eos_token
        model = model_class.from_pretrained(
            args.model_name,
            torch_dtype=torch.float16,
            device_map="auto"
        )
        model.to("cuda")
        model.eval()

    if os.path.isdir(args.data_path):
        paths = [os.path.join(args.data_path, filename) for filename in os.listdir(args.data_path)][::-1]
    else:
        paths = [args.data_path]

    os.makedirs(args.output_dir, exist_ok=True)
    os.makedirs(os.path.join(args.output_dir, "basic"), exist_ok=True)
    os.makedirs(os.path.join(args.output_dir, "compositional"), exist_ok=True)

    for path in paths:
        result_filename = "unknown"
        for s in SPLITS:
            if s in path:
                result_filename = s
                break

        raw_data = read_jsonl(path)
        print(f"Filtering {result_filename} ({len(raw_data)} items) with {args.model_type}...")
        print(f"ERG raw data: {raw_data}")

        # 1. Filter best sentences (Run GGUF LM scoring)
        cleaned_data = select_best(raw_data, model, tokenizer, predictor)
        print(f"Cleaned best data: {cleaned_data}")

        # 2. Apply Logic Rules
        final_data = apply_rules(cleaned_data, ALL_RULES[args.task])
        print(f"Applied rules final data: {final_data}")

        # 3. Save Results
        pickle.dump(final_data, open(os.path.join(args.output_dir, result_filename), "wb"))

        # 4. Split Basic vs Compositional
        basic_data, comp_data = [], []
        basic_rules = ["1a", "1b", "2a", "2b", "3a", "3b", "4", "5"]
        comp_rules = ["7a", "7b", "8a", "8b", "9a", "9b"]

        for d in final_data:
            basic_d = {"0": d.get("0")}
            comp_d = {"0": d.get("0")}
            has_basic, has_comp = False, False

            for r in basic_rules:
                if r in d:
                    basic_d[r] = d[r]
                    has_basic = True

            for r in comp_rules:
                if r in d:
                    comp_d[r] = d[r]
                    has_comp = True

            if has_basic: basic_data.append(basic_d)
            if has_comp: comp_data.append(comp_d)

        print(f"Split basic data: {basic_data}")
        print(f"Split compositional data: {comp_data}")
        pickle.dump(basic_data, open(os.path.join(args.output_dir, "basic", result_filename), "wb"))
        pickle.dump(comp_data, open(os.path.join(args.output_dir, "compositional", result_filename), "wb"))

        print(f"All done, saved {len(final_data)} entries to {result_filename} (Basic: {len(basic_data)}, Comp: {len(comp_data)})")

if __name__ == "__main__":
    main()
