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
from itertools import product
from datetime import datetime
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
from making_sense_zoy import DEBUG

os.environ['TF_CPP_MIN_LOG_LEVEL'] = '0'
ORI = "original"

# Key: orig_label;1st_trans;2nd_trans, value: index of the rule
# * means the rule could apply to all orig_label, and final_label is the same
snli_rules_old = {
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

# Key: orig_label;1st_trans;2nd_trans, value: rule_id
snli_rules = {
    # original -> sanity check
    f"{ORI};{ORI};{ORI}": "0_orig",

    # tense change -> neutral
    "*;past simple;future simple": "1a_double",
    "*;future simple;past simple": "1b_double",
    f"*;past simple;{ORI}": "1a_lhs",
    f"*;{ORI};future simple": "1a_rhs",
    f"*;future simple;{ORI}": "1b_lhs",
    f"*;{ORI};past simple": "1b_rhs",

    # modality change -> neutral
    f"*;may;{ORI}": "2a_lhs",
    f"*;{ORI};modality: may": "2a_rhs",
    "*;may;may": "3_double",

    # double modality changes -> neutral
    "entailment;may;may": "3a",
    "contradiction;may;may": "3b",

    # negation change -> flip label
    # entailment <-> contradiction, neutral <-> neutral
    f"entailment;{ORI};negation": "neg_hyp_e2c",
    f"contradiction;{ORI};negation": "neg_hyp_c2e",
    f"neutral;{ORI};negation": "neg_hyp_n2n",

    # passive change -> same as original
    f"*;passive: ARG2;{ORI}": "pass_lhs",
    f"*;{ORI};passive: ARG2": "pass_rhs",
    "*;passive: ARG2;passive: ARG2": "pass_double",

    # it cleft change -> same as original
    f"*;it cleft: ARG1;{ORI}": "cleft1_lhs",
    f"*;{ORI};it cleft: ARG1": "cleft1_rhs",
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

def select_best(data, model, tokenizer, predictor, top_k=0):
    """
    Selects candidates for each variation.
    - If top_k <= 0: Disable LLM filtering, keeps ALL candidates.
    - If num_candidates <= top_k: Keeps ALL candidates (no scoring).
    - If num_candidates > top_k:  Scores them and keeps the top k.
    Preserves all other keys.
    """
    cleaned_data = []
    for idx, entry in enumerate(data):
        cleaned_entry = defaultdict(lambda: defaultdict(list))

        # Keep all other key value pairs
        for key, val in entry.items():
            if key not in ["sentence1", "sentence2"]:
                cleaned_entry[key] = val

        for sent in ["sentence1", "sentence2"]:
            if sent not in entry: continue

            val = entry[sent]

            # If it is NOT a dictionary, it cannot have variations. Treat as plain text.
            if not isinstance(val, dict):
                surface = val[0] if isinstance(val, list) and len(val) > 0 else str(val)
                # Save as a dict to be consistent with 'original' structure
                cleaned_entry[sent][ORI] = {'surface': surface}
                continue

            # It is a dict, so we can iterate keys
            for form, results in val.items():
                if not results: continue

                # Preserve original mrs
                if form == ORI:
                    if isinstance(results, list) and len(results) > 0 and isinstance(results[0], dict):
                        cleaned_entry[sent][ORI] = results[0]
                    elif isinstance(results, dict):
                        cleaned_entry[sent][ORI] = results
                    else:
                        # Fallback for strings in list or raw string
                        s = results[0] if isinstance(results, list) else str(results)
                        cleaned_entry[sent][ORI] = {'surface': s}
                    continue

                # Filter variations
                candidates = []
                if isinstance(results, list):
                    candidates = [r["surface"] if isinstance(r, dict) else str(r) for r in results]
                elif isinstance(results, str):
                    candidates = [results]

                # Remove empty strings
                candidates = [c for c in candidates if c]
                if not candidates: continue

                # Conditional Filtering
                if DEBUG: print(f"\nZoy Debug: form={form}")
                if top_k is not None and top_k <= 0:
                    # Disable LLM filtering entirely: keep ALL candidates, do NOT call predictor()
                    final_candidates = candidates
                else:
                    # Normal behavior: only score if we have more than top_k candidates
                    if len(candidates) <= top_k:
                        # If we have fewer than (or equal to) K candidates, keep them ALL. No LLM scoring needed.
                        final_candidates = candidates
                    else:
                        scores = [predictor(c, model, tokenizer) for c in candidates]
                        # Get indices of top K scores (descending order)
                        top_indices = np.argsort(scores)[-top_k:][::-1]
                        final_candidates = [candidates[i] for i in top_indices]
                cleaned_entry[sent][form] = final_candidates
        cleaned_data.append(cleaned_entry)
        if DEBUG: print(f"Zoy Debug: processed {idx} out of {len(data)}", end="\r")
    return cleaned_data

def get_new_label(old_label, rule_id):
    """
    Determines the new label based on the linguistic transformation rule.
    """
    # 0. Original
    if rule_id == "0_orig":
        return old_label

    # 1, 2, 3: Tense / Modality -> usually breaks entailment to Neutral
    if rule_id.startswith("1") or rule_id.startswith("2") or rule_id.startswith("3"):
        return "neutral"

    # 4, 5: Structural (Passive/Cleft) -> Preserves meaning
    if rule_id.startswith("4") or rule_id.startswith("5"):
        return old_label

    # Negation -> Flip
    if rule_id.startswith("neg"):
        if old_label == "entailment": return "contradiction"
        if old_label == "contradiction": return "entailment"
        if old_label == "neutral": return "neutral"

    # Compositional (7, 8, 9) -> Usually Neutral if they involve Tense/Modality
    if rule_id.startswith("7") or rule_id.startswith("8") or rule_id.startswith("9"):
        return "neutral"

    return old_label

def apply_rules(cleaned_data, rules):
    final_data = []

    for idx, entry in enumerate(cleaned_data):
        label = entry.get("gold_label")
        sent1 = entry.get("sentence1")
        sent2 = entry.get("sentence2")

        if not isinstance(sent1, dict) or not isinstance(sent2, dict): continue

        # Extract Original Surfaces (Anchors)
        s1_obj = sent1.get(ORI)
        s2_obj = sent2.get(ORI)
        if not s1_obj or not s2_obj: continue

        s1_orig = s1_obj['surface'] if isinstance(s1_obj, dict) else str(s1_obj)
        s2_orig = s2_obj['surface'] if isinstance(s2_obj, dict) else str(s2_obj)

        # Base Metadata to copy to all generated items
        base_metadata = {k: v for k, v in entry.items() if k not in ["sentence1", "sentence2", "0"]}

        # --- MRS CHECKING (For Tense Rules) ---
        mrs1, mrs2 = None, None
        try:
            if isinstance(s1_obj, dict) and 'mrs' in s1_obj:
                mrs1 = simplemrs.decode(s1_obj['mrs']) if isinstance(s1_obj['mrs'], str) else mrsjson.from_dict(s1_obj['mrs'])
            if isinstance(s2_obj, dict) and 'mrs' in s2_obj:
                mrs2 = simplemrs.decode(s2_obj['mrs']) if isinstance(s2_obj['mrs'], str) else mrsjson.from_dict(s2_obj['mrs'])
        except Exception: pass

        # Iterate over all defined rules
        for rule_str, ridx in rules.items():
            parts = rule_str.split(";")
            if len(parts) != 3: continue
            orig_label_req, trans1_req, trans2_req = parts

            # 1. Filter by Label Requirement
            if orig_label_req != "*" and orig_label_req != label:
                continue

            # 2. Filter by Tense (Specific to Rule 1)
            if ridx.startswith("1"):
                if not mrs1 or not mrs2: continue
                # Rule 1 assumes Present -> Past/Future. If input isn't Present, skip.
                if get_tense(mrs1) != "present" or get_tense(mrs2) != "present":
                    continue

            # 3. Find Candidates for Sentence 1
            s1_candidates = []
            if trans1_req == ORI:
                s1_candidates = [s1_orig]
            else:
                # Check if any key in sent1 (e.g. "past simple") contains the req
                reqs = trans1_req.split("+")
                for k1, val1 in sent1.items():
                    if k1 != ORI and all(r in k1 for r in reqs):
                        # val1 is either a string or a list of strings (from select_best)
                        if isinstance(val1, list): s1_candidates.extend(val1)
                        else: s1_candidates.append(str(val1))
                        # Note: We don't break here because we want ALL matching variations
                        # e.g. if there are multiple 'passive' keys? Usually only one per type though.
                        break

            # 4. Find Candidates for Sentence 2
            s2_candidates = []
            if trans2_req == ORI:
                s2_candidates = [s2_orig]
            else:
                reqs = trans2_req.split("+")
                for k2, val2 in sent2.items():
                    if k2 != ORI and all(r in k2 for r in reqs):
                        if isinstance(val2, list): s2_candidates.extend(val2)
                        else: s2_candidates.append(str(val2))
                        break

            # 5. Generate Combinations
            if s1_candidates and s2_candidates:
                calculated_label = get_new_label(label, ridx)

                # Cartesian Product: (S1_a, S1_b) x (S2_a, S2_b) => 4 pairs
                for s1_text, s2_text in product(s1_candidates, s2_candidates):
                    if not s1_text or not s2_text: continue

                    new_item = base_metadata.copy()
                    new_item.update({
                        "gold_label": calculated_label,
                        "sentence1": s1_text,
                        "sentence2": s2_text,
                        "rule": ridx
                    })
                    final_data.append(new_item)

    return final_data

def read_jsonl(filepath: str):
    ret = []
    assert ".jsonl" in filepath
    if DEBUG: print(f"Zoy Debug: reading from: {filepath}")
    with open(filepath, "r") as f:
        for line in f:
            if line == "":
                continue
            ret.append(json.loads(line))
    return ret

def write_jsonl(final_data, output_path):
    count = 0
    LABEL_MAP = {"entailment": 0, "neutral": 1, "contradiction": 2}
    with open(output_path, 'w') as f:
        for item in final_data:
            if item["gold_label"] not in LABEL_MAP: continue
            out_json_line = {
                "premise": item["sentence1"],
                "hypothesis": item["sentence2"],
                "label": LABEL_MAP[item["gold_label"]],
                "rule": item["rule"]
            }
            f.write(json.dumps(out_json_line) + '\n')
            count += 1
    if DEBUG: print(f"Zoy Debug: wrote {count} records to {output_path}")

def wirte_to_text(cleaned_data, output_dir):
    with open(os.path.join(output_dir, "samples.txt"), "w") as file:
        for i, d in enumerate(cleaned_data):
            file.write("data: " + str(i) + "\n")
            for sent in ["sentence1", "sentence2"]:
                file.write(sent + "\n" + d[sent][ORI] + "\n\n")
                for k, v in d[sent].items():
                    if k != ORI:
                        file.write(k + ": \n" + v + "\n\n")

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
    parser = argparse.ArgumentParser("Process ACE ERG generated data to augmented datasets.")
    # python3 post-process/process_zoy.py --data_path datasets/dev/ace_erg_transfer_train_only_3_lines.jsonl --output_dir datasets/dev_zoy --task snli --model_path ../../models/gpt-oss-20b/gpt-oss-20b-Q4_K_M.gguf
    # Required parameters
    parser.add_argument(
        "--data_path",
        default=None,
        type=str,
        required=True,
        help="The path to the jsonl file containing original data and possible transformations.",
    )
    parser.add_argument(
        "--output_dir",
        default=None,
        type=str,
        required=True,
        help="The output directory to put processed jsonl data files.",
    )
    # Other parameters
    parser.add_argument(
        "--model_type",
        default="gguf",
        type=str,
        help="Type of the model used to select best sentence in a category, choose from gpt, gpt2, bert, roberta, xlnet, gguf. Default is gguf.",
    )
    parser.add_argument(
        "--model_path",
        default="gpt-oss-20b.gguf",
        type=str,
        help="Model file path used to select best sentence in a category, e.g. ../../models/gpt-oss-20b/gpt-oss-20b-Q4_K_M.gguf",
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
    parser.add_argument(
        "--keep_top_k",
        default=0,
        type=int,
        help="Number of best variations to keep, default is 0, which disables this feature.",
    )
    parser.add_argument(
        "--debug",
        action="store_true",
        help="Enable debug print() output.",
    )


    SPLITS = ["test", "dev", "train"]

    args = parser.parse_args()
    DEBUG = args.debug

    # Decide whether to load LLM model at all
    use_llm_model = args.keep_top_k is not None and args.keep_top_k > 0
    model = None
    tokenizer = None
    predictor = None

    if use_llm_model:
        # Load Model to select best candidate
        if args.model_type not in MODEL_CONFIGS:
            raise ValueError(f"Model type {args.model_type} not found in MODEL_CONFIGS")

        model_class, predictor = MODEL_CONFIGS[args.model_type]

        if args.model_type == "gguf":
            tokenizer = None # GGUF has internal tokenizer
            model = model_class(
                model_path=args.model_path,
                n_gpu_layers=-1, # all layers on GPU
                n_ctx=8192, # limit memory usage by reducing context to 8k instead of 128k
                logits_all=True, # calculating log-likelihood score of the tokens needs full logit extraction
                verbose=False
            )
        else:
            tokenizer = AutoTokenizer.from_pretrained(os.path.basename(args.model_path))
            # Fix padding token issues for Llama/Mistral
            if tokenizer.pad_token is None: tokenizer.pad_token = tokenizer.eos_token
            model = model_class.from_pretrained(
                args.model_path,
                torch_dtype=torch.float16,
                device_map="auto"
            )
            model.to("cuda")
            model.eval()
    else:
        if DEBUG: print("Zoy Debug: keep_top_k <= 0, therefore disabling LLM model loading and filtering.")

    if os.path.isdir(args.data_path):
        paths = [os.path.join(args.data_path, filename) for filename in os.listdir(args.data_path)][::-1]
    else:
        paths = [args.data_path]

    os.makedirs(args.output_dir, exist_ok=True)

    for path in paths:
        timestamp = datetime.now().strftime("%Y%m%d%H%M%S")
        result_filename = f"augmented_{args.task}_{timestamp}.jsonl"
        for s in SPLITS:
            if s in path:
                result_filename = f"augmented_{s}_{timestamp}.jsonl"
                break

        raw_data = read_jsonl(path)
        if args.sample > 0: raw_data = sample(raw_data, args.sample)
        if DEBUG: print(f"Zoy Debug: filtering {result_filename} ({len(raw_data)} items) with {args.model_type}\n")
        if DEBUG: print(f"Zoy Debug: ace-erg raw data: {raw_data}\n")

        # Filter best sentences with LLM top-k scoring
        cleaned_data = select_best(raw_data, model, tokenizer, predictor, top_k=args.keep_top_k)
        if DEBUG: print(f"\nZoy Debug: cleaned best data: {cleaned_data}\n")

        # Apply logic rules to generate label
        final_data = apply_rules(cleaned_data, ALL_RULES[args.task])
        if DEBUG: print(f"Zoy Debug: applied rules final data: {final_data}\n")

        # Save JSONL results
        output_path = os.path.join(args.output_dir, result_filename)
        write_jsonl(final_data, output_path)
        print(f"All done!")

if __name__ == "__main__":
    main()
