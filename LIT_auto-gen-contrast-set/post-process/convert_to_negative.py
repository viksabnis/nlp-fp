from datasets import load_dataset, Dataset
import pandas as pd # Used only for demonstration/verification
from pandas import json_normalize

# 1. Define the path to your JSON Lines file
# file_path = "/usr/local/google/home/viksabnis/LIT_auto-gen-contrast-set/datasets/aug_snli_1.0/aug_snli_1.0_train_00.jsonl" # Replace with your actual file path
# file_path_dir = "/usr/local/google/home/viksabnis/LIT_auto-gen-contrast-set/datasets/aug_snli_1.0/" # Replace with your actual file path
# file_path_dir = "/usr/local/google/home/viksabnis/LIT_auto-gen-contrast-set/datasets/with30_records/" # Replace with your actual file path
file_path_dir = "./aug_snli/" # Replace with your actual file path

import json
import pandas as pd
import os
import multiprocessing

def extract_negation_pairs_from_jsonl(file_path):
    """
    Reads a JSONL file and extracts the gold_label, pairID,
    and the first negation sentence from sentences1 and sentences2.
    """
    extracted_data = []

    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            for line_number, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                try:
                    record = json.loads(line)
                    s1_original = record.get('sentence1', {}).get('original', [])
                    original_1 = s1_original[0] if s1_original else record.get('sentence1')
                    # Safely access the first negation sentence from sentence1
                    # s1_negations = record.get('sentence1', {}).get('negation', None)
                    # s1_itclefts_arg1 = record.get('sentence1', {}).get('it cleft: ARG1', None)
                    # s1_passive_arg1 = record.get('sentence1', {}).get('passive: ARG2', None)
                    # s1_subjswap_arg1 = record.get('sentence1', {}).get('swap subj/obj', None)
                    # We take the first negation sentence for the pair
                    # negation1 = s1_negations[0] if s1_negations else None
                    # itclefts_arg1_1 = s1_itclefts_arg1[0] if s1_itclefts_arg1 else None
                    # passive_arg1_1 = s1_passive_arg1[0] if s1_passive_arg1 else None
                    # subjswap_arg1 = s1_subjswap_arg1[0] if s1_subjswap_arg1 else None

                    # s2_original = record.get('sentence2', {}).get('original', [])
                    # original_2 = s2_original[0] if s2_original else record.get('sentence2')
                    # print(s2_original)
                    # print(original_2)

                    # Safely access the first negation sentence from sentence2
                    # s2_negations = record.get('sentence2', {}).get('negation', None)
                    # s2_itclefts_arg1 = record.get('sentence2', {}).get('it cleft: ARG1', None)
                    # s2_passive_arg1 = record.get('sentence2', {}).get('passive: ARG2', None)
                    s2_subjswap_arg1 = record.get('sentence2', {}).get('swap subj/obj', None)

                    # negation2 = s2_negations[0] if s2_negations else None
                    # itclefts_arg1_2 = s2_itclefts_arg1[0] if s2_itclefts_arg1 else None
                    # passive_arg1_2 = s2_passive_arg1[0] if s2_passive_arg1 else None
                    subjswap_arg2 = s2_subjswap_arg1[0] if s2_subjswap_arg1 else None

                    # Only add the record if we successfully extracted a pair
                    # if negation1 is not None and negation2 is not None:
                    # if itclefts_arg1_1 is not None and itclefts_arg1_2 is not None:
                    # if subjswap_arg1 is not None and subjswap_arg2 is not None:
                    if subjswap_arg2 is not None :
                        extracted_data.append({
                            'id': record.get('pairID'),
                            'label': record.get('gold_label'),
                            'premise': original_1,
                            'hypothesis': subjswap_arg2
                        })

                except json.JSONDecodeError as e:
                    print(f"Warning: Skipping line {line_number} due to JSON decoding error: {e}")
                except Exception as e:
                    print(f"Warning: Skipping line {line_number} due to extraction error: {e}")

    except FileNotFoundError:
        print(f"Error: File not found at {file_path}")
        return pd.DataFrame()

    return pd.DataFrame(extracted_data)

# --- Example Usage ---
# file_path = "data.jsonl"


# The resulting DataFrame (df_negations) contains the extracted pairs:
# | pairID | gold_label | negation1 | negation2 |
# | :--- | :--- | :--- | :--- |
# | 3416050480.jpg#4r1n | neutral | No person on a horse jumps over... | No person is training his horse... |
# 2. Use load_dataset to create the Dataset object
# 'json' tells the function how to interpret the file
# data_files specifies the path
try:
    num_division = 64
    # dfs = []
    # parallel_inputs = [f"aug_snli_1.0_train_0{i}.jsonl" for i in range(num_division)]
    parallel_inputs = [f"aug_snli_1.0_train_{i:03d}.jsonl" for i in range(num_division)]
    #
    # target_file_name = file_path_dir + "negations_only.jsonl"
    # target_file_name = file_path_dir + "itclefts_s1.jsonl"
    # target_file_name = file_path_dir + "passive_s1.jsonl"
    # target_file_name = file_path_dir + "subj_obj_swap_s1.jsonl"
    # target_file_name = file_path_dir + "itclefts_s2.jsonl"
    # target_file_name = file_path_dir + "passive_s2.jsonl"
    target_file_name = file_path_dir + "subj_obj_swap_s2.jsonl"
    with open(target_file_name, 'a') as outfile:
        outfile.truncate()

    for file_name in parallel_inputs:
        file_path = file_path_dir + file_name
        df_negations = extract_negation_pairs_from_jsonl(file_path)
        if len(df_negations) != 0:
        # df_negations.to_json(target_file_name, append=True)
            with open(target_file_name, 'a') as outfile:
                outfile.write(df_negations.to_json(orient="records", lines=True))


        #     for aug_datum in aug_data:
        #         json.dump(aug_datum, outfile)
        #         outfile.write('\n')

        # dfs.append(df_negations)
    # df = extract_negation_pairs_from_jsonl(file_path)
    # df_nested = pd.read_json(file_path, lines=True)

    # sentence1_df = json_normalize(
    #     data=df_nested,
    #     record_path = "sentence1",
    #     # These are the columns from the original DataFrame to include
    #     meta=['pairID', 'gold_label', 'captionID'],
    #     # Use the original DataFrame to provide the meta data
    #     meta_prefix='parent_',
    #     record_prefix='',
    #     # Set the separator for nested column names
    #     sep='_'
    # )
    # sentence2_df = json_normalize(
    #     data=df_nested,
    #     # These are the columns from the original DataFrame to include
    #     record_path = "sentence2",
    #     meta=['pairID'],
    #     # Use the original DataFrame to provide the meta data
    #     meta_prefix='parent_',
    #     record_prefix='',
    #     # Set the separator for nested column names
    #     sep='_'
    # )
    # df_merged = pd.merge(
    #     sentence1_df,
    #     sentence2_df,
    #     on='parent_pairID',
    #     how='outer',
    #     suffixes=('_item', '_tag')
    # )
    # df_flattened = df_flattened.set_index(df_nested.index).assign(
    #     pairID=df_nested['pairID'],
    #     gold_label=df_nested['gold_label']
    #     captionID = df_nested['captionID']
    # )
    # dataset = load_dataset("json", data_files=file_path)

    # By default, load_dataset creates a 'train' split if no split is specified.
    # We access the resulting Dataset object:
    # dataset = Dataset.from_pandas(pd.concat(dfs))
    # print(f"{dataset=}")
    # data_split = dataset['train']
    # data_split = dataset

    # print(f"✅ Successfully loaded {len(data_split)} records.")
    # print("\n--- Dataset Info ---")
    # print(data_split)

    # print("\n--- First 3 Examples (as a Pandas DataFrame for clarity) ---")
    # print(pd.DataFrame(data_split[:3]))
    # dataset.to_json(file_path_dir + "negations.json")


except Exception as e:
    # print(traceback.format_exc())

    print(f"❌ Error loading dataset: {e}")
    print("Please ensure your file exists and is in valid JSON Lines format.")

