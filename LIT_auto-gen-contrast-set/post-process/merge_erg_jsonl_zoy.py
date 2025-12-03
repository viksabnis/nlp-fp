import json
import os
import sys
import argparse
from collections import defaultdict
from tqdm import tqdm

def get_surface(sentence_data):
    """
    Robustly extract the raw surface string from sentence data
    that might be a string, list, or dictionary.
    """
    if not sentence_data or 'original' not in sentence_data:
        return None

    raw = sentence_data['original']

    # Case 1: It's a simple string
    if isinstance(raw, str):
        return raw

    # Case 2: It's a list (e.g., ["The dog runs"] or [{"surface": "..."}])
    if isinstance(raw, list) and len(raw) > 0:
        item = raw[0]
        if isinstance(item, str):
            return item
        if isinstance(item, dict) and 'surface' in item:
            return item['surface']

    # Case 3: It's a dict (e.g., {"surface": "...", "mrs": "..."})
    if isinstance(raw, dict) and 'surface' in raw:
        return raw['surface']

    return None

def get_fingerprint(item):
    """
    Creates a unique hashable key for the item based on strict identity fields.
    """
    pid = item.get('pairID')
    cid = item.get('captionID')
    label = item.get('gold_label')

    s1_surf = get_surface(item.get('sentence1', {}))
    s2_surf = get_surface(item.get('sentence2', {}))

    if not pid or not cid or not label or not s1_surf or not s2_surf:
        return None

    # The Fingerprint: (PairID, CaptionID, Label, Premise_Text, Hypothesis_Text)
    return (str(pid), str(cid), str(label), s1_surf.strip(), s2_surf.strip())

def merge_sentence_block(target_sent, source_sent):
    """
    Merges variations from source into target.
    Prioritizes keeping MRS data in 'original' if present.
    """
    for key, val in source_sent.items():
        # 1. Handle 'original' carefully to preserve MRS
        if key == 'original':
            if 'original' not in target_sent:
                target_sent['original'] = val
            else:
                # If target is just a string/list of strings, but source has MRS (dict), take source
                target_raw = target_sent['original']
                source_raw = val

                target_has_mrs = False
                if isinstance(target_raw, list) and len(target_raw) > 0 and isinstance(target_raw[0], dict) and 'mrs' in target_raw[0]:
                    target_has_mrs = True
                elif isinstance(target_raw, dict) and 'mrs' in target_raw:
                    target_has_mrs = True

                source_has_mrs = False
                if isinstance(source_raw, list) and len(source_raw) > 0 and isinstance(source_raw[0], dict) and 'mrs' in source_raw[0]:
                    source_has_mrs = True
                elif isinstance(source_raw, dict) and 'mrs' in source_raw:
                    source_has_mrs = True

                # Overwrite if source has MRS and target does not
                if source_has_mrs and not target_has_mrs:
                    target_sent['original'] = val

        # 2. Merge all other variations (negation, passive, etc.)
        elif key not in target_sent:
            target_sent[key] = val
        else:
            # If both have the same variation, keep existing to avoid duplicates.
            pass

def merge_files(file_paths, output_file):
    merged_db = {} # Key: Fingerprint, Value: Item

    total_read = 0
    merged_count = 0
    new_count = 0

    # Validate inputs
    valid_paths = [p for p in file_paths if os.path.exists(p)]
    if len(valid_paths) < len(file_paths):
        print(f"Warning: {len(file_paths) - len(valid_paths)} input files were not found and will be skipped.")

    for fpath in valid_paths:
        print(f"Processing {fpath}...")
        with open(fpath, 'r') as f:
            for line in tqdm(f):
                if not line.strip(): continue
                try:
                    item = json.loads(line)
                    total_read += 1

                    key = get_fingerprint(item)
                    if not key:
                        continue # Skip broken items

                    if key in merged_db:
                        # MERGE: Existing item found
                        existing = merged_db[key]

                        # Merge sentence 1 variations
                        if 'sentence1' in item:
                            if 'sentence1' not in existing: existing['sentence1'] = {}
                            merge_sentence_block(existing['sentence1'], item['sentence1'])

                        # Merge sentence 2 variations
                        if 'sentence2' in item:
                            if 'sentence2' not in existing: existing['sentence2'] = {}
                            merge_sentence_block(existing['sentence2'], item['sentence2'])

                        merged_count += 1
                    else:
                        # NEW: Add to DB
                        merged_db[key] = item
                        new_count += 1

                except json.JSONDecodeError:
                    continue

    print(f"\nTotal lines processed: {total_read}")
    print(f"Unique items (Final Count): {len(merged_db)}")
    print(f"Merges performed (Intersections): {merged_count}")

    # Ensure output dir exists
    output_dir = os.path.dirname(output_file)
    if output_dir and not os.path.exists(output_dir):
        os.makedirs(output_dir)

    print(f"Writing to {output_file}...")
    with open(output_file, 'w') as f:
        for item in merged_db.values():
            f.write(json.dumps(item) + '\n')

    print("Done.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Merge multiple ERG-generated JSONL files by fingerprint.")
    parser.add_argument(
        "--merge_from",
        nargs='+',
        required=True,
        help="List of input JSONL files to merge. Supports wildcards via shell expansion."
    )
    parser.add_argument(
        "--merge_into",
        type=str,
        required=True,
        help="Path to the destination output JSONL file."
    )
    args = parser.parse_args()
    merge_files(args.merge_from, args.merge_into)
