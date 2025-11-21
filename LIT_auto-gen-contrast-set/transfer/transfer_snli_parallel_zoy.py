import json
import os
import sys
import copy
import argparse
import subprocess
from tqdm import tqdm
#from transfer import transfer
from ergtransfer import transfer

parser = argparse.ArgumentParser("Generating sentences using ERG")
parser.add_argument("--data_dir", type=str, default=f"{os.getcwd()}/../../datasets/snli_1.0")
parser.add_argument("--target_data_dir", type=str, default=f"{os.getcwd()}/../../datasets/aug_snli_1.0")
parser.add_argument("--tenses", nargs='+', default=['past', 'pres', 'fut'])
parser.add_argument("--modalities", nargs='+', default=['_may_v_modal'])
parser.add_argument("--progs", nargs='+', default=['+', '-'])
parser.add_argument("--grm_path", type=str, default=f"{os.getcwd()}/../../ace-erg/erg-1214-x86-64-0.9.34.dat")
parser.add_argument("--ace_path", type=str, default=f"{os.getcwd()}/../ace-0.9.34-zoy-build/ace")
parser.add_argument("--checkpoint_period", type=int, default=200)
parser.add_argument("--timeout", type=int, default=3)


def read_snli(file_path):
    """

    :param data_dir: path to snli directory
    :return: return a dictionary like <"train": [train examples]>
    """
    extracted_fields = ['gold_label',
                        'sentence1', 'sentence2', 'pairID', 'captionID']
    data = []
    with open(file_path, "r") as f:
        for line in f:
            json_obj = json.loads(line)
            added_obj = {}
            for field in extracted_fields:
                added_obj[field] = json_obj[field]
            data.append(added_obj)
    return data[:3]


def parse_file(x):
    args, filename, workerid = x
    log_file_path = f"{args.target_data_dir}/log_worker_{workerid:02d}.txt"
    f = open(log_file_path, 'w')
    # FLUSH Python's current buffers to avoid mixed order output
    sys.stdout.flush()
    sys.stderr.flush()
    # OS-Level Redirection overrides File Descriptor 1 (stdout) and 2 (stderr) with your file.
    # C binaries like ACE have no choice but to write to your file.
    os.dup2(f.fileno(), 1)
    os.dup2(f.fileno(), 2)
    print(f"Zoy Debug: worker {workerid} started, processing {filename}")
    data = read_snli(f"{args.data_dir}/{filename}")
    statistics = {'unparsed_sentence': 0, "timeout": 0}
    aug_data = []
    target_file_name = f"{args.target_data_dir}/aug_{filename}"

    for i, datum in enumerate(data):
        aug_datum = copy.deepcopy(datum)
        # print(f"Worker: {workerid}, {i}")
        for idx in ['1', '2']:
            sentence = datum[f'sentence{idx}']
            aug_sentence = {'original': sentence}
            transforms = transfer(sentence, args.grm_path, args.ace_path,
                                  timeout=args.timeout,
                                  tenses=args.tenses,
                                  progs=args.progs, perfs=[])
            if transforms is None or len(transforms) == 0:
                statistics["unparsed_sentence"] += 1
                continue
            elif "timeout" in transforms:
                statistics["timeout"] += 1
                continue

            for trans_type in transforms:
                aug_sentence[trans_type] = [t['surface'] for t in transforms[trans_type]]

            aug_datum[f'sentence{idx}'] = aug_sentence
        aug_data.append(aug_datum)

        if (i + 1) % args.checkpoint_period == 0:
            print(f"{i + 1}th datum: Worker {workerid} saving.....")
            with open(target_file_name, 'w') as outfile:
                for aug_datum in aug_data:
                    json.dump(aug_datum, outfile)
                    outfile.write('\n')

    with open(target_file_name, 'w') as outfile:
        for aug_datum in aug_data:
            json.dump(aug_datum, outfile)
            outfile.write('\n')
    with open(f"{args.target_data_dir}/"
              f"parse_stats_{'.'.join(filename.split('.')[:-1])}.json", 'w') as outfile:
        json.dump(statistics, outfile)

    return True


def check_and_split_dataset(data_dir, prefix, split, num_division):
    """
    Checks if ALL split files exist for the given num_division.
    If ANY are missing, it runs the split command to regenerate/overwrite them.
    """
    missing_found = False
    for i in range(num_division):
        expected_file = f"{data_dir}/{prefix}_{split}_{i:02d}.jsonl"
        
        if not os.path.exists(expected_file):
            print(f"Zoy Debug: missing split file detected: {expected_file}")
            missing_found = True
            break
    if not missing_found:
        print(f"Zoy Debug: all {num_division} splits for '{split}' exist. skipping split.")
        return

    original_file = f"{data_dir}/{prefix}_{split}.jsonl"
    if not os.path.exists(original_file):
        print(f"Zoy Debug: original file {original_file} not found! cannot split.")
        exit(1)
    # Command: split -d -a 2 -n l/{num} --additional-suffix=.jsonl {in} {out_prefix}
    # Note: 'split' automatically overwrites existing files of the same name.
    output_prefix = f"{data_dir}/{prefix}_{split}_"
    cmd = [
        "split",
        "-d",                        # Numeric suffixes
        "-a", "2",                   # Suffix length 2 (00, 01...99)
        "-n", f"l/{num_division}",   # Split by line count gracefully
        "--additional-suffix=.jsonl",
        original_file,
        output_prefix
    ]
    try:
        subprocess.run(cmd, check=True)
        print(f"Zoy Debug: successfully generated splits for {split}.")
    except subprocess.CalledProcessError as e:
        print(f"Zoy Debug: error executing split command: {e}")
        exit(1)


if __name__ == "__main__":
    import multiprocessing
    import traceback

    args = parser.parse_args()
    print("Zoy Debug: reading all SNLI 1.0 data splits")
    if not os.path.exists(args.target_data_dir):
        os.mkdir(args.target_data_dir)
    data_file_prefix = "snli_1.0"
    #splits = ["train", "dev", "test"]
    splits = ["test"]
    num_division = 1
    pool = multiprocessing.Pool(processes=num_division)
    for split in tqdm(splits[:1]):
        check_and_split_dataset(args.data_dir, data_file_prefix, split, num_division)
        parallel_inputs = [(args, f"{data_file_prefix}_{split}_{i:02d}.jsonl", i) for i in range(num_division)]
        print(f"Zoy Debug: parallel_inputs={parallel_inputs}")
        try:
            outputs = pool.map(parse_file, parallel_inputs)
            assert all(outputs)
        except Exception as e:
            print(f"Zoy Debug: main process error: {e}")
            traceback.print_exc()
    print("Zoy Debug: All finish")
