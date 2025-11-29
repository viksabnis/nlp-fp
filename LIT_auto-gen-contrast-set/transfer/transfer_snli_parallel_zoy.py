import json
import os
import sys
import copy
import argparse
import subprocess
import traceback
from tqdm import tqdm
from ergtransfer_zoy import transfer
from delphin.ace import ACEParser, ACEGenerator

parser = argparse.ArgumentParser("Generating sentences using ERG")
parser.add_argument("--data_dir", type=str, default=f"{os.getcwd()}/../../datasets/snli_1.0")
parser.add_argument("--target_data_dir", type=str, default=f"{os.getcwd()}/../../datasets/erg_snli_1.0")
parser.add_argument("--tenses", nargs='+', default=['past', 'pres', 'fut'])
parser.add_argument("--modalities", nargs='+', default=['_may_v_modal'])
parser.add_argument("--progs", nargs='+', default=['+', '-'])
parser.add_argument("--grm_path", type=str, default=f"{os.getcwd()}/../../ace-erg/erg-1214-x86-64-0.9.34.dat")
#parser.add_argument("--grm_path", type=str, default=f"{os.getcwd()}/../../ace-erg/erg-2025-x86-64-0.9.34.dat")
parser.add_argument("--ace_path", type=str, default=f"{os.getcwd()}/../ace-0.9.34-binary/ace")
parser.add_argument("--checkpoint_period", type=int, default=10)
parser.add_argument("--timeout", type=int, default=10)
parser.add_argument("--max_sentences_reset_ace_process", type=int, default=10)


def read_snli(file_path):
    extracted_fields = ['gold_label', 'sentence1', 'sentence2', 'pairID', 'captionID']
    data = []
    with open(file_path, "r") as f:
        for line in f:
            try:
                json_obj = json.loads(line)
                s1 = json_obj.get('sentence1', '')
                s2 = json_obj.get('sentence2', '')
                # skip long sentences to prevent ACE hangs
                if len(s1.split()) > 16 or len(s2.split()) > 16:
                    continue
                added_obj = {k: json_obj[k] for k in extracted_fields}
                data.append(added_obj)
            except: continue
    return data


def init_ace(args, workerid):
    print(f"Zoy Debug: Worker {workerid} starting new ACE processes...")
    try:
        ace_parser = ACEParser(
            args.grm_path,
            executable=args.ace_path,
            cmdargs=['--timeout', str(args.timeout), '--disable-generalization']
        )

        ace_generator = ACEGenerator(
            args.grm_path,
            executable=args.ace_path,
            cmdargs=['--timeout', str(args.timeout), '--disable-generalization']
        )
        return ace_parser, ace_generator
    except Exception as e:
        print(f"Error starting ACE in worker {workerid}: {e}")
        return None, None


def close_ace(ace_parser, ace_generator, workerid):
    print(f"Zoy Debug: Worker {workerid} closing ACE processes.")
    try:
        if ace_parser is not None:
            ace_parser.close()
    except Exception as e:
        print(f"Zoy Debug: Worker {workerid} error closing ACEParser: {e}")
    try:
        if ace_generator is not None:
            ace_generator.close()
    except Exception as e:
        print(f"Zoy Debug: Worker {workerid} error closing ACEGenerator: {e}")


def parse_file(x):
    args, filename, workerid = x

    # 1. Setup Logging
    log_file_path = f"{args.target_data_dir}/log_worker_{workerid:02d}.txt"
    f_log = open(log_file_path, 'w')
    sys.stdout.flush()
    sys.stderr.flush()
    os.dup2(f_log.fileno(), 1)  # stdout -> file
    os.dup2(f_log.fileno(), 2)  # stderr -> file
    print(f"Zoy Debug: Worker {workerid} initializing...")

    # 2. Initialize Persistent ACE Processes (first batch)
    ace_parser, ace_generator = init_ace(args, workerid)
    if ace_parser is None or ace_generator is None:
        print(f"Zoy Debug: Worker {workerid} failed to start ACE, aborting.")
        f_log.close()
        return False

    data = read_snli(f"{args.data_dir}/{filename}")
    statistics = {'unparsed_sentence': 0, "timeout": 0}
    erg_data = []
    target_file_name = f"{args.target_data_dir}/erg_{filename}"

    print(f"Worker {workerid} processing {len(data)} items...")

    # counter for how many examples processed with current ACE instances
    since_restart = 0
    restart_interval = max(1, args.max_sentences_reset_ace_process)

    try:
        for i, datum in enumerate(data):
            # Restart ACE after every N examples to avoid long-lived process issues
            if since_restart >= restart_interval:
                print(f"Zoy Debug: Worker {workerid} restarting ACE after {since_restart} items.")
                close_ace(ace_parser, ace_generator, workerid)
                ace_parser, ace_generator = init_ace(args, workerid)
                if ace_parser is None or ace_generator is None:
                    print(f"Zoy Debug: Worker {workerid} failed to restart ACE, aborting loop.")
                    break
                since_restart = 0

            erg_datum = copy.deepcopy(datum)
            processed_any_sentence = False  # track if at least one side succeeded

            for idx in ['1', '2']:
                sentence = datum[f'sentence{idx}']
                erg_sentence = {'original': sentence}

                transforms = transfer(
                    sentence, args.grm_path, args.ace_path,
                    timeout=args.timeout,
                    tenses=args.tenses,
                    progs=args.progs,
                    perfs=[],
                    parser=ace_parser,
                    generator=ace_generator
                )

                if transforms is None or len(transforms) == 0:
                    statistics["unparsed_sentence"] += 1
                    continue
                elif "timeout" in transforms:
                    statistics["timeout"] += 1
                    continue

                # if we reached here, we have some transforms
                processed_any_sentence = True

                for trans_type in transforms:
                    # Handle original specially to keep MRS
                    if trans_type == 'original':
                        erg_sentence[trans_type] = transforms[trans_type]
                    else:
                        erg_sentence[trans_type] = [t['surface'] for t in transforms[trans_type]]

                erg_datum[f'sentence{idx}'] = erg_sentence

            if processed_any_sentence:
                erg_data.append(erg_datum)

            since_restart += 1  # count this datum towards restart threshold

            # Checkpoint
            if (i + 1) % args.checkpoint_period == 0:
                print(f"Worker {workerid}: Processed {i + 1}/{len(data)}, "
                      f"erg_data so far = {len(erg_data)}")
                with open(target_file_name, 'w') as outfile:
                    for d in erg_data:
                        json.dump(d, outfile)
                        outfile.write('\n')
                        outfile.flush()

    except Exception:
        traceback.print_exc()
    finally:
        # 3. Clean up processes
        close_ace(ace_parser, ace_generator, workerid)
        f_log.close()

    # Final Write
    with open(target_file_name, 'w') as outfile:
        for d in erg_data:
            json.dump(d, outfile)
            outfile.write('\n')
            outfile.flush()
    with open(f"{args.target_data_dir}/parse_stats_{filename.replace('.jsonl','')}.json", 'w') as outfile:
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

    args = parser.parse_args()
    if not os.path.exists(args.target_data_dir):
        os.mkdir(args.target_data_dir)
    data_file_prefix = "snli_1.0"
    #splits = ["train", "dev", "test"]
    splits = ["dev"]
    num_division = 32
    pool = multiprocessing.Pool(processes=num_division)
    for split in splits:
        print(f"Zoy Debug: processing split: {split}")
        check_and_split_dataset(args.data_dir, data_file_prefix, split, num_division)
        parallel_inputs = [(args, f"{data_file_prefix}_{split}_{i:02d}.jsonl", i) for i in range(num_division)]
        print(f"Zoy Debug: parallel_inputs: {parallel_inputs}")
        try:
            results = list(tqdm(
                pool.imap_unordered(parse_file, parallel_inputs),
                total=len(parallel_inputs),
                desc=f"Processing {split} chunks",
                unit="file"
            ))
            if not all(results):
                print("Zoy Debug: one or more workers returned False and need to check logs")
        except KeyboardInterrupt:
            print("\nZoy Debug: keyboardInterrupt caught, terminating pool...")
            pool.terminate()
            pool.join()
            sys.exit(1)
        except Exception as e:
            print(f"Zoy Debug: main process error: {e}")
            traceback.print_exc()
    pool.close()
    pool.join()
    print("Zoy Debug: All finish")
