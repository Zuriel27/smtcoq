import sys 
import os
import subprocess
import re
import tempfile
from pathlib import Path
import json
import benchmark

results_json = "results.json"
end_keywords = {"Qed.", "Abort.", "Admitted."}
# path to the SMTCoq tactics folder
tactics_path = ""

# a temporary file is created version where each proof body is replaced with try_smt
# idtac is used inserted as a marker so that the output can be later be sliced by the theorem name
def rewrite_file(fname):
    file_text = fname.read_text(errors="ignore")
    lines = file_text.splitlines(True)
    new_file_text = []

    # add SMTCoq load path and import to the rewritten file
    new_file_text.append(f'Add Rec LoadPath "{tactics_path}" as SMTCoq.\n')
    new_file_text.append("Require Import SMTCoq.SMTCoq.\n")

    state = "OUTSIDE"
    checking_theorem = False
    theorem_name = None
    theorem_count = 0

    for line in lines:
        Lstrip = line.strip()

        if state == "OUTSIDE":
            new_file_text.append(line)

            # detect the start of a theorem
            if benchmark.is_theorem_start(line) or checking_theorem:
                if not checking_theorem:
                    theoremPart = Lstrip.split()

                    if len(theoremPart) >= 2:
                        theorem_name = theoremPart[1].replace(":", "")
                    else:
                        theorem_name = f"theorem number {theorem_count}"


                if Lstrip.endswith("."):
                    state = "THEOREM"
                    checking_theorem = False
                else:
                    checking_theorem = True

        elif state == "THEOREM":
            theorem_complete = False

            for key in end_keywords:
                if key in Lstrip:
                    theorem_complete = True

            if theorem_complete:
                theorem_count += 1
                # have a marker so parse_output can identify which output belongs to which theorem
                new_file_text.append(f'idtac "lemma_start {theorem_name}". \n')
                new_file_text.append(" try_smt.\n")
                # new_file_text.append(f'idtac "end_lemma". \n')
                new_file_text.append("Abort.\n")
                state = "OUTSIDE"


    temporary_file = fname.with_name(f"{fname.stem}_rewrite.v")
    with open(temporary_file, "w") as f:
        f.write("".join(new_file_text))

    return temporary_file


def run_coqc(fname):
    coqc = subprocess.run(['coqc', str(fname)], text=True, capture_output=True)
    coqcop = coqc.stdout + coqc.stderr #output to be parsed
    return {
        "file name:" : str(fname),
        "terminal output:" : coqcop,
        "return code:" : coqc.returncode
    }

# classifies one theorem's terminal output.
def classify_results(text):
    output = text.lower()

    if ("non-linear fact" in output) or ("unsupported" in output) or ("can only deal with") in output:
        return "UNSUPPORTED"

    if "unsat" in output:
        return "PROVED"

    if "sat" in output and "model" in output:
        return "COUNTEREXAMPLE"

    if "error" in output or "exception" in output:
        return "ERROR"

    return "UNKNOWN"


def parse_output(log_text):
    lines = log_text.splitlines()

    results = []
    buffer = []
    current_lemma = None

    for line in lines:
        lemma_start = re.search(r'lemma_start\s+([^\s."]+)', line)

        if lemma_start:
            if current_lemma is not None:
                block_text = "\n".join(buffer)
                results.append({
                    "lemma:": current_lemma,
                    "label:": classify_results(block_text),
                    "terminal output:": block_text
                })

            current_lemma = lemma_start.group(1)
            buffer = []

        else:
            if current_lemma is not None:
                buffer.append(line)

    if current_lemma is not None:
        block_text = "\n".join(buffer)
        results.append({
            "lemma:": current_lemma,
            "label:": classify_results(block_text),
            "terminal output:": block_text
        })

    return results

# compiles the rewritten file, and removes missing imports
# the max number of loops is based on the number of attempts it took to fully run the .v file
def run_modified_file(fname, max_loop):
    change_attemps = 0
    complete_running = False

    while complete_running == False and change_attemps < max_loop:
        result = run_coqc(fname)
        output = result["terminal output:"]

        if result["return code:"] == 0:
            complete_running = True

        else:
            error_cause = benchmark.missing_import(output)

            if error_cause is not None:
                removed = benchmark.remove_import(fname, error_cause)

                if removed:
                    change_attemps += 1
                
                else:
                    complete_running = True
            else:
                complete_running = True 
    
    return result


def process_file(entry):
    fname = entry["file name:"]
    attempts = entry["attempts:"]

    print()
    print(f"Compiling: {fname}")

    temp_file = rewrite_file(Path(fname))
    compile_temp_file = run_modified_file(temp_file, attempts)
    output_results = parse_output(compile_temp_file["terminal output:"])

    file_results = {
        "file name:" : fname,
        "lemma classification:" : output_results
    }

    if temp_file is not None:
        if temp_file.exists():
            os.remove(temp_file)

    
    return file_results

# stores each theorem result into one of three lists, files all results, SMT supported, and SMT unsupported 
def store_results(file, all_results, supported_lemmas, unsupported_lemmas):
    file_name = file["file name:"]
    lemma_results = file["lemma classification:"]

    for lemma in lemma_results:

        lemma_classify = {
            "file name:" : file_name, 
            "lemma:" : lemma["lemma:"],
            "classification:" : lemma["label:"]
        }

        all_results.append(lemma_classify)

        if lemma["label:"] == "PROVED" or lemma["label:"] == "COUNTEREXAMPLE":
            supported_lemmas.append(lemma_classify)

        else:
            unsupported_lemmas.append(lemma_classify)
    
        print(f"lemma name: {lemma_classify["file name:"]}")
        print(f"lemma classification: {lemma_classify["classification:"]}")




def main():
    # read the usable files produced by benchmark.py
    with open(results_json, "r") as f:
        files = json.load(f)

        all_results = []
        supported_lemmas = []
        unsupported_lemmas = []

        for entry in files:

            results = process_file(entry)

            store_results(results, all_results, supported_lemmas, unsupported_lemmas)

    # store all theorem classifications into three json files
    with open("All Lemmas Results.json", "w") as f:
        json.dump(all_results, f, indent=2)
    
    with open("Supported Lemmas Results.json", "w") as g:
        json.dump(supported_lemmas, g, indent=2)

    with open("Unsupported Lemmas Results.json", "w") as h:
        json.dump(unsupported_lemmas, h, indent=2)


    print()
    print("Done processing json.")



if __name__ == "__main__":
    main()
