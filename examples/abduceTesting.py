import subprocess
import tempfile
import sys 
import re
import json
import os
from pathlib import Path


tactics_path = ""
supported_lemmas_json = "Supported Lemmas Results.json"
output_json = "automation_results.json"
end_keywords = {"Qed.", "Abort.", "Admitted."}

# runs coqc on the given Rocq file and returns both stdout and stderr
def run_coqc(fname):
    return subprocess.run(["coqc", fname], text=True, capture_output=True)


def run_coqtop(input_text):
    return subprocess.run(["coqtop"], input=input_text, text=True, capture_output=True)


def obtain_abducts(text):
    abducts = []
    pattern = r"would make it provable:\s*\n\s*(.*)"
    match = re.search(pattern, text)
    
    if match:
        potential_abduct = match.group(1).strip()
        if potential_abduct and not potential_abduct.startswith(("Goal", "Proof", "Qed", "Abort")):
            abducts.append(potential_abduct)
                
    return abducts

# generalizes the abduct by replacing lowercase variable names with "_"
def generalize(abduct):
    pattern = r"\b[a-z][A-Za-z0-9_]*\b"
    return re.sub(pattern, "_", abduct)

# builds a Rocq Search command using the generalized abduct
# the file header/imports are included so Search runs in the same environment
def find_lemmas(general_abduce, fname):
    environment_setup = []
    is_header = True

    with open(fname, "r") as f:
        for line in f:
            Lstript = line.strip()

            if is_header:
                if Lstript.startswith(("Goal", "Lemma", "Theorem")):
                    is_header = False

                else:
                    environment_setup.append(line)

    Rocqcommand = "".join(environment_setup)
    Rocqcommand += "\n"
    Rocqcommand += f"Search (" + general_abduce + ")."

    result = run_coqtop(Rocqcommand)
    return result.stdout + result.stderr

# looks through the Search results and chooses a lemma whose statement matches the abduct
def choose_lemma(lemmas, abduct):
    abduce = abduct.strip().rstrip(".")

    for line in lemmas.splitlines():
        line = line.strip()
        matching = re.match(r"^([A-Za-z0-9_'\.]+)\s*:\s*(.*)$", line)

        if matching:
            lemma_name = matching.group(1)
            lemma_stmt = matching.group(2).strip().rstrip(".")

            if abduce in lemma_stmt:
                return lemma_name

    return None

# deletes a file
def delete_file(file_path):
    if file_path:
        path_obj = Path(file_path)
        if path_obj.exists():
            os.remove(file_path)

    # Creates a temporary file where the selected theorem
    # is rewritten to use:
    #   Proof.
    #   abduce 1.
    #   Abort.
def rewrite_file_abduct(file_path, lemma_name):
    file_text = Path(file_path).read_text(errors="ignore")
    lines = file_text.splitlines(True)

    new_file_text = []
    # add SMTCoq imports/load path to the top of the temporary file.
    new_file_text.append(f'Add Rec LoadPath "{tactics_path}" as SMTCoq.\n')
    new_file_text.append("Require Import SMTCoq.SMTCoq.\n")

    state = "OUTSIDE"
    checking_theorem = False
    current_lemma = None
    target_lemma = lemma_name

    for line in lines:
        Lstrip = line.strip()

        if state == "OUTSIDE":
            if "Theorem" in Lstrip or "Lemma" in Lstrip:
                parts = Lstrip.split()

                if len(parts) >= 2:
                    current_lemma = parts[1].replace(":", "")

            if checking_theorem or "Theorem" in Lstrip or "Lemma" in Lstrip:
                checking_theorem = True

                if Lstrip.endswith("."):
                    checking_theorem = False

                    if current_lemma == target_lemma:
                        new_file_text.append(line)
                        state = "TARGET"

                    else:
                        new_file_text.append(line)
                        state = "SKIP"

                else:
                    new_file_text.append(line)
            else:
                new_file_text.append(line)

        elif state == "TARGET":
            complete_writing = False

            for key in end_keywords:
                if key in Lstrip:
                    complete_writing = True
            
            if complete_writing:
                new_file_text.append("Proof.\n")
                new_file_text.append("abduce 1.\n")
                new_file_text.append("Abort.\n")
                state = "OUTSIDE"

        elif state == "SKIP":
            complete_writing = False

            for key in end_keywords:
                if key in Lstrip:
                    complete_writing = True
            
            if complete_writing:
                new_file_text.append(line)
                state = "OUTSIDE"

            else:
                new_file_text.append(line)

    temporary_file = Path(file_path).with_name(Path(file_path).stem + "_abduce.v")
    temporary_file.write_text("".join(new_file_text))

    return str(temporary_file)

    # creates a temporary file containing the reconstructed proof:
    #
    #   assert (abduct).
    #   { apply matching_lemma. }
    #   try_smt.
    #
    # the file is later compiled to test whether automation succeeded.
def rewrite_file_automation(file_path, lemma_name, abduct, lemma_match):
    file_text = Path(file_path).read_text(errors="ignore")
    lines = file_text.splitlines(True)

    new_file_text = []
    new_file_text.append(f'Add Rec LoadPath "{tactics_path}" as SMTCoq.\n')
    new_file_text.append("Require Import SMTCoq.SMTCoq.\n")

    state = "OUTSIDE"
    checking_theorem = False
    current_lemma = None
    target_lemma = lemma_name

    for line in lines:
        Lstrip = line.strip()

        if state == "OUTSIDE":
            if "Theorem" in Lstrip or "Lemma" in Lstrip:
                parts = Lstrip.split()
                if len(parts) >= 2:
                    current_lemma = parts[1].replace(":", "")

            if checking_theorem or "Theorem" in Lstrip or "Lemma" in Lstrip:
                checking_theorem = True

                if Lstrip.endswith("."):
                    checking_theorem = False

                    if current_lemma == target_lemma:
                        new_file_text.append(line)
                        state = "TARGET"

                    else:
                        new_file_text.append(line)
                        state = "SKIP"

                else:
                    new_file_text.append(line)
            else:
                new_file_text.append(line)

        elif state == "TARGET":
            has_ended = False

            for key in end_keywords:
                if key in Lstrip:
                    has_ended = True
            
            if has_ended:
                new_file_text.append(f"  assert ({abduct}).\n")
                new_file_text.append(f"  {{ apply {lemma_match}. }}\n")
                new_file_text.append("  try_smt.\n")
                new_file_text.append("Qed.\n")
                state = "OUTSIDE"

        elif state == "SKIP":
            has_ended = False

            for key in end_keywords:
                if key in Lstrip:
                    has_ended = True
            
            if has_ended:
                new_file_text.append(line)
                state = "OUTSIDE"
            else:
                new_file_text.append(line)

    temporary_file = Path(file_path).with_name(Path(file_path).stem + "_auto.v")
    temporary_file.write_text("".join(new_file_text))

    return str(temporary_file)


def automation_success(success):
    if success:
        return "Automation success"
    
    else:
        return "Automation failure"


# results are recorded and will be stored in a json file
def build_result(file_path, lemma, abducts, gen_abduct, lemma_match, classification):
    return {
        "file": file_path,
        "lemma": lemma,
        "abducts": abducts,
        "generalized abduct": gen_abduct,
        "lemma match": lemma_match,
        "classification": classification
    }


# runs the complete automation pipeline on a single theorem: an abduct is generated, the abduct is generalized, a supporting lemma is searched. 
# a matching lemma is selcted and the theorem is reconstructed, the results are classified
def run_single(file_path, lemma_name):
    abduct_file = None
    auto_file = None
    final_output = None

    abduct_file = rewrite_file_abduct(file_path, lemma_name)
    result = run_coqc(abduct_file)
    abducts = obtain_abducts(result.stdout + result.stderr)

    if not abducts:
        final_output = build_result(file_path, lemma_name, [], None, None, "No abduct produced")

    else:
        abduct = abducts[0]
        generalize_abduce = generalize(abduct)

        lemmas = find_lemmas(generalize_abduce, file_path)
        chosen = choose_lemma(lemmas, abduct)

        if chosen is None:
            final_output = build_result(file_path, lemma_name, abducts, generalize_abduce, None, "No searched lemma matched abduct")

        else:
            auto_file = rewrite_file_automation(file_path, lemma_name, abduct, chosen)
            res = run_coqc(auto_file)
            success = res.returncode == 0

            final_output = build_result(file_path, lemma_name, abducts, generalize_abduce, chosen,  automation_success(success))

    delete_file(abduct_file)
    delete_file(auto_file)
    return final_output


def main():
    with open(supported_lemmas_json, "r") as f:
        files = json.load(f)

    all_results = []

    for entry in files:
        lemma_classification = entry.get("classification:")
        if lemma_classification is None:
            lemma_classification = entry.get("classification")
            
        if lemma_classification == "COUNTEREXAMPLE":
            file_path = entry.get("file name:")
            if file_path is None:
                file_path = entry.get("file")
                
            lemma_name = entry.get("lemma:")
            if lemma_name is None:
                lemma_name = entry.get("lemma")


            process_file = run_single(file_path, lemma_name)
            all_results.append(process_file)

    with open(output_json, "w") as f:
        json.dump(all_results, f, indent=2)

    print(f"Done processing files. Results written to: {output_json}")


if __name__ == "__main__":
    main()