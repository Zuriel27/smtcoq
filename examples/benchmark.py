#Get first command line argument into a string variable
import sys 
import os
import subprocess
import re
import tempfile
from pathlib import Path
import json

# path to the SMTCoq tactics folder
tactics_path = ""
start_keywords = {"Lemma", "Theorem", "Goal"}
end_keywords = {"Qed.", "Abort.", "Admitted."}


# checks if a line starts a theorem, lemma, or goal
def is_theorem_start(line):
    line_s = line.strip()

    if line_s == "":
        return False
    
    first = line_s.split()[0]

    if first in start_keywords:
        return True
    
    return False

# creates a temporary version of the Rocq file, in the temporary file, every proof body is replaced with:
#   try_smt.
#   Abort.
# lets the script test whether the theorem supports SMTCoq
def rewrite_file(fname):
    file_text = fname.read_text(errors="ignore")
    lines = file_text.splitlines(True)
    new_file_text = []

    # add SMTCoq imports/load path to the top of the temporary file.
    new_file_text.append(f'Add Rec LoadPath "{tactics_path}" as SMTCoq.\n')
    new_file_text.append("Require Import SMTCoq.SMTCoq.\n")

    state = "OUTSIDE"
    checking_theorem = False

    for line in lines:
        Lstrip = line.strip()

        if state == "OUTSIDE":
            new_file_text.append(line)

            if is_theorem_start(line) or checking_theorem:
                if Lstrip.endswith("."):
                    state = "THEOREM"
                    checking_theorem = False
                else:
                    checking_theorem = True

        elif state == "THEOREM":
            theorem_complete = False
            
            # skip the original proof body until the proof ends
            for key in end_keywords:
                if key in Lstrip:
                    theorem_complete = True

            if theorem_complete:
                new_file_text.append("try_smt.\n")
                new_file_text.append("Abort.\n")
                state = "OUTSIDE"
            
     
    # write the modified file as a temporary _tmp.v file
    temporary_file = fname.with_name(f"{fname.stem}_tmp.v")
    with open(temporary_file, "w") as f:
        f.write("".join(new_file_text))

    return temporary_file

# looks at a coqc error message and extracts the missing import
def missing_import(stderr_text):
    match = re.search(
        r'logical path ([A-Za-z0-9_\.]+)',
        stderr_text
    )
    if match:
        return match.group(1)

    return None

 # removes line that contains the missing import
def remove_import(modified_file, import_name):
    file_text = modified_file.read_text(errors="ignore")
    lines = file_text.splitlines(True)

    new_text = []
    removed = False
    for line in lines:
        Lstrip = line.strip()
        should_remove = False

        if Lstrip.startswith("Require Import"):
            if import_name in Lstrip:
                should_remove = True
        
        if Lstrip.startswith("From"):
            if import_name in Lstrip:
                should_remove = True
        
        if should_remove:
            removed = True
        else:
            new_text.append(line)

    modified_file.write_text("".join(new_text))

    return removed

# compiles the temporary rewritten file, if compilation fails because of a missing import, the import is removed and recompiled
# code stops once the file compiles, fails for a non-import reason, or reaches the maximum number of attempts
def run_modified_file(fname, max_loop = 10):
    change_attempts = 0
    removed_lines = []
    error_cause = None

    complete_running = False
    success = False

    while complete_running == False and change_attempts < max_loop:
        print()
        print(f"Compiling: {fname.name}")
        print(f"Attempt: {change_attempts + 1}")
        print()


        result = run_coqc(fname)
        terminal_output = result.stdout + result.stderr

        if result.returncode == 0:
                print("succeded")
                print(f"Removed lines: {removed_lines}")
                complete_running = True
                success = True
                
        
        else:
            print("failure\n")
            # print(terminal_output)
            error_cause = missing_import(terminal_output)

            if error_cause is not None:
                print("missing import")

                removed = remove_import(fname, error_cause)
            
                if removed:
                    print("removed import")
                    removed_lines.append(error_cause)
                    change_attempts += 1

                else:
                    print("could not remove import")
                    complete_running = True
            
            else:
                print("non-import compilation failure")
                complete_running = True
        
    return {
        "success" : success,
        "attempts": change_attempts + 1,
        "removed_imports": removed_lines,
        "error": error_cause
    }



def run_coqc(fname):
    # path = Path(fname)
    coqc = subprocess.run(['coqc', str(fname)], text=True, capture_output=True)
    return coqc

# processes a single .v file by calling the rewrite_file method, and the results are stored
# a temporary file is crated when rewriting the file and is deleted when the results are stored 
def process_file(v_file):
    print()
    print(f"Compiling: {v_file}")

    temp_file = rewrite_file(v_file)
    compile_temp_file = run_modified_file(temp_file)

    if compile_temp_file["success"]:
        file_results = {
            "file name:" : str(v_file),
            "attempts:" : compile_temp_file["attempts"],
            "imports removed:" : compile_temp_file["removed_imports"],
            "error:" : compile_temp_file["error"]
        }

    if temp_file is not None:
        if temp_file.exists():
            os.remove(temp_file)
    
    return file_results

# finds all .v files inside the project directory
def collect_vFiles(project_directory):
    root = Path(project_directory)
    v_files = []
    for path in root.rglob("*.v"):

        if "_tmp" not in path.name:
            v_files.append(path)

    return v_files


# processes every .v file in a project directory
def process_project(project_directory):
    project_filesResults = []
    v_files = collect_vFiles(project_directory)
    print()
    print(f"Number of .v files in project: {len(v_files)}")

    for file in v_files:
        process = process_file(file)

        if process is not None:
            project_filesResults.append(process)

    
    return project_filesResults


# results are stored in a json file
def store_results(results):
    results_file = "results.json"

    with open(results_file, "w") as f:
        json.dump(results, f, indent=1)


def main():
    # the user input
    base_name = sys.argv[1]
    results = process_project(base_name)
    store_results(results)

    print("Done processing project. Results written to results.json")


if __name__ == "__main__":
    main()
