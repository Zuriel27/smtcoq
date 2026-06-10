
# First iteration of the automation process.
# The code runs a Rocq file, extracts an abduct from the output,
# generalizes the abduct, searches for a matching lemma, and tries
# to generate a new proof file using that lemma.

#Get first command line argument into a string variable
import sys 
import os
import subprocess
# from enum import Enum
import re

# the user input
base_name = sys.argv[1]
# directory path from user input
path = re.split("[^/]+$", base_name)[0]

name_match = re.search("[^/]+$", base_name)
name = name_match.group() if name_match else base_name

full_name = base_name + ".v"
parse_name = base_name + ".txt"


# runs coqc on the given Rocq file and returns both stdout and stderr
def run_coqc(fname):
    coqc = subprocess.run(['coqc', fname], text=True, capture_output=True)
    coqcop = coqc.stdout + coqc.stderr #output to be parsed
    return coqcop

# reads and returns the full contents of a file
def file_contents(fname):
    with open(fname, "r") as f:
        contents = f.read()
        return contents


def obtain_abducts(text):
    parse_string = "The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:"

    if parse_string in text:
        abduce = text.split(parse_string)[1].strip().split("\n")
        return abduce
    else:
        return []
    
# generalizes the abduct by replacing lowercase variable names with "_"
def generalize(abduct):
    abductParts = abduct.strip().split()
    generalAbduce = []

    for p in abductParts:
        if p.islower():
            generalAbduce.append("_")
        else:
            generalAbduce.append(p)

    return " ".join(generalAbduce)


# builds a Rocq Search command using the generalized abduct
# the file header/imports are included so Search runs in the same environment
def findLemmas(general_abduce, fname):
    environment_setup = []
    isHeader = True

    with open(fname, "r") as f:
        for line in f:
            line_strip = line.strip()
            if isHeader and line_strip.startswith(("Goal", "Lemma", "Theorem")):
                isHeader = False
            if isHeader:
                environment_setup.append(line)
    
    RocqCommand = "".join(environment_setup)
    RocqCommand += "\n"
    RocqCommand += f"Search ({general_abduce})."

    print(RocqCommand)

    Rocqtop = subprocess.run(['coqtop'], input=RocqCommand, text=True, capture_output=True)
    return Rocqtop.stdout


# looks through the Search results and chooses a lemma whose statement matches the abduct
def choose_lemma(lemmas, abduct):
    abduce = abduct.strip().rstrip(".")

    for line in lemmas.splitlines():
        line = line.strip()
        matching = re.match(r"^([A-Za-z0-9_']+)\s*:\s*(.*)$", line)

        if matching:
            lemmaName = matching.group(1)
            lemmaStmt = matching.group(2).strip().rstrip(".")

            if lemmaStmt == abduce:
                return lemmaName
    return None

# creates a new Rocq file where the abduct is asserted, the selected lemma is applied, and smt is retried
def complete_proof(fname, abduct, lemma_name):
    new_file = fname.replace(".v", "_automate.v")

    with open(fname, "r") as f:
        lines = f.readlines()

    rocqCommand = []

    for line in lines:
        if "abduce" in line.strip():
            parts = line.split(".")
            for p in parts:
                p = p.strip()

                if len(p) > 0:
                    if p.startswith("abduce"):
                        rocqCommand.append("  Fail " + p + ".\n")
                    else:
                        rocqCommand.append("  " + p + ".\n")

        else:
            rocqCommand.append(line)

        if line.strip() == "Qed.":
            rocqCommand.insert(
                len(rocqCommand)-1,
                f"  assert ({abduct}).\n"
                f"  {{ apply {lemma_name}. }}\n"
                f"  smt.\n"
            )

    with open(new_file, "w") as f:
        f.writelines(rocqCommand)

    return new_file

            
def main():
    print(f"Running: coqc {full_name}")
    file_output = run_coqc(full_name)

    abducts = obtain_abducts(file_output)
    print(f"Abduct: {abducts[0]}")

    general_abduct = generalize(abducts[0])
    print(f"Generalized abduct: ({general_abduct})")


    lemmas_found = findLemmas(general_abduct, full_name)
    print(f"Lemmas found: {lemmas_found}")

    selected_lemma = choose_lemma(lemmas_found, abducts[0])
    print(f"Chosen lemma: {selected_lemma}")

    if selected_lemma == None:
        print("Unable to complete proof")
    
    else:
        complete_proof(full_name, abducts[0], selected_lemma)

    print("Done!")


if __name__ == "__main__":
    main()

    