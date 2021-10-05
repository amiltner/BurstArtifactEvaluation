#!/usr/local/bin/python

from __future__ import print_function
from easyprocess import EasyProcess

import os
import csv
from os.path import splitext, join
import subprocess
import sys
import time

from math import sqrt

def can_be_float(s):
    try:
        float(s)
        return True
    except ValueError:
        return False

def can_be_int(s):
    try:
        int(s)
        return True
    except ValueError:
        return False

def simple_write_to_file(fname,data):
    text_file = open(fname,"w")
    text_file.write(data)
    text_file.close()

def clean(s):
    s = str(s)
    if can_be_int(s):
        return int(s)
    elif can_be_float(s):
        f = float(s)
        if f.is_integer():
            return int(f)
        else:
            return "{:.2f}".format(float(s))
    elif s == "timeout":
        return "\\incorrect"
    elif s == "error":
        return "\\incorrect"
    else:
        return s

def stddev(lst):
    mean = float(sum(lst)) / len(lst)
    return sqrt(float(reduce(lambda x, y: x + y, map(lambda x: (x - mean) ** 2, lst))) / len(lst))

def average(lst):
    return sum(lst)/len(lst)


TEST_EXT = '.mls'
BASELINE_EXT = '.out'
BASE_FLAGS = []
TIMEOUT_TIME = 120
CORRECT_TIMEOUT_TIME = 120
STILL_WORK_TIMEOUT_TIME = 120
GENERATE_EXAMPLES_TIMEOUT_TIME = 600000

REPETITION_COUNT = 5

def ensure_dir(f):
    d = os.path.dirname(f)
    if not os.path.exists(d):
        os.makedirs(d)

def transpose(matrix):
    return list(zip(*matrix))

def check_equal(prog,path,base,data):
    infofname = join(path,base + TEST_EXT)
    exfname = join(path,base + BASELINE_EXT)
    temp_name = "temp.out"
    simple_write_to_file(temp_name,data)
    (time,datum,err) = gather_datum(prog, path, base, ["-check-equiv1",exfname,"-check-equiv2",temp_name], CORRECT_TIMEOUT_TIME)
    return err == ""

def find_tests(root):
    tests = []
    for path, dirs, files in os.walk(root):
        files = [(f[0], f[1]) for f in [splitext(f) for f in files]]
        tests.extend([(path, f[0]) for f in files if f[1] == TEST_EXT])
    return tests

def find_subs(root):
    dirs = next(os.walk(root))[1]
    groupings=[]
    for direct in dirs:
        files = next(os.walk(join(root,direct)))[2]
        positives = [join(root,direct,f) for f in files if splitext(f)[1] == POS_EXT]
        negatives = [join(root,direct,f) for f in files if splitext(f)[1] == NEG_EXT]
        posndfs = [join(root,direct,f) for f in files if splitext(f)[1] == POSNDF_EXT]
        negndfs = [join(root,direct,f) for f in files if splitext(f)[1] == NEGNDF_EXT]
        groupings.append((direct,positives,posndfs,negatives,negndfs))
    return groupings

def gather_datum(prog, path, base, additional_flags, timeout):
    start = time.time()
    flags = additional_flags
    #flags = map(lambda t: t(path,base),additional_flags)
    print([prog] + BASE_FLAGS + flags + [join(path, base + TEST_EXT)])
    process_output = EasyProcess([prog] + BASE_FLAGS + flags + [join(path, base + TEST_EXT)]).call(timeout=timeout+5)
    end = time.time()
    return ((end - start), process_output.stdout,process_output.stderr)

def gather_data(rootlength, prog, path, base,name,run_smyth):
    current_data = {"Test":name}

    def gather_col(flags, run_combiner, col_names, timeout_time, repetition_count, compare):
        run_data = []
        timeout = False
        error = False
        incorrect = False
        memout = False
        iteration = 0
        for iteration in range(repetition_count):
            (time,datum,err) = gather_datum(prog, path, base,flags,timeout_time)
            print(time)
            if err != "":
                error = True
                break
            if time >= TIMEOUT_TIME:
                timeout = True
                break
            if datum == "":
                memout = True
                break
            this_run_data = list(map(lambda d: d.strip(),datum.split(";"))) + [time]
            if iteration == 0 and compare and not check_equal(prog,path,base,this_run_data[0]):
                incorrect = True
            run_data.append(this_run_data)
            iteration = iteration+1
        if error:
            print("\\incorrect")
            for col_name in col_names:
                if "ComputationTime" in col_name:
                    current_data[col_name]="\\incorrect"
                else:
                    current_data[col_name]="\\na"
        elif timeout:
            print("\\incorrect")
            for col_name in col_names:
                if "ComputationTime" in col_name:
                    current_data[col_name]="\\incorrect"
                else:
                    current_data[col_name]="\\na"
        elif memout:
            print("\\incorrect")
            for col_name in col_names:
                if "ComputationTime" in col_name:
                    current_data[col_name]="\\incorrect"
                else:
                    current_data[col_name]="\na"
        elif incorrect:
            print("incorrect")
            for col_name in col_names:
                if "ComputationTime" in col_name:
                    current_data[col_name]="\\incorrect"
                else:
                    current_data[col_name]="\\na"
        else:
            run_data_transpose = transpose(run_data)
            combined_data = run_combiner(run_data_transpose)
            for (col_name,data) in zip(col_names,combined_data):
                current_data[col_name] = data

    def ctime_combiner(run_data_transpose):
        data_indices = range(1,len(run_data_transpose))
        cols = [[float(x) for x in run_data_transpose[i]] for i in data_indices]
        averages = [average(col) for col in cols]
        return averages

    gather_col([],ctime_combiner,["IsectTotal","IsectMax","MinifyTotal","MinifyMax","MinEltTotal","MinEltMax","InitialCreationTotal","InitialCreationMax","AcceptsTermTotal","AcceptsTermMax","LoopCount","FullSynth","FullSynthMax","ComputationTime"],TIMEOUT_TIME,REPETITION_COUNT,False)
    if run_smyth:
        gather_col(["-use-smyth"],ctime_combiner,["SmythIsectTotal","SmythIsectMax","SmythMinifyTotal","SmythMinifyMax","SmythMinEltTotal","SmythMinEltMax","SmythInitialCreationTotal","SmythInitialCreationMax","SmythAcceptsTermTotal","SmythAcceptsTermMax","SmythLoopCount","SmythFullSynth","SmythFullSynthMax","SmythComputationTime"],TIMEOUT_TIME,REPETITION_COUNT,False)
    gather_col(["-use-simple"],ctime_combiner,["SimpleIsectTotal","SimpleIsectMax","SimpleMinifyTotal","SimpleMinifyMax","SimpleMinEltTotal","SimpleMinEltMax","SimpleInitialCreationTotal","SimpleInitialCreationMax","SimpleAcceptsTermTotal","SimpleAcceptsTermMax","SimpleLoopCount","SimpleFullSynth","SimpleFullSynthMax","SimpleComputationTime"],TIMEOUT_TIME,REPETITION_COUNT,False)

    return current_data

def extract_test(x):
    return x["Test"]

def specsize_compare(x,y):
    return int(x["SpecSize"])-int(y["SpecSize"])

def test_compare(x,y):
    return int(x["Test"])-int(y["Test"])

def sort_data(data):
    data.sort(key=extract_test)#sorted(data,cmp=test_compare)

def clean_full_data(data):
    for row in data:
        for key in row.keys():
            row[key] = clean(row[key])

def print_data(data,name):
    clean_full_data(data)
    ensure_dir("generated-data/")
    with open("generated-data/" + name, "w") as csvfile:
        datawriter = csv.DictWriter(csvfile,fieldnames=data[0].keys())
        datawriter.writeheader()
        datawriter.writerows(data)

def print_usage(args):
    print("Usage: {0} <prog> <example_based> <equivalence_dir> <postconditional_dir>".format(args[0]))

def load_data(name):
    try:
        with open("generated-data/" + name, "r") as csvfile:
            datareader = csv.DictReader(csvfile)
            return [row for row in datareader]
    except:
        return []

def main(args):
    if len(args) == 5:
        prog = args[1]
        equivalence_path = args[2]
        postconditional_path = args[3]
        example_based_path = args[4]
        data = load_data("io.csv")
        print("example data")
        print(data)
        rootlength = len(example_based_path)
        if os.path.exists(prog) and os.path.exists(example_based_path) and os.path.isdir(example_based_path):
            for path, base in find_tests(example_based_path):
                test_name = join(path, base).replace("_","-")[rootlength+1:]
                print(test_name)
                if (not (any(row["Test"] == test_name for row in data))):
                    current_data = gather_data(rootlength,prog, path, base,test_name,True)
                    data.append(current_data)
                    print_data(data,"io.csv")
                else:
                    print("data already retrieved")
            sort_data(data)
            print_data(data,"io.csv")
        else:
            print(os.path.exists(prog))
            print_usage(args)
        data = load_data("ref.csv")
        print("equiv data")
        rootlength = len(equivalence_path)
        print(data)
        if os.path.exists(prog) and os.path.exists(equivalence_path) and os.path.isdir(equivalence_path):
            for path, base in find_tests(equivalence_path):
                test_name = join(path, base).replace("_","-")[rootlength+1:]
                print(test_name)
                if (not (any(row["Test"] == test_name for row in data))):
                    current_data = gather_data(rootlength,prog, path, base,test_name,True)
                    data.append(current_data)
                    print_data(data,"ref.csv")
                else:
                    print("data already retrieved")
            sort_data(data)
            print_data(data,"ref.csv")
        else:
            print(os.path.exists(prog))
            print_usage(args)
        data = load_data("logical.csv")
        rootlength = len(postconditional_path)
        print("postconditional data")
        print(data)
        if os.path.exists(prog) and os.path.exists(postconditional_path) and os.path.isdir(postconditional_path):
            for path, base in find_tests(postconditional_path):
                test_name = join(path, base).replace("_","-")[rootlength+1:]
                print(test_name)
                if (not (any(row["Test"] == test_name for row in data))):
                    current_data = gather_data(rootlength,prog, path, base,test_name,False)
                    data.append(current_data)
                    print_data(data,"logical.csv")
                else:
                    print("data already retrieved")
            sort_data(data)
            print_data(data,"logical.csv")
        else:
            print(os.path.exists(prog))
            print_usage(args)
    else:
        print_usage(args)

if __name__ == '__main__':
    main(sys.argv)
