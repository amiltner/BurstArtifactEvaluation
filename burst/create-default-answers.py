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

def stddev(lst):
    mean = float(sum(lst)) / len(lst)
    return sqrt(float(reduce(lambda x, y: x + y, map(lambda x: (x - mean) ** 2, lst))) / len(lst))


TEST_EXT = '.mls'
REF_EXT = '.out'
SMYTH_EXT = '.smyth.out'
BASELINE_EXT = '.out'
BASE_FLAGS = []
TIMEOUT_TIME = 120
STILL_WORK_TIMEOUT_TIME = 120
GENERATE_EXAMPLES_TIMEOUT_TIME = 600000

REPETITION_COUNT = 1

def ensure_dir(f):
    d = os.path.dirname(f)
    if not os.path.exists(d):
        os.makedirs(d)

def transpose(matrix):
    return zip(*matrix)

def find_tests(root):
    tests = []
    for path, dirs, files in os.walk(root):
        files = [(f[0], f[1]) for f in [splitext(f) for f in files]]
        tests.extend([(path, f[0]) for f in files if f[1] == TEST_EXT])
    return tests

def gather_datum(prog, path, base, additional_flags, timeout):
    process_output = EasyProcess([prog] + additional_flags + [join(path, base + TEST_EXT)]).call(timeout=timeout)
    return process_output.stdout


def gather_data(rootlength, prog, path, base,run_smyth):
    if not os.path.exists(join(path,base+REF_EXT)):
        res = gather_datum(prog, path, base,[],TIMEOUT_TIME)
        if res == "":
            res = "timeout or error out"
        print(join(path,base+REF_EXT))
        with open(join(path,base+REF_EXT), "w") as outfile:
            outfile.write(res)
    if not os.path.exists(join(path,base+SMYTH_EXT)) and run_smyth:
        print(join(path,base+SMYTH_EXT))
        res = gather_datum(prog, path, base,["-use-smyth"],TIMEOUT_TIME)
        if res == "":
            res = "timeout or error out"
        with open(join(path,base+SMYTH_EXT), "w") as outfile:
            outfile.write(res)

def specsize_compare(x,y):
    return int(x["SpecSize"])-int(y["SpecSize"])

def sort_data(data):
    return sorted(data,cmp=specsize_compare)

def print_data(data):
    ensure_dir("generated_data/")
    with open("generated_data/generated_data.csv", "w") as csvfile:
        datawriter = csv.DictWriter(csvfile,fieldnames=data[0].keys())
        datawriter.writeheader()
        datawriter.writerows(data)

def print_usage(args):
    print("Usage: {0} <prog> <test|testdir>".format(args[0]))

def transform_data(path, base, run_data):
    current_data = {"Test":join(path, base + TEST_EXT).replace("_","-")[6:]}
    run_data_transpose = transpose(run_data)
    for index in range(len(run_data_transpose)/2):
        col_name = run_data_transpose[index][0]
        col_data = run_data_transpose[index+1]
        if "" in col_data:
            current_data[col_name]=-1
        else:
            col = [float(x) for x in col_data]
            current_data[col_name] = str(sum(col)/len(col))
    return current_data

def main(args):
    if len(args) == 4:
        prog = args[1]
        postconditional_path = args[2]
        example_based_path = args[3]
        rootlength = len(example_based_path)
        if not os.path.exists(prog):
            print_usage(args)
        elif os.path.exists(example_based_path) and os.path.isdir(example_based_path):
            for path, base in find_tests(example_based_path):
                print(join(path, base + TEST_EXT).replace("_","-")[rootlength:])
                gather_data(rootlength,prog, path, base,True)
        else:
            print_usage(args)
        rootlength = len(postconditional_path)
        if os.path.exists(postconditional_path) and os.path.isdir(postconditional_path):
            for path, base in find_tests(postconditional_path):
                print(join(path, base + TEST_EXT).replace("_","-")[rootlength:])
                gather_data(rootlength,prog, path, base,False)
        else:
            print_usage(args)
    else:
        print_usage(args)

if __name__ == '__main__':
    main(sys.argv)
