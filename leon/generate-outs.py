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


TEST_EXT = '.scala'
REF_EXT = '.out'
BASELINE_EXT = '.out'
BASE_FLAGS = []
TIMEOUT_TIME = 130
STILL_WORK_TIMEOUT_TIME = 240
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

def gather_datum(path, base, timeout):
    process_output = EasyProcess(["./leon","--synthesis"] + [join(path, base + TEST_EXT)]).call(timeout=timeout)
    return process_output.stdout


def gather_data(rootlength, path, base):
    if not os.path.exists(join(path,base+REF_EXT)):
        res = gather_datum(path, base,TIMEOUT_TIME)
        with open(join(path,base+REF_EXT), "w") as outfile:
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
    print("Usage: {0} <test|testdir>".format(args[0]))

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
    if len(args) == 2:
        postconditional_path = args[1]
        postrootlength = len(postconditional_path)
        if os.path.exists(postconditional_path) and os.path.isdir(postconditional_path):
            for path, base in find_tests(postconditional_path):
                print(join(path, base + TEST_EXT).replace("_","-")[postrootlength+1:])
                gather_data(postrootlength,path, base)
        else:
            print_usage(args)
    else:
        print_usage(args)

if __name__ == '__main__':
    main(sys.argv)
