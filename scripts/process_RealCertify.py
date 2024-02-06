#!/usr/bin/env python3

import re

def average(l):
    sum = 0
    size = len(l)
    i = 0
    while True:
        if i >= size:
            break
        sum += l[i]
        i = i + 1
    return float(sum)/size

outLine = re.compile('.*>>.*')

#file = open('./../data/output_RealCertify_algo_1.txt', 'r')
file = open('./../data/output_RealCertify_algo_2.txt', 'r')

table = {}
times = []

STATE_READ_NORMAL=0
STATE_READ_NUM_INTERVALS=1
STATE_READ_BASIS=2
STATE_READ_ARCH_POLY=3
STATE_READ_TIME_REALCERTIFY_OK=4
STATE_READ_TIME_REALCERTIFY_NOK=5
state = STATE_READ_NORMAL

num_intervals=0

while True:
    line = file.readline()
    if not line:
        break
    if outLine.match(line):
        for word in line.split(','):
            word = word.strip()
            if state == STATE_READ_NORMAL:
                if word == '">> Number of intervals"':
                    # Write row
                    if len(times) > 0:
                        #print("Number of intervals:", num_intervals, "Number of tests:", len(times), "Avg time:", average(times))
                        print(num_intervals, "&", len(times), "&", average(times), "\\\\")
                    # Reset state
                    times = []
                    # Process new row
                    state = STATE_READ_NUM_INTERVALS
                if word == '">> Basis"':
                    state = STATE_READ_BASIS
                if word == '">> Archimedean Poly"':
                    state = STATE_READ_ARCH_POLY
                if word == '">> Time RealCertify succeds"':
                    state = STATE_READ_TIME_REALCERTIFY_OK
                if word == '">> Time RealCertify succeds"':
                    state = STATE_READ_TIME_REALCERTIFY_OK
                if word == '">> Time RealCertify fails"':
                    state = STATE_READ_TIME_REALCERTIFY_NOK
                continue

            if state == STATE_READ_NUM_INTERVALS:
                num_intervals = word
                state = STATE_READ_NORMAL
                continue

            if state == STATE_READ_BASIS:
                state = STATE_READ_NORMAL
                continue

            if state == STATE_READ_ARCH_POLY:
                state = STATE_READ_NORMAL
                continue

            if state == STATE_READ_TIME_REALCERTIFY_OK:
                times.append(float(word))
                state = STATE_READ_NORMAL
                continue

            if state == STATE_READ_TIME_REALCERTIFY_NOK:
                state = STATE_READ_NORMAL
                continue
