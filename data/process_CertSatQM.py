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

file = open('output_CertSatQM_endpoints.txt', 'r')

table = {}
times = []

STATE_READ_NORMAL=0
STATE_READ_NUM_INTERVALS=1
STATE_READ_BASIS=2
STATE_READ_ARCH_POLY=3
STATE_READ_TIME_CERTSATQM=4
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
                        # print("Number of intervals:", num_intervals, "Number of tests:", len(times), "Avg time:", average(times))
                        print(num_intervals, "&", len(times), "&", average(times), "\\\\")
                    # Reset state
                    times = []
                    # Process new row
                    state = STATE_READ_NUM_INTERVALS
                if word == '">> Basis"':
                    state = STATE_READ_BASIS
                if word == '">> Archimedean Poly"':
                    state = STATE_READ_ARCH_POLY
                if word == '">> Time CertSatQM"':
                    state = STATE_READ_TIME_CERTSATQM
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

            if state == STATE_READ_TIME_CERTSATQM:
                times.append(float(word))
                state = STATE_READ_NORMAL
                continue
