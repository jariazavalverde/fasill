#!/bin/bash

# clean files
rm ../www/pages/ref-doc/*
rm ../www/pages/src-doc/*

# generate predicate reference documentation
python builtin.py "../src/fasill_builtin.pl" "../www/pages/ref-doc/"

# generate implementation details documentation
for f in ../src/*; do
	python source.py "../src/${f}" "../www/pages/src-doc/"
done;