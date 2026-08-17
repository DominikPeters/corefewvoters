# Reproducing the six- and seven-voter computations

This directory contains the scripts for performing the computational verification used in Section 5 of
"Core Existence in Approval-Based Committee Elections with up to Seven Voter Types"
(Patrick Becker, Matthias Greger, Dominik Peters, [arXiv:2605.06194](https://arxiv.org/abs/2605.06194)).
Note that the code and the following readme was written by LLMs.
We plan to make more thoroughly checked versions available in due course.

The main file is `reproduce.ipynb`, an executable
Jupyter notebook that develops the reproduction from the mathematical setup
through the final fact checks. It includes explanatory text, LaTeX,
worked examples, sample catalogue records, and recorded output from a complete
six-voter run.

The accompanying `enumerate_antichains.c` program performs the expensive
purely combinatorial search for candidate type families, including
canonicalization under voter relabeling.  The notebook compiles and invokes it
when rebuilding a catalogue.

All continuous feasibility questions use Z3's exact rational arithmetic.
Integral committees are enumerated directly.  There is no floating-point LP.

## Installation

Python 3.10 or newer and a C11 compiler are required.

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r requirements.txt
```

## Reading and running the notebook

Start Jupyter from this directory:

```sh
jupyter lab reproduce.ipynb
```

Read and run the cells from top to bottom.  The configuration cell near the
top controls:

- `N`, which is either 6 or 7;
- `JOBS`, the number of parallel workers;
- `REBUILD_CATALOGUE`, which selects a full rebuild or a fact-property recheck
  of the bundled precomputed catalogue; and
- `OUTPUT`, the result directory.

The defaults perform a complete six-voter reproduction and write to
`notebook-results-n6/`.  For the complete seven-voter reproduction, set `N=7`
and leave `REBUILD_CATALOGUE=True`.

The same configuration is available through environment variables for
headless execution.  For example:

```sh
CORE67_N=6 CORE67_REBUILD=1 jupyter nbconvert \
  --to notebook --execute --inplace reproduce.ipynb

CORE67_N=7 CORE67_REBUILD=1 jupyter nbconvert \
  --to notebook --execute --inplace reproduce.ipynb \
  --ExecutePreprocessor.timeout=20000
```

The seven-voter run is dominated by catalogue construction.  A complete
four-worker run on an Apple M1 Pro MacBook Pro (8 cores, 16 GB RAM), using Z3
4.16.0, took 9,227 seconds (2 h 33 min 47 s):

- antichain enumeration: 77.8 seconds for 228,853 canonical candidates;
- exact candidate-to-hole verification: 9,126.4 seconds;
- post-catalogue fact verification: 22.9 seconds.

To perform only the fact-property checks on the bundled precomputed seven-voter
catalogue, use:

```sh
CORE67_N=7 CORE67_REBUILD=0 jupyter nbconvert \
  --to notebook --execute --inplace reproduce.ipynb \
  --ExecutePreprocessor.timeout=1000
```

This shortcut does not reproduce the antichain enumeration or catalogue
construction. It checks condition (R7), the two classes in the seven-voter
fact, and the exact `8/9` bound on the saved 54,985-hole catalogue.

## What is checked

The generated catalogue imposes conditions (R1)--(R6) from the paper and then
checks every compatible committee size and utility vector for fractional
feasibility and integral infeasibility. Thus the reported 54,985 seven-voter
holes are exactly the candidate minimal holes in the finite search space used
in the proof.

For six voters, the notebook checks that there are 50 holes on 23 antichain
families. For every voter `i` in every hole, it checks that every fractional
witness gives utility exactly `u_i` and that `u-e_i` is integrally feasible.

For seven voters, it checks that 21,818 of the 54,985 holes satisfy the
Lindahl-compatibility condition (R7). It checks that 21,520 belong to class
(1) of the fact and that the remaining 298 belong to class (2). For every
class (2) hole and voter, it checks that `u-e_i` is integrally feasible and
proves over the closed beta polytope that

```text
beta_i + k - sum_j u_j beta_j <= 8/9
```

The notebook always exits with an error if a paper count or fact-property
check differs from the expected result.
