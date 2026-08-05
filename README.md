# Reproducing the six- and seven-voter computations

This directory contains the scripts for performing the computational verification used in Section 5 of
"Core Existence in Approval-Based Committee Elections with up to Seven Voter Types"
(Patrick Becker, Matthias Greger, Dominik Peters, [arXiv:2605.06194](https://arxiv.org/abs/2605.06194)).
Note that the code and the following readme was written by LLMs.
We plan to make more thoroughly checked versions available in due course.

There are two executable source files:

- `enumerate_antichains.c` performs only the expensive combinatorial search
  for candidate type families, including canonicalization under voter
  relabeling;
- `verify.py` treats both `n=6` and `n=7`.  It enumerates integral committees
  directly and uses Z3's exact rational arithmetic for every continuous
  feasibility question.  There is no floating-point LP and no custom LP
  implementation.

The generated catalogue is deliberately a **candidate superset**.  It imposes
(R1), (R2), and (R4)--(R6) from the paper, but not (R3).  Thus the reported
54,985 seven-voter holes include every residual relevant to the proof, without
claiming that every listed hole has only strictly interior fractional
witnesses.  The optional interior diagnostic makes this distinction visible.

## Installation

Python 3.10 or newer and a C11 compiler are required.

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r requirements.txt
```

## Full reproduction

Run from this directory:

```sh
python3 verify.py 6 --jobs 4
python3 verify.py 7 --jobs 4
```

The program compiles the C helper, regenerates the candidate antichains,
constructs `holes6.json.gz` or `holes7.json.gz`, and checks the corresponding
theorem.  Outputs go to `results-n6/` and `results-n7/` by default.

The six-voter run is quick.  The seven-voter run is dominated by exhaustive
catalogue construction and is expected to take substantially longer.

For reference, a complete four-worker `n=7` run on an Apple M1 Pro MacBook Pro
(8 cores, 16 GB RAM), using Z3 4.16.0, took 9,227 seconds (2 h 33 min 47 s):

- antichain enumeration: 77.8 seconds for 228,853 canonical candidates;
- exact candidate-to-hole verification: 9,126.4 seconds;
- post-catalogue theorem verification: 22.9 seconds.

The same theorem verification starting from the saved catalogue took about 92
seconds in a single process.  Timings are recorded automatically in
`summary.json`, together with the Z3 version, so results from other machines
can be reported directly.

To recheck a previously generated catalogue without rerunning the antichain
search, use:

```sh
python3 verify.py 7 --jobs 4 --catalogue results-n7/holes7.json.gz
```

To inspect the distinction surrounding (R3), add
`--interior-diagnostics`.  For each checked hole this tests both existence of
a witness with all `0 < x_R < 1` and the stronger claim that no witness has a
coordinate equal to 0 or 1.

## Mathematical checks

For a candidate family `F`, committee size `k`, and integer utility vector
`u`, catalogue membership means:

1. no integral committee of size `k` weakly dominates `u`; and
2. Z3 finds rational values `x_R` satisfying
   `0 <= x_R <= 1`, `sum(x_R) <= k`, and
   `sum(R contains i) x_R >= u_i` for every voter `i`.

It suffices to enumerate committees of exactly size `k`: a smaller committee
can be padded with unused candidates without decreasing any utility.

For the six-voter theorem, for every one of the 50 holes and every voter `i`,
the script checks:

- `u-e_i` is integrally feasible by exhaustive committee enumeration;
- the witness constraints together with `u_i(x) > u_i` are unsatisfiable.
  Hence every fractional witness gives voter `i` exactly the integer utility
  `u_i`.

For seven voters, a hole is called important when Z3 finds strictly positive
`beta_i` with `sum(i in R) beta_i = 1` for every `R` in `F`.  On all important
holes the script computes the patchable and pinned voters as above.  It checks
the expected split into 21,520 pinned-and-patchable holes and 298 exceptions.
For every exceptional hole and every voter `i`, it then proves

```text
beta_i + k - sum_j u_j beta_j <= 8/9
```

over the closed price polytope by asking Z3 for a solution with value greater
than `8/9` and requiring `unsat`.  A separate exact satisfiability check records
a price vector attaining `8/9`.

`summary.json` contains the counts, the sharpness witness, the Z3 version, and
the elapsed time.  Unless `--no-expected` is passed, the program exits with an
error if any paper count or theorem check differs from the expected result.

The fresh generator uses ordinary lexicographic canonical representatives.
The older exploratory catalogue used a different canonical key, so its raw
records are usually labelled differently.  An orbit-level comparison of the
complete catalogues found them identical up to voter relabeling.
