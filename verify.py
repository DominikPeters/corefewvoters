#!/usr/bin/env python3
"""Reproduce the computational checks in Section 5 of core67voters.tex.

The C helper enumerates candidate antichains.  This program performs every
mathematical feasibility check with exact Z3 rational arithmetic and every
integral check by exhaustive enumeration of committees.
"""
from __future__ import annotations

import argparse
import gzip
import io
import itertools
import json
import os
import subprocess
import time
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from pathlib import Path
from typing import Iterable, Sequence

from z3 import Q, Real, Solver, Sum, sat, unsat


EXPECTED = {
    6: {"holes": 50, "families": 23, "important": 40},
    7: {
        "holes": 54_985,
        "families": 10_292,
        "important": 21_818,
        "pinned_patchable": 21_520,
        "exceptions": 298,
    },
}


def popcount(mask: int) -> int:
    return mask.bit_count()


def bit_string(mask: int, n: int) -> str:
    return "".join("1" if mask >> i & 1 else "0" for i in range(n))


def dominates(a: Sequence[int], b: Sequence[int]) -> bool:
    return all(x >= y for x, y in zip(a, b))


def committee_utilities(types: Sequence[int], k: int, n: int) -> list[tuple[int, ...]]:
    """Utilities of all size-k committees.

    It suffices to use exactly k candidates: any smaller committee can be
    padded with unused candidates without decreasing utilities.
    """
    result = []
    for committee in itertools.combinations(types, k):
        result.append(tuple(sum(mask >> i & 1 for mask in committee) for i in range(n)))
    return result


def witness_solver(types: Sequence[int], k: int, utility: Sequence[int]) -> tuple[Solver, list]:
    x = [Real(f"x_{j}") for j in range(len(types))]
    solver = Solver()
    for value in x:
        solver.add(value >= 0, value <= 1)
    solver.add(Sum(x) <= k)
    for i, target in enumerate(utility):
        solver.add(Sum([x[j] for j, mask in enumerate(types) if mask >> i & 1]) >= target)
    return solver, x


def fractionally_feasible(types: Sequence[int], k: int, utility: Sequence[int]) -> bool:
    solver, _ = witness_solver(types, k, utility)
    return solver.check() == sat


@lru_cache(maxsize=2)
def permutation_data(n: int) -> tuple[tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...]]:
    permutations = tuple(itertools.permutations(range(n)))
    tables = []
    for permutation in permutations:
        table = []
        for mask in range(1 << n):
            image = sum(1 << permutation[i] for i in range(n) if mask >> i & 1)
            table.append(image)
        tables.append(tuple(table))
    return permutations, tuple(tables)


def canonical_utilities(types: tuple[int, ...], utilities: Iterable[tuple[int, ...]], n: int):
    """Quotient utilities by automorphisms of an already-canonical family."""
    permutations, tables = permutation_data(n)
    automorphisms = [
        permutation
        for permutation, table in zip(permutations, tables)
        if tuple(sorted(table[mask] for mask in types)) == types
    ]
    result = set()
    for utility in utilities:
        images = []
        for permutation in automorphisms:
            image = [0] * n
            for old, new in enumerate(permutation):
                image[new] = utility[old]
            images.append(tuple(image))
        result.add(min(images))
    return sorted(result)


def verify_family(arguments) -> list[dict]:
    """Enumerate the holes supported by one canonical antichain.

    Integral infeasibility and the elementary total-utility bound are checked
    first.  Z3 is called only for the surviving utility vectors.
    """
    n, types = arguments
    types = tuple(types)
    degrees = [sum(mask >> i & 1 for mask in types) for i in range(n)]
    sizes = sorted((popcount(mask) for mask in types), reverse=True)
    raw_holes: list[tuple[int, tuple[int, ...]]] = []

    for k in range(2, len(types) - 1):
        upper = tuple(min(degrees[i], k) - 1 for i in range(n))
        integral = committee_utilities(types, k, n)
        if any(dominates(vector, upper) for vector in integral):
            continue
        size_bound = sum(sizes[:k])
        for utility in itertools.product(*(range(1, bound + 1) for bound in upper)):
            if sum(utility) > size_bound:
                continue
            if any(dominates(vector, utility) for vector in integral):
                continue
            if fractionally_feasible(types, k, utility):
                raw_holes.append((k, utility))

    if not raw_holes:
        return []
    by_k: dict[int, list[tuple[int, ...]]] = defaultdict(list)
    for k, utility in raw_holes:
        by_k[k].append(utility)
    result = []
    for k, utilities in by_k.items():
        for utility in canonical_utilities(types, utilities, n):
            result.append({
                "types": [bit_string(mask, n) for mask in types],
                "masks": list(types),
                "k": k,
                "u": list(utility),
            })
    return result


def price_solver(types: Sequence[int], n: int, *, positive: bool) -> tuple[Solver, list]:
    beta = [Real(f"beta_{i}") for i in range(n)]
    solver = Solver()
    for value in beta:
        solver.add(value > 0 if positive else value >= 0, value <= 1)
    for mask in types:
        solver.add(Sum([beta[i] for i in range(n) if mask >> i & 1]) == 1)
    return solver, beta


def patchable_voters(types: Sequence[int], k: int, utility: Sequence[int], n: int) -> list[int]:
    integral = committee_utilities(types, k, n)
    result = []
    for i in range(n):
        target = list(utility)
        target[i] -= 1
        if any(dominates(vector, target) for vector in integral):
            result.append(i)
    return result


def pinned_voters(types: Sequence[int], k: int, utility: Sequence[int], n: int) -> list[int]:
    solver, x = witness_solver(types, k, utility)
    if solver.check() != sat:
        raise AssertionError("catalogue contains a fractionally infeasible entry")
    result = []
    for i in range(n):
        # Feasibility already forces load_i >= utility_i.  Consequently the
        # strict counterexample below is unsatisfiable exactly when every
        # witness gives voter i the integer utility utility_i.
        load = Sum([x[j] for j, mask in enumerate(types) if mask >> i & 1])
        solver.push()
        solver.add(load > utility[i])
        verdict = solver.check()
        solver.pop()
        if verdict == unsat:
            result.append(i)
    return result


def analyze_family(arguments) -> dict:
    """Analyze all holes on one family, sharing its price-feasibility check."""
    n, records = arguments
    types = tuple(records[0]["masks"])
    live_solver, _ = price_solver(types, n, positive=True)
    live = live_solver.check() == sat
    result = {"holes": len(records), "live": len(records) if live else 0, "checked": []}

    for record in records:
        utility, k = record["u"], record["k"]
        entry = {}
        if n == 6 or live:
            patch = patchable_voters(types, k, utility, n)
            pin = pinned_voters(types, k, utility, n)
            entry.update({"record": record, "patch": patch, "pin": pin, "ok": bool(set(patch) & set(pin))})
        if entry:
            result["checked"].append(entry)
    return result


def rational_value(model, expression) -> str:
    value = model.eval(expression, model_completion=True)
    return f"{value.numerator_as_long()}/{value.denominator_as_long()}"


def check_small_surplus(exceptions: Sequence[dict], n: int) -> dict:
    """Prove the 8/9 bound by exact counterexample queries, and show sharpness."""
    bound = Q(8, 9)
    equality_witness = None
    for exception in exceptions:
        record = exception["record"]
        types, utility, k = record["masks"], record["u"], record["k"]
        solver, beta = price_solver(types, n, positive=False)
        for i in range(n):
            expression = beta[i] + k - Sum([utility[j] * beta[j] for j in range(n)])
            solver.push()
            solver.add(expression > bound)
            verdict = solver.check()
            solver.pop()
            if verdict != unsat:
                raise AssertionError(f"small-surplus bound fails for {record}, voter {i + 1}")
            if equality_witness is None:
                solver.push()
                solver.add(expression == bound)
                if solver.check() == sat:
                    model = solver.model()
                    equality_witness = {
                        "record": record,
                        "voter": i + 1,
                        "value": "8/9",
                        "beta": [rational_value(model, value) for value in beta],
                    }
                solver.pop()
    if equality_witness is None:
        raise AssertionError("the 8/9 upper bound was verified but not attained")
    return {"bound": "8/9", "attained": True, "witness": equality_witness}


def load_catalogue(path: Path) -> list[dict]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        records = json.load(stream)
    for record in records:
        if "masks" not in record:
            record["masks"] = [
                sum(1 << i for i, bit in enumerate(bits) if bit == "1") for bits in record["types"]
            ]
    return records


def write_gzip_json(path: Path, value) -> None:
    with path.open("wb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as compressed:
            with io.TextIOWrapper(compressed, encoding="utf-8") as text:
                json.dump(value, text, separators=(",", ":"), sort_keys=True)


def generate_candidates(n: int, jobs: int, output: Path) -> tuple[list[tuple[int, ...]], float]:
    start = time.time()
    source = Path(__file__).with_name("enumerate_antichains.c")
    binary = output / f"enumerate-n{n}"
    subprocess.run(
        [os.environ.get("CC", "cc"), "-O3", "-std=c11", f"-DNV={n}", str(source), "-o", str(binary)],
        check=True,
    )
    processes = []
    handles = []
    for worker in range(jobs):
        candidates = output / f"candidates-{worker}.txt"
        log = (output / f"enumerator-{worker}.txt").open("w", encoding="utf-8")
        handles.append(log)
        processes.append(subprocess.Popen(
            [str(binary), str(candidates), str(worker), str(jobs)], stdout=log, stderr=subprocess.STDOUT
        ))
    for process in processes:
        if process.wait() != 0:
            raise RuntimeError("antichain generator failed; see enumerator logs")
    for handle in handles:
        handle.close()

    lines = set()
    for worker in range(jobs):
        lines.update((output / f"candidates-{worker}.txt").read_text(encoding="utf-8").splitlines())
    families = sorted(tuple(map(int, line.split())) for line in lines if line.strip())
    (output / "candidates.txt").write_text(
        "".join(" ".join(map(str, family)) + "\n" for family in families), encoding="utf-8"
    )
    elapsed = time.time() - start
    print(f"antichain enumeration: {len(families):,} candidates in {elapsed:.1f}s", flush=True)
    return families, elapsed


def build_catalogue(n: int, jobs: int, output: Path) -> tuple[list[dict], dict]:
    start = time.time()
    families, enumeration_seconds = generate_candidates(n, jobs, output)
    verification_start = time.time()
    arguments = [(n, family) for family in families]
    chunksize = max(1, len(arguments) // max(1, jobs * 64))
    records = []
    if jobs == 1:
        for arguments_for_family in arguments:
            records.extend(verify_family(arguments_for_family))
    else:
        with ProcessPoolExecutor(max_workers=jobs) as pool:
            for result in pool.map(verify_family, arguments, chunksize=chunksize):
                records.extend(result)
    records.sort(key=lambda record: (record["masks"], record["k"], record["u"]))
    write_gzip_json(output / f"holes{n}.json.gz", records)
    verification_seconds = time.time() - verification_start
    total_seconds = time.time() - start
    print(f"hole verification: {len(records):,} holes in {verification_seconds:.1f}s", flush=True)
    return records, {
        "candidate_antichains": len(families),
        "antichain_enumeration_seconds": round(enumeration_seconds, 3),
        "hole_verification_seconds": round(verification_seconds, 3),
        "catalogue_total_seconds": round(total_seconds, 3),
    }


def analyze_catalogue(n: int, records: list[dict], jobs: int) -> tuple[dict, list[dict]]:
    groups: dict[tuple[int, ...], list[dict]] = defaultdict(list)
    for record in records:
        groups[tuple(record["masks"])].append(record)
    arguments = [(n, group) for _, group in sorted(groups.items())]
    chunksize = max(1, len(arguments) // max(1, jobs * 32))
    if jobs == 1:
        results = [analyze_family(arguments_for_family) for arguments_for_family in arguments]
    else:
        with ProcessPoolExecutor(max_workers=jobs) as pool:
            results = list(pool.map(analyze_family, arguments, chunksize=chunksize))

    checked = [entry for result in results for entry in result["checked"]]
    important = sum(result["live"] for result in results)
    summary = {
        "n": n,
        "holes": len(records),
        "families": len(groups),
        "important": important,
    }
    exceptions = []
    if n == 6:
        summary.update({
            "all_voters_pinned": all(len(entry["pin"]) == n for entry in checked),
            "all_voters_patchable": all(len(entry["patch"]) == n for entry in checked),
        })
    else:
        exceptions = [entry for entry in checked if not entry["ok"]]
        summary.update({
            "pinned_patchable": len(checked) - len(exceptions),
            "exceptions": len(exceptions),
            "exceptions_patchable_at_every_voter": all(len(entry["patch"]) == n for entry in exceptions),
            "small_surplus": check_small_surplus(exceptions, n),
        })
    return summary, exceptions


def check_expected(summary: dict) -> None:
    expected = EXPECTED[summary["n"]]
    for key, value in expected.items():
        if summary.get(key) != value:
            raise AssertionError(f"expected {key}={value:,}, obtained {summary.get(key)!r}")
    if summary["n"] == 6:
        if not summary["all_voters_pinned"] or not summary["all_voters_patchable"]:
            raise AssertionError("the six-voter pinned/patchable theorem failed")
    else:
        if not summary["exceptions_patchable_at_every_voter"]:
            raise AssertionError("an exceptional seven-voter hole is not patchable everywhere")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, choices=(6, 7))
    parser.add_argument("--jobs", type=int, default=max(1, min(4, os.cpu_count() or 1)))
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--catalogue",
        type=Path,
        help="recheck the theorem on this trusted catalogue instead of rebuilding it",
    )
    args = parser.parse_args()

    output = args.output or Path(f"results-n{args.n}")
    output.mkdir(parents=True, exist_ok=True)
    start = time.time()
    if args.catalogue:
        records = load_catalogue(args.catalogue)
        build_timing = None
    else:
        records, build_timing = build_catalogue(args.n, args.jobs, output)
    analysis_start = time.time()
    summary, exceptions = analyze_catalogue(args.n, records, args.jobs)
    analysis_seconds = time.time() - analysis_start
    summary["elapsed_seconds"] = round(time.time() - start, 3)
    summary["timing"] = {"theorem_analysis_seconds": round(analysis_seconds, 3)}
    if build_timing is not None:
        summary["timing"].update(build_timing)
    summary["z3_version"] = __import__("z3").get_version_string()
    (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if exceptions:
        write_gzip_json(output / "exceptions.json.gz", exceptions)
    check_expected(summary)
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
