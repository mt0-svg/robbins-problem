<h1 align="center">The value of Robbins' problem is larger than 2</h1>

<p align="center">
  <a href="https://github.com/mt0-svg/robbins-problem/releases/latest/download/robbins.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.23124501"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.23124501.svg"></a>
  <a href="https://mt0-svg.github.io/robbins-problem/run.html"><img alt="Lean Proved" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Frobbins-problem%2Fbadges%2Flean.json"></a>
  <a href="https://mt0-svg.github.io/robbins-problem/run.html"><img alt="Lean Comparator" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Frobbins-problem%2Fbadges%2Fcomparator.json"></a>
  <a href="https://mt0-svg.github.io/robbins-problem/run.html"><img alt="Computation Certificates" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Frobbins-problem%2Fbadges%2Fcertificates.json"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

Robbins' problem asks for the least expected rank $`V(n)`$ of a value selected by a stopping rule from $`n`$ independent uniform values shown one at a time, with full information, and for its limit $`V`$. We prove that $`V(n)>2.0038`$ for every $`n\ge300`$, so that $`V>2`$. This answers a question of Bruss and Ferguson, who asked in 1996 whether $`V>2`$. The proof relaxes the problem to one in which only the five smallest values seen are remembered and each value that leaves the memory is charged the probability that all later values exceed it. A lower bound for the relaxed problem with $`300`$ values is certified by finite tables of values and slopes on geometric grids, in exact integer arithmetic. The proof is computer-assisted, and the whole of it, the check of the certificate included, is formalized in Lean 4 with Mathlib.

The question is the one of p. 7 of F. T. Bruss and T. S. Ferguson, Half-prophets and Robbins' problem of minimizing the expected rank, [Lecture Notes in Statist. 114 (1996)](https://doi.org/10.1007/978-1-4612-0749-8_1), and of Section 8 of F. T. Bruss, What is known about Robbins' problem?, [J. Appl. Probab. 42 (2005)](https://doi.org/10.1239/jap/1110381374).

```lean
theorem Robbins.main_so : ∀ n ≥ 300, ((137704521264 : ℝ) / 2 ^ 36) ≤ Robbins.v n
theorem Robbins.main_so_limit :
    ∀ V : ℝ, Filter.Tendsto Robbins.v Filter.atTop (nhds V) → (137704521264 : ℝ) / 2 ^ 36 ≤ V
```

## What is checked

- **Lean 4.** `Robbins.main_so` and `Robbins.main_so_limit` state Theorem 1.2 of the paper for the definitions of `Robbins/Statement.lean`, where `Robbins.v n` is the infimum of the expected rank over all stopping rules for `n` values. The first has no hypothesis; the second assumes only that its number is a limit of the sequence. Both use only the axioms `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no `native_decide`. The Lean kernel checks the tables of the certificate by evaluation, with no compiled code: a checker written in Lean, proved sound, runs on the data modules. CI runs Comparator on the ten theorems of `config.json` (Theorem 1.2 as `main_so` and `main_so_limit`, with `v300` and `two_lt_v`; Proposition 2.4; Theorems 2.2 and 2.3; Proposition A.1; and `lower_bound_of_base` and `limit_lower_bound_of_base`, the steps from `v 300` to every `n ≥ 300` and to the limit) against `Robbins/Challenge.lean`, which imports only Mathlib, with nanoda, a second implementation of the Lean kernel, checking every declaration they depend on. Before the release, Comparator with nanoda passed on two parts of this list, on the machine of Section 6.3 of the paper: `v300`, `main_so`, `main_so_limit` and `two_lt_v`, and Theorems 2.2 and 2.3, Proposition A.1 and the two steps (Section 6.1 of the paper). On the machine of Section 6.3 of the paper, nanoda checks the 59335 declarations behind the five theorems of `Robbins/Main.lean`, the two main theorems among them, in 55 minutes on four threads, with less than 9.1 GB of memory. The badge Lean Proved gives the number of hypotheses and axioms of these ten theorems, as `code/formal-proof/facts.lean` counts them: a hypothesis is a binder whose type is a proposition that mentions no earlier binder, so `n ≥ 300` in `main_so`, the limit assumption of `main_so_limit` and `c ≤ v N` in the two steps, which restrict quantified variables, are not counted. [`STATEMENTS.md`](STATEMENTS.md) gives, for each numbered statement of the paper, its Lean declarations.
- **The data modules.** The Lean modules of the tables and of the theorems that check them (300 tables, 4837 theorems by evaluation) are not committed: `code/formal-proof/gen.sh` writes them from the tables of the program `soq` (`code/soq`), and their sha256 are listed in `code/formal-proof/modules.sha256`. The tables of the paper were computed with Rust 1.101 (nightly of 2026-10-01); the repository pins Rust 1.98.1, with which `soq` writes the same grid file and the same 300 tables, byte for byte (their sha256 are in `code/soq/out/tables.sha256`). The proof does not trust `soq`, whose tables the kernel checks.
- **PARI/GP.** `code/gp/numbers.gp` prints the numbers of the paper that follow from the grid file and the output of `soq`.

CI (`.github/workflows/ci.yml`) reruns all of it before every release: `soq` and the data modules, the Lean build as a chain of jobs of at most 300 minutes, the axioms, a scan of the sources of `Robbins/` (the generated modules under `RobbinsSO/` are pinned by `code/formal-proof/modules.sha256` and covered by the axiom check and Comparator), Comparator with nanoda, and the PARI/GP script against its recorded output. The logs of that run give the time of each step. [`code/README.md`](code/README.md) describes the programs.

## Layout

| Path                                                             | Content                                                                                                  |
| ---------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------- |
| `Robbins/`                                                       | the Lean proof (Lean and Mathlib `v4.34.1`)                                                              |
| `Robbins/Statement.lean`                                         | the definitions of the statement: the law of the values, the stopping rules, the rank, `v n`             |
| `Robbins/Challenge.lean`, `Robbins/Solution.lean`, `config.json` | the statements with `sorry`, their proofs, and the Comparator configuration                              |
| `RobbinsSO/`                                                     | the data modules, written by `code/formal-proof/gen.sh` (not committed)                                  |
| `code/`                                                          | `soq`, which writes the tables, `so-pack` and `gen.sh`, which write the data modules, the PARI/GP script |
| `paper/`                                                         | the TeX source and `statement_map.sh` (which writes `STATEMENTS.md`)                                     |

The files of `Robbins/` other than `Challenge.lean` and `Solution.lean` are the Lean sources that were checked, with only their comments edited. They are left in the form that was checked and not converted to the Lean module system.

## Check and reuse

The data modules, from the tables of `soq` (times measured on the machine of Section 6.3 of the paper, six threads):

```sh
code/soq/run.sh /tmp/robbins-tables > soq.txt && cmp soq.txt code/soq/out/soq-m5-n300-r1.3-w0.35-14.txt  # 5 s once built
code/formal-proof/gen.sh N300 /tmp/robbins-tables . all  # 48 s
sha256sum --quiet -c code/formal-proof/modules.sha256  # under a second
```

Fast check, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive
lake build --no-build       # nothing left to build
rm -f .lake/build/lib/lean/Robbins/Challenge.* .lake/build/ir/Robbins/Challenge.*
# then Comparator, as the job comparator of .github/workflows/ci.yml runs it
```

Full check, from source, then Comparator (the step modules of the data peak near 2.5 GB each and the modules Chain, Final and Main near 8 GB, so the script builds the step modules four at a time and the heavy ones one at a time). On the machine of Section 6.3, a single `lake build` of the package with its data modules, at `LEAN_NUM_THREADS=4`, took 58 minutes, with at most 8.6 GB for one process; `clean_build.sh` was not timed there. Comparator, with nanoda on four threads, took 81 minutes there, the build in its sandbox included, with less than 12 GB of memory, on the four theorems of Section 6.1 of the paper (`v300`, `main_so`, `main_so_limit`, `two_lt_v`, against a challenge of `Robbins/Statement.lean`); the full list of `config.json` has not been run outside CI:

```sh
lake exe cache get && code/formal-proof/clean_build.sh
```

The PARI/GP script:

```sh
cd code/gp && gp -q numbers.gp < /dev/null | diff - numbers.out  # under a second
```

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "robbins"
git = "https://github.com/mt0-svg/robbins-problem"
rev = "v1.0.0"
```

then `lake update robbins`, `lake exe cache get` and `lake build`, which downloads the build archive of the release. A module that imports `Robbins.Main` also needs the data modules, written by `code/formal-proof/gen.sh` in the directory of the package.

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export) and [landrun](https://github.com/zouuup/landrun): the check of the statements in CI.
- [nanoda](https://github.com/ammkrn/nanoda_lib) of Chris Bailey (Apache 2.0), commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`: the second implementation of the Lean kernel, which Comparator runs to check again every declaration the theorems depend on.
- L. Lamport, Multiple byte processing with full-word instructions, Comm. ACM 18(8), 1975: the arithmetic on several numbers packed in one integer, in `Robbins/Lanes`.
- T. Granlund and P. L. Montgomery, Division by invariant integers using multiplication, PLDI 1994: the division by a constant by a multiplication and a shift (`divC`), in `Robbins/Lanes`.
- [Rust](https://www.rust-lang.org/) with [rayon](https://github.com/rayon-rs/rayon) (MIT or Apache 2.0): the program `soq`.
- [PARI/GP](https://pari.math.u-bordeaux.fr/): the numbers of the paper.

## Citation

```bibtex
@misc{robbins,
  title     = {The value of {R}obbins' problem is larger than 2},
  author    = {{mt0-svg}},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23124501},
  url       = {https://doi.org/10.5281/zenodo.23124501}
}
```

## Contact

Questions and corrections: [open an issue](https://github.com/mt0-svg/robbins-problem/issues/new/choose).

## License

Apache 2.0 (`LICENSE`, `NOTICE`).
