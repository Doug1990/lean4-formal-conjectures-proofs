# Machine-checked Lean 4 proofs of known results

Lean 4 / Mathlib (v4.33.1) proofs of statements taken from the [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) repository. Each result is a known theorem (category `textbook`, `research solved` or `API` there); nothing here is a new mathematical result.

## How these were produced

**AI-generated.** The proofs were written by Claude (Anthropic) in an unattended agent loop, then re-checked independently by a separate script (`verification/verify-results.ps1`). No human has reviewed the proofs line by line.

Each file was accepted only if:
- it compiles with no errors and no `sorry`,
- `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` (checked for every declaration in the file),
- a static scan finds no `native_decide`, `axiom`, `unsafe`, `macro`, `#eval` and similar,
- the statement matches the one in the formal-conjectures checkout (whitespace-normalised).

Results of the independent check: `verification/verified.csv` (all `PASS`, fidelity `SAME`).

## Caveats

- Definitions from the formal-conjectures helper libraries are **copied verbatim** into each file (that library was not built on the machine), and files import `Mathlib` or targeted Mathlib modules. A file is therefore a standalone proof of the same statement, not a drop-in replacement for the repository file.
- Each file has a note in `notes/` with the source file and line in formal-conjectures and a short proof idea.
- Not every file was compiled in this exact repository layout; they were checked inside a formal-conjectures checkout at the same toolchain. If `lake build` reports a problem, please open an issue.

## Contents

| File | Statement / source |
|---|---|
| [Proofs/wolstenholme.lean](Proofs/wolstenholme.lean) ([notes](notes/wolstenholme.md)) | WolstenholmePrime.wolstenholme_theorem |
| [Proofs/wolstenholme_harmonic.lean](Proofs/wolstenholme_harmonic.lean) ([notes](notes/wolstenholme_harmonic.md)) | WolstenholmePrime.wolstenholme_harmonic |
| [Proofs/divisor_dirichlet.lean](Proofs/divisor_dirichlet.lean) ([notes](notes/divisor_dirichlet.md)) | DirichletDivisorProblem.divisor_error_dirichlet |
| [Proofs/erdos770_h.lean](Proofs/erdos770_h.lean) ([notes](notes/erdos770_h.md)) | Erdos770.Nat.Prime.h_eq_add_one |
| [Proofs/erdos770_odd.lean](Proofs/erdos770_odd.lean) ([notes](notes/erdos770_odd.md)) | Erdos770.erdos_770.variants.odd_h_unbounded |
| [Proofs/oeis105751_prime_dvd.lean](Proofs/oeis105751_prime_dvd.lean) ([notes](notes/oeis105751_prime_dvd.md)) | OeisA105751.prime_divides_some_term |
| [Proofs/oeis87719_exists.lean](Proofs/oeis87719_exists.lean) ([notes](notes/oeis87719_exists.md)) | OeisA87719.a_exists |
| [Proofs/congruent1.lean](Proofs/congruent1.lean) ([notes](notes/congruent1.md)) | CongruentNumber.not_congruentNumber_1 |
| [Proofs/jacobson_comm.lean](Proofs/jacobson_comm.lean) ([notes](notes/jacobson_comm.md)) | Jacobson.jacobson_conjecture_of_comm_ring |
| [Proofs/leinster_cyclic.lean](Proofs/leinster_cyclic.lean) ([notes](notes/leinster_cyclic.md)) | LeinsterGroup.cyclic_of_perfect_is_leinster |
| [Proofs/ramsey33.lean](Proofs/ramsey33.lean) ([notes](notes/ramsey33.md)) | RamseyNumbers.ramsey_number_three_three : R(3, 3) = 6 |
| [Proofs/erdos508_four.lean](Proofs/erdos508_four.lean) ([notes](notes/erdos508_four.md)) | Erdos508.HadwigerNelsonAtLeast4 |
| [Proofs/erdos508_seven.lean](Proofs/erdos508_seven.lean) ([notes](notes/erdos508_seven.md)) | Erdos508.HadwigerNelsonAtMostSeven |
| [Proofs/erdos704_cube.lean](Proofs/erdos704_cube.lean) ([notes](notes/erdos704_cube.md)) | Erdos704.erdos_704.variants.cube_colouring |
| [Proofs/erdos640_three.lean](Proofs/erdos640_three.lean) ([notes](notes/erdos640_three.md)) | Erdos640.erdos_640.variants.three |
| [Proofs/erdos261_bl.lean](Proofs/erdos261_bl.lean) ([notes](notes/erdos261_bl.md)) | Erdős 261: Borwein–Loring construction (3 statements) |
| [Proofs/erdos261_two.lean](Proofs/erdos261_two.lean) ([notes](notes/erdos261_two.md)) | Erdős 261: two infinite representations of 7/4 |
| [Proofs/mahler32_consequence.lean](Proofs/mahler32_consequence.lean) ([notes](notes/mahler32_consequence.md)) | Mahler32.mahler_conjecture.variants.consequence |
| [Proofs/c7a_two_le.lean](Proofs/c7a_two_le.lean) ([notes](notes/c7a_two_le.md)) | Constant7a.two_le_irrationalityExponent |
| [Proofs/diophantine4_infinite.lean](Proofs/diophantine4_infinite.lean) ([notes](notes/diophantine4_infinite.md)) | DiophantineTuple: infinitely many integral Diophantine 4-tuples |
| [Proofs/borsuk_one.lean](Proofs/borsuk_one.lean) ([notes](notes/borsuk_one.md)) | Borsuk.borsuk_conjecture.one |
| [Proofs/erdos748_lower.lean](Proofs/erdos748_lower.lean) ([notes](notes/erdos748_lower.md)) | Erdos748.erdos_748.variants.lower_bound |
| [Proofs/erdos780_sharp.lean](Proofs/erdos780_sharp.lean) ([notes](notes/erdos780_sharp.md)) | Erdos780.erdos_780.variants.sharp |

## Build

```
lake exe cache get   # downloads the Mathlib build
lake build
```

## License

Apache License 2.0 (same as Mathlib), see [LICENSE](LICENSE). The statements and the copied definitions come from formal-conjectures (Copyright 2026 The Formal Conjectures Authors, also Apache-2.0); the proofs were generated with Claude (Anthropic).
