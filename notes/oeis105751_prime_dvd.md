# OeisA105751.prime_divides_some_term

- Source: `FormalConjectures/OEIS/105751.lean`, line 72 (category textbook, AMS 11)
- Statement: for every prime p there is n with a(n) ≠ 0 and p ∣ a(n), where a(n) = ⌊Im ∏_{k=0}^n (1 + k i)⌋.
- Result file: `results/oeis105751_prime_dvd.lean` (targeted imports, no `import Mathlib`; definition `a` and the statement copied verbatim)

## Proof idea
The complex product equals the image of the product P(N) = ∏_{k<N} (1 + k i) in ℤ[i] (formalised as `QuadraticAlgebra ℤ (-1) 0`), so a(n) = Im P(n+1). Reduce mod q with an explicit ring hom ℤ[i] → (ZMod q)[i]. The factors are q-periodic mod q, so P(mq) ≡ Q_q^m with Q_q = ∏_{k<q}(1 + k i). For an odd prime p, conjugation permutes the factors {1 + j i : j ∈ ZMod p} (j ↦ −j), so Q_p is self-conjugate, 2·Im Q_p = 0, and Im Q_p = 0 because 2 is invertible. Then Q_p^m is "real" and p ∣ Im P(mp). For nonvanishing, mod 3: Q_3 ≡ 2 and P(3m+2) ≡ 2^m(1 + i), so 3 ∤ Im P(3m+2). For a prime p ≥ 5, choose m ∈ {1,2} with mp ≡ 2 (mod 3) and take n = mp − 1. Then p ∣ a(n), and 3 ∤ a(n), so a(n) ≠ 0. The cases p = 2 (n = 4, a = −40) and p = 3 (n = 2, a = 3) are checked by kernel `decide` on ℤ[i].

## Axioms
`'OeisA105751.prime_divides_some_term' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-28. 3 compiles (only lint warnings remain).
