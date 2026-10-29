# Erdos770.Nat.Prime.h_eq_add_one

- Source: `FormalConjectures/ErdosProblems/770.lean:45` (category textbook, AMS 11)
- Statement: for `2 < n`, `h n = n + 1 ↔ (n + 1).Prime`, where `h n` is the least `m > 2` with
  `gcd(2^n - 1, …, m^n - 1) = 1`.

## Proof idea
If a prime q divides every i^n − 1 for 2 ≤ i ≤ m, then q > m (otherwise i = q gives 0 ≡ 1), so
1, …, m are m distinct roots of X^n − 1 in ZMod q, and so m ≤ n. Hence the gcd is 1 for every
m ≥ n + 1, so h n ≤ n + 1. If n + 1 = p is prime, Fermat gives p | i^n − 1 for all 2 ≤ i ≤ n, so no
m ≤ n works and h n = n + 1. If n + 1 = a·b is composite (2 ≤ a, b ≤ n), then the gcd at m = n is
already 1: such a q would have q > n and q ≠ n + 1. So q > n + 1, and n + 1 = a·b is also a root,
which gives n + 1 distinct roots, a contradiction. So h n ≤ n < n + 1.

## Axioms
`'Erdos770.Nat.Prime.h_eq_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-29. 3 compiles (1: missing `Fact q.Prime` for `zero_ne_one` in ZMod q, plus deprecation lints; 2: clean; 3: axioms).
Reusable helpers: `roots_of_dvd`, `le_of_roots` (≤ n distinct n-th roots of unity mod q), `gcd_eq_one_iff`.
