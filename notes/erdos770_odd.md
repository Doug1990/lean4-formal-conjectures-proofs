# Erdos770.erdos_770.variants.odd_h_unbounded

- Source: `FormalConjectures/ErdosProblems/770.lean:51` (category textbook, AMS 11)
- Statement: `Unbounded (· ≤ ·) (ENat.toNat '' (h '' Odd))`, i.e. h n takes arbitrarily large
  (finite) values on odd n.

## Proof idea
Given m, Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_eq_mod`) gives a prime p > m + 5 with
p ≡ −1 mod 8·m!. Then p ≡ 7 mod 8, so 2 is a square mod p. For each odd prime ℓ ≤ m we have
p ≡ −1 mod ℓ. By quadratic reciprocity (split into ℓ ≡ 1 and ℓ ≡ 3 mod 4, using p ≡ 3 mod 4),
ℓ is a square mod p. By multiplicativity (`Nat.recOnMul`), every 1 ≤ i ≤ m is a square mod p.
Euler's criterion then gives i^((p−1)/2) ≡ 1 mod p. So n = p/2 is odd, and p divides every
i^n − 1 for 2 ≤ i ≤ m, which gives h n ≥ m + 1. Also h n ≤ n + 1 < ⊤ (helper from erdos770_h),
so toNat (h n) > m.

## Axioms
`'Erdos770.erdos_770.variants.odd_h_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-29. 2 compiles (1: clean; 2: axioms). Reuses the helpers from results/erdos770_h.lean.
