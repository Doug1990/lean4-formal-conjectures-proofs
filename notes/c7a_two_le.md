# Constant7a.two_le_irrationalityExponent

- Source: `FormalConjectures/OptimizationConstants/7a.lean:98` (category textbook)
- Statement: `{x : ℝ} (hx : Irrational x) : 2 ≤ irrationalityExponent x`
- `irrationalityExponent` restated verbatim; the API lemma `le_irrationalityExponent_iff` is copied
  with its original proof from the same file. Targeted Mathlib imports (no FormalConjecturesUtil).

**Proof idea.** By `le_irrationalityExponent_iff` it suffices to show `LiouvilleWith z x` for all
`z < 2`, and by monotonicity it suffices to show `LiouvilleWith 2 x` (helper `liouvilleWith_two`, with
C = 1). Given a bound a, let δ > 0 be the minimum of the distances `|kx - round(kx)|` over
1 ≤ k ≤ a+1 (positive since x is irrational). Choose n ≥ a+1 with 1/(n+1) < δ. Dirichlet's lemma
`Real.exists_int_int_abs_mul_sub_le` gives 0 < k ≤ n and j with |kx - j| ≤ 1/(n+1) < δ. This forces
k > a+1, and |x - j/k| ≤ 1/(k(n+1)) < 1/k², with x ≠ j/k by irrationality. So such approximations
occur for arbitrarily large denominators.

**Axioms:** `propext, Classical.choice, Quot.sound`

Date: 2026-10-29
