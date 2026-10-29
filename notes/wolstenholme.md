# WolstenholmePrime.wolstenholme_theorem

- Source: `FormalConjectures/Wikipedia/WolstenholmePrime.lean:39` (category textbook)
- Statement: for a prime p > 3, `(2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]`.

**Proof idea.** Let g(x) = (x+1)(x+2)⋯(x+p−1) ∈ ℤ[x]. Then g(0) = (p−1)! and
g(p) = (p+1)⋯(2p−1) = (p−1)!·C(2p−1, p−1) (via `ascFactorial`). Reflecting the
factors k ↦ p−k shows g(−p) = (−1)^{p−1} g(0) = g(0) since p is odd. For any
integer polynomial, t³ divides g(t) − (c₀ + c₁t + c₂t²). Using this at t = p and
t = −p and adding, the c₁ terms cancel and g(−p) = c₀ gives
g(p) − g(0) ≡ 2c₂p² (mod p³). Over ZMod p, g equals X^{p−1} − 1: both are monic of
degree p−1 and agree on all p−1 nonzero residues (Fermat, plus the vanishing factor
x + (p − x)). So, because p > 3, the x² coefficient is 0 mod p, which gives p | c₂.
This yields p³ | (p−1)!·(C − 1), and (p−1)! is coprime to p³.

Imports are targeted (no `import Mathlib`). Helper lemmas in the file: `cube_dvd_eval_sub`,
`prod_eq_X_pow_sub_one` (ZMod p), `dvd_coeff_two`, `eval_zero_wg`, `eval_neg_wg`, `eval_p_wg`.

Axioms: `'WolstenholmePrime.wolstenholme_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-28. 3 compiles.
