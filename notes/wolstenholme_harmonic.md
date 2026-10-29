# WolstenholmePrime.wolstenholme_harmonic

- Source: `FormalConjectures/Wikipedia/WolstenholmePrime.lean:80` (category textbook)
- Statement: `IsWolstenholmePrime p ↔ p > 7 ∧ Nat.Prime p ∧ ↑(p ^ 3) ∣ (harmonic (p - 1)).num`
- Date: 2026-10-29

Proof idea: let g(X) = (X+1)(X+2)⋯(X+(p-1)) ∈ ℤ[X] with coefficients c_j. By induction,
c_0 = (p-1)! and c_1 = (p-1)!·H_{p-1} (over ℚ). As in the Wolstenholme theorem proof, g(-p) = g(0)
and g(p) = (p-1)!·C(2p-1,p-1); over ZMod p, g = X^(p-1) - 1, so p ∣ c_3 (p > 7). Taylor expansion
mod t^4 at t = ±p gives (p-1)!(C(2p-1,p-1) - 1) = 2p·c_1 + p^4·K. Since (p-1)! and 2 are prime to p,
C(2p-1,p-1) ≡ 1 mod p^4 ⟺ p^3 ∣ c_1. Finally c_1·den(H) = num(H)·(p-1)!, and p ∤ den(H) whenever
p ∣ num(H) (num and den are coprime), so p^3 ∣ c_1 ⟺ p^3 ∣ num(H). The file uses targeted
Mathlib imports and restates `IsWolstenholmePrime` locally.

Axioms: `'WolstenholmePrime.wolstenholme_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound]`
