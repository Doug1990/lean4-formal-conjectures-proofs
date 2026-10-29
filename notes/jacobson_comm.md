# Jacobson.jacobson_conjecture_of_comm_ring

- Source: FormalConjectures/Wikipedia/Jacobson.lean:58 (category textbook)
- Date: 2026-10-29

Proof idea: Krull's intersection theorem in the form `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`
(Mathlib, RingTheory/Filtration.lean): for a Noetherian commutative ring R, a finite R-module M and
an ideal I contained in the Jacobson radical, ⋂ₙ Iⁿ·M = 0. Apply it with M = R and I = Ring.jacobson R
(using `Ideal.jacobson_bot : jacobson ⊥ = Ring.jacobson R`), and rewrite Iⁿ • ⊤ = Iⁿ via `Ideal.mul_top`.
The definition `JacobsonConjectureFor` is restated locally (identical text) because the project's
`FormalConjecturesUtil` import is not built; targeted Mathlib imports are used.

Axioms: `[propext, Classical.choice, Quot.sound]`
