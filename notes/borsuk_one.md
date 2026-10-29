# Borsuk.borsuk_conjecture.one

- Source: `FormalConjectures/Wikipedia/BorsukConjecture.lean`, line 183 (category textbook): `BorsukConjecture 1`.
- Draft: `work/borsuk_one.lean`. Uses targeted Mathlib imports. `HasBorsukCover`, `BorsukConjecture` and the scoped `ℝ^n` notation are copied verbatim; the statement is unchanged. Added helpers: `proj1`, `proj1_isometry`, `ediam_half_lt`, `ediam_preimage_lt`.

**Proof idea.** The coordinate map `proj1 : ℝ^1 → ℝ` is an isometry, so it preserves `ediam`, and the image `t` of a bounded set `s` is bounded. Let `a = sInf t` and `b = sSup t`. Then `a < b`, because `s` has two distinct points and `proj1` is injective. Also `ediam s = ediam t = ofReal (b - a)` by `Real.ediam_eq`. Split `s` at the midpoint `m = (a+b)/2` into `s ∩ proj1⁻¹[a,m]` and `s ∩ proj1⁻¹[m,b]`. These two sets cover `s`, and each one maps into an interval of diameter `(b-a)/2 < b-a`, so each has strictly smaller `ediam` than `s`.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-28
