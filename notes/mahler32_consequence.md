# Mahler32.mahler_conjecture.variants.consequence

- Source: `FormalConjectures/Wikipedia/Mahler32.lean:48` (category textbook)
- Statement: `(H : 1 / 2 < Ω (3 / 2)) : type_of% mahler_conjecture`, i.e. `∀ x, IsZNumber x → False`.
- Note: `type_of% mahler_conjecture` is spelled out as `∀ (x : ℝ) (_hx : IsZNumber x), False` (the same type),
  so the open conjecture does not need a `sorry` stub. A first version with the stub and the literal
  `type_of%` also compiled with the same axioms (only warning: the stub's own `sorry`).
  `IsZNumber` (from FormalConjecturesForMathlib) and `Ω` are restated verbatim; targeted Mathlib imports.

**Proof idea.** Take θ = x for a Z-number x > 0. Since `{x(3/2)^n} < 1/2` for all n ≥ 1, the limsup of
the fractional parts is ≤ 1/2, and their liminf is ≥ 0 (fractional parts lie in [0,1), giving the
coboundedness side conditions). So the oscillation for θ = x is ≤ 1/2 and lies in the set whose inf is
Ω(3/2). If that set is bounded below, `csInf_le` gives Ω(3/2) ≤ 1/2, contradicting H; if not, the real
`sInf` is 0 by convention, again contradicting H.

**Axioms:** `propext, Classical.choice, Quot.sound`

Date: 2026-10-29
