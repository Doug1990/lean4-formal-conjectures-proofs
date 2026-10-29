# OeisA87719.a_exists

- Source: `FormalConjectures/OEIS/87719.lean:49` (category textbook)
- Statement: `∀ n, ∃ m, countExceeding n m > countNotExceeding n m`
- Date: 2026-10-29

Proof idea: let B = 3^n and m = 30B. The two counts partition {1,…,m}, so they sum to m = 30B
(`Finset.card_filter_add_card_filter_not`). The injective map g(x) = 6B + 6⌊x/4⌋ + c(x mod 4)
with c ∈ {2,3,4,6} sends {0,…,16B-1} into (6B, 30B]. Every value is divisible by 2 or 3, so its
minFac is ≤ 3, and minFac^n ≤ 3^n = B < g(x). So it is an "exceeding" number. Hence
countExceeding ≥ 16B > 14B ≥ countNotExceeding. The definitions are restated locally and the
file uses targeted imports (no `import Mathlib`).

Axioms: `[propext, Classical.choice, Quot.sound]`
