# DiophantineTuple: infinitely many integral Diophantine 4-tuples

- Source: `FormalConjectures/Wikipedia/DiophantineTuple.lean`, line 98 (category textbook): `example : integralDiophantine4Tuple.encard = ⊤`. The source declaration is an anonymous `example`. Here it is named `DiophantineTuple.integralDiophantine4Tuple_encard_eq_top` so that `#print axioms` can be run. The type is unchanged.
- Draft: `work/diophantine4_v2.lean`. Uses targeted Mathlib imports. `IsDiophantineTuple`, `IsIntegralDiophantineTuple` and `integralDiophantine4Tuple` are copied verbatim, because `FormalConjecturesUtil` is not built.

**Proof idea.** We use the parametric family from the docstring, {n, n+2, 4n+4, 16n³+48n²+44n+12}, for n ≥ 1. Each pairwise product plus 1 is an explicit square: (n+1)², (2n+1)², (2n+3)², (4n²+6n+1)², (4n²+10n+5)² and (8n²+16n+7)². Each identity is checked by `ring1`. The four elements are distinct, and the card is 4 (`omega`, with n², n³ generalized to atoms). The map k ↦ family (k+1) is injective because the smallest element is k+1 and smaller values are not members. `Set.infinite_of_injective_forall_mem` then shows the set is infinite, and `Set.Infinite.encard_eq` gives encard = ⊤.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-28
