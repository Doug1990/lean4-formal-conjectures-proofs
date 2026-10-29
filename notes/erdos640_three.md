# Erdos640.erdos_640.variants.three

- Source: `FormalConjectures/ErdosProblems/640.lean:55` (category textbook)
- Statement: every graph on `Fin n` with chromatic number ≥ 3 has an odd cycle whose vertex set induces a subgraph with chromatic number ≥ 3.

Proof idea: since χ ≥ 3, G is not 2-colourable. By `two_colorable_iff_forall_loop_even`, G therefore has a closed walk of odd length. `exists_odd_cycle` turns it into an odd cycle by strong induction on the length. Write the walk as `cons h p`. If p is a path, the edge back to the start is not in p, because otherwise p has length 1 and the walk length 2 would be even. So the walk is a cycle (`cons_isCycle_iff`). If p is not a path, `isPath_iff_isSubwalk_imp_nil` gives a nontrivial closed subwalk c with p = r1 ++ c ++ r2. Both c and `cons h (r1 ++ r2)` are shorter, and one of them has odd length, so recurse. Finally, `lift` copies the cycle into the subgraph induced on its support with the same length. That subgraph then has an odd closed walk, so its χ ≥ 3 by `Walk.three_le_chromaticNumber_of_odd_loop`.

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-10-29 (2 compiles; the first was clean without `#print axioms`)
