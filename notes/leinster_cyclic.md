# LeinsterGroup.cyclic_of_perfect_is_leinster

- Source: `FormalConjectures/Wikipedia/LeinsterGroup.lean` (category API)
- Statement unchanged; `import Mathlib` is used in place of `FormalConjecturesUtil` (see ledger notes), and `IsLeinster` is restated verbatim.

**Proof idea.** Write n = |G|. Because G is perfect, ∑_{d ∣ n} d = 2n (`Nat.perfect_iff_sum_divisors_eq_two_mul`). The map H ↦ |H| from normal subgroups to `n.divisors` is a bijection, and `Finset.sum_bij` turns the first sum into the second. Each value is a divisor by Lagrange. For injectivity (helper `subgroup_eq_of_card_eq`): if |K| = d, then K contains all solutions of x^d = 1, since K already lies inside that solution set and in a cyclic group the set has at most d elements (`IsCyclic.card_pow_eq_one_le`). So any H with |H| = d satisfies H ≤ K, and equal cardinalities give H = K. For surjectivity, take a generator g and d·m = n. Then zpowers(g^m) has order n/m = d, and it is normal because cyclic groups are commutative.

Axioms: `'LeinsterGroup.cyclic_of_perfect_is_leinster' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-27
