# Erdos748.erdos_748.variants.lower_bound

- Source: `FormalConjectures/ErdosProblems/748.lean:67` (category textbook)
- Date: 2026-10-29
- Compiles: 2 (1: omega did not see through an un-beta-reduced `(fun x y => x + y) x y`; fixed with `beta_reduce`)

Proof idea: every subset of (n/2, n] is sum-free, since two elements > n/2 add up to more than n.
So the powerset of `Finset.Ioc (n/2) n` is contained in the filtered family counted by `f n`, which
gives `2^(n - n/2) ≤ f n`. Then (n:ℝ)/2 ≤ n − ⌊n/2⌋, and monotonicity of `2^x` gives the real bound.
`IsSumFree` (from FormalConjecturesForMathlib, which is not built here) is restated locally with the
same definition `Disjoint (S + S) S`, and `f` is copied verbatim.

Axioms: `'Erdos748.erdos_748.variants.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`
