# Erdős 261: two infinite representations of 7/4

- Statement: `Erdos261.erdos_261.variants.two_representations` (category research solved)
- Source: `FormalConjectures/ErdosProblems/261.lean:110`
- Result file: `results/erdos261_two.lean` (targeted imports; `Erdos261InfiniteRepresentation` restated verbatim)

Proof idea (Rafik's observation, quoted in the source docstring): ∑_{k≥1} k/2^k = 2, and
4/2^4 = 1/4 = 5/2^5 + 6/2^6. So 7/4 is represented both by ℕ_{>0}∖{4} (enumerated by
seqA k = k+1 for k<3, k+2 otherwise) and by ℕ_{>0}∖{5,6} (seqB). In ℝ, the base sum comes from
`hasSum_coe_mul_geometric_of_norm_lt_one` with r = 1/2. Subtracting `hasSum_ite_eq` terms
removes the excluded indices. `Function.Injective.hasSum_iff` moves this to the subsequence,
because outside the range the modified summand is 0 (index 0 contributes 0/1). The real
HasSum is transferred to ℚ through the inducing cast `Rat.castHom ℝ`
(`Topology.IsInducing.hasSum_iff`). That gives Summable and the tsum value in ℚ. The two
sequences differ at index 3, so `Cardinal.two_le_iff` finishes the proof.

Axioms: `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-29
