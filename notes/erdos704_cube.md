# Erdos704.erdos_704.variants.cube_colouring

- Source: `FormalConjectures/ErdosProblems/704.lean:91` (category textbook)
- Statement: for every n there is k with the unit distance graph on ℝⁿ k-colourable and k ≤ (2 + √n)ⁿ.

Proof idea: let t = ⌊√n⌋ + 1, so n < t². Colour x ∈ ℝⁿ by the vector (⌊t·xᵢ⌋ mod (t+1))ᵢ ∈ (ZMod (t+1))ⁿ, which uses (t+1)ⁿ colours. Suppose two points at distance 1 get the same colour. If their cube indices differ in some coordinate, they differ by at least t+1 there, so |xᵢ − yᵢ| > 1, which contradicts distance 1. Otherwise they lie in the same cube of side 1/t, so every (xᵢ − yᵢ)²t² < 1. Summing gives t² ≤ n, a contradiction. Finally t + 1 = ⌊√n⌋ + 2 ≤ √n + 2. Helper lemmas: `key` (indices congruent mod m ≥ t+1 means equal or far apart), `key2` (same cube means close), `colour` (colourability with (t+1)ⁿ colours).

Axioms: `propext, Classical.choice, Quot.sound`

Date: 2026-10-29 (2 compiles; the first passed with only a `haveI` style warning)
