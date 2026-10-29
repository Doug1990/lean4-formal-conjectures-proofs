# Erdos780.erdos_780.variants.sharp

- Source: `FormalConjectures/ErdosProblems/780.lean:60` (category textbook)
- Date: 2026-10-29
- Compiles: 3 (1: `positivity` not loaded with targeted imports; 2: `#print axioms` placed before the theorem; 3: clean)

Proof idea: for k = 1 the vertex set has r − 1 elements, so no r-edge exists. For k ≥ 2 the vertices
0..(t−1)(k−1)−1 are cut into t−1 blocks of size k−1, and the remaining k·r−1 vertices form the last
block. An edge e gets colour min(t−1, min(e)/(k−1)), i.e. the first block it meets. If k disjoint
edges of colour i < t−1 existed, their k distinct minima would all lie in block i of size k−1
(injection via `min % (k−1)`, pigeonhole). If they had colour t−1, all of them would lie in the last
block, and their disjoint union of size k·r would inject into `range (k·r−1)`. The theorem in the
checkout uses a reversed block order, which is the same up to relabelling the vertices.

Axioms: `'Erdos780.erdos_780.variants.sharp' depends on axioms: [propext, Classical.choice, Quot.sound]`
