# Erdos508.HadwigerNelsonAtLeast4

- Source: `FormalConjectures/ErdosProblems/508.lean:88` (category research solved, `4 ≤ χ(ℝ²)`).
- `UnitDistancePlaneGraph` is restated locally, same definition as
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/UnitDistancePlaneGraph.lean`. Targeted Mathlib imports are used.

Proof idea: the Moser spindle. With s = √3, t = √11 the seven points are A=(0,0), B=(s/2,1/2), C=(s/2,−1/2),
D=(s,0) (two equilateral triangles ABC, BCD), and the same rhombus rotated about A by θ with cos θ = 5/6,
sin θ = t/6: B'=(5s/12−t/12, st/12+5/12), C'=(5s/12+t/12, st/12−5/12), D'=(5s/6, st/6), so |DD'| = 1.
Every one of the 11 unit distances becomes a polynomial identity in s, t, which `ring_nf` plus s²=3, t²=11 settles.
A 3-colouring of the plane restricts to these points. Triangles ABC and BCD force colour(D) = colour(A),
and likewise colour(D') = colour(A), which contradicts the edge DD' (`omega` on the Fin 3 values). So the graph is
not 3-colourable, and `chromaticNumber_le_iff_colorable` gives 4 ≤ χ.

Axioms: `'Erdos508.HadwigerNelsonAtLeast4' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-29
