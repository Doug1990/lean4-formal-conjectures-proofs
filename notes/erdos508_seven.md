# Erdos508.HadwigerNelsonAtMostSeven

- Source: `FormalConjectures/ErdosProblems/508.lean:105` (category textbook, `χ(ℝ²) ≤ 7`).
- `UnitDistancePlaneGraph` is restated locally, same definition as
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/UnitDistancePlaneGraph.lean`. Targeted Mathlib imports are used.

Proof idea: instead of the hexagon tiling, the proof uses a sheared brick tiling. Bricks are half-open rectangles of
width 4/5 and height 11/20, so every brick has diameter² < 0.9425 < 1. Row j = ⌊20y/11⌋ is shifted horizontally by
(48/25)·j (2.4 brick widths), and the colour is the column index i = ⌊(5/4)(x − (48/25)j)⌋ mod 7.
Take two points with difference (X, Y), X² + Y² = 1, row difference b and column difference 7m. Then |Y| ≤ 1 forces
|b| ≤ 2, and |X| ≤ 1 forces |m| ≤ 1. Each of the 15 cases (m, b) gives a contradiction:
- (0, 0) is the same brick, so the points are less than 1 apart.
- |b| = 1 puts the horizontal gap above 1.
- (∓1, ±2) gives |X| > 0.96 and |Y| > 0.55, so X² + Y² > 1.
- All other cases are linear contradictions.
`interval_cases` plus `nlinarith` settles the cases. The colouring into `ZMod 7` gives `Colorable 7`, hence χ ≤ 7.

Axioms: `'Erdos508.HadwigerNelsonAtMostSeven' depends on axioms: [propext, Classical.choice, Quot.sound]`

Date: 2026-10-29
