# RamseyNumbers.ramsey_number_three_three : R(3, 3) = 6

Source: FormalConjectures/Wikipedia/RamseyNumbers.lean (~line 129).
Proof: results/ramsey33.lean. Compiled with check.ps1; axioms: propext, Classical.choice, Quot.sound; no sorry.

Caveat for review: the file imports only Mathlib (FormalConjecturesUtil is not built) and restates
`graphRamsey` / `classicalRamsey` locally in namespace R33, following the definitions in
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean. Check that the restated
definitions match before porting the proof into the checkout.

Method: upper bound by a kernel `decide` over 15 edge Booleans (some triple is monochromatic);
lower bound by the 5-cycle (no triangle in it or its complement).
