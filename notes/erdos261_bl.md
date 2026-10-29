# Erdős 261: Borwein–Loring construction (3 statements)

- Statements: `Erdos261.erdos_261.variants.borwein_loring` (textbook, line 58),
  `Erdos261.erdos_261.variants.borwein_loring_property` (textbook, line 66),
  `Erdos261.erdos_261.parts.i` (research solved, line 76)
- Source: `FormalConjectures/ErdosProblems/261.lean`
- Result file: `results/erdos261_bl.lean` (targeted Mathlib imports; `Erdos261Prop` restated verbatim)

Proof idea: the tail sums telescope, ∑_{a<k≤a+j} k/2^k = (a+2)/2^a − (a+j+2)/2^(a+j)
(proved by induction on j). With n = 2^(m+1) − m − 2 we have n + m + 2 = 2^(m+1). So the
right-hand side equals (n+2)/2^n − 2·2^m/2^(n+m) = n/2^n. This holds for every m, so the
hypothesis `0 < m` is not used. For the property, take t = m and a_i = n+1+i. A reindexing
lemma (sum over Ioc a (a+j) equals sum over Fin j) turns the identity into the required
form. For parts.i, m ↦ 2^(m+3) − (m+2) − 2 is strictly increasing and positive, and every
value has the property (m+2 ≥ 2). So the set is infinite. This is Cusick's simple
observation, consistent with the "research solved" tag.

Axioms (all three): `[propext, Classical.choice, Quot.sound]`

Date: 2026-10-29
