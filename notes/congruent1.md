# CongruentNumber.not_congruentNumber_1

- Source: `FormalConjectures/Wikipedia/CongruentNumber.lean:41` (category textbook)
- Statement: `¬ congruentNumber 1` (no rational right triangle has area 1)
- Date: 2026-10-29

Proof idea: Fermat's descent for x⁴ − y⁴ = z². `no_sol` uses strong induction on x > 0. If
gcd(x,y) > 1, divide by a common prime p (then p² | z). If gcd(x,y) = 1, `step` uses Mathlib's
primitive Pythagorean-triple classification (`coprime_classification'`) on (y²)² + z² = (x²)².
For odd y, (m, n, xy) is a smaller solution because m⁴ − n⁴ = (m²+n²)(m²−n²). For even y,
y² = 2mn splits into squares, which gives x² = v⁴ + 4u⁴. A second classification in `desc4`
then gives a smaller solution p⁴ − q⁴ = v². For the triangle: from a² + b² = c² and ab = 2 we
get c⁴ − 16 = (a² − b²)². Here a² ≠ b², since otherwise a² = 2, which contradicts
`irrational_sqrt_two`. Clearing the denominator of c gives num⁴ − (2·den)⁴ = T² for an integer T
(a rational whose square is an integer is an integer, via `Rat.den_pow`). This contradicts
`no_sol`.

Axioms: `[propext, Classical.choice, Quot.sound]`
