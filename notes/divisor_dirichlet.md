# DirichletDivisorProblem.divisor_error_dirichlet

- Source: FormalConjectures/Wikipedia/DirichletDivisorProblem.lean:70 (category textbook)
- Date: 2026-10-29

Proof idea: Dirichlet's hyperbola method. With N = ⌊x⌋ and m = Nat.sqrt N, first
Σ_{n≤N} d(n) = Σ_{a≤N} ⌊N/a⌋ (swap the double sum, `Nat.Ioc_filter_dvd_card_eq_div`), then the
hyperbola identity Σ_{a≤N} ⌊N/a⌋ = 2 Σ_{a≤m} ⌊N/a⌋ − m², proved in ℤ by writing [ab≤N] =
[a≤m][ab≤N] + [b≤m][ab≤N] − [a≤m][b≤m] pointwise (uses m² ≤ N < (m+1)²). Analytic part, with
s = √x (so m ≤ s < m+1): each |⌊N/a⌋ − x/a| ≤ 2, giving |S − x·H_m| ≤ 2m; Mathlib's
Euler–Mascheroni monotone sequences give H_m − log(m+1) < γ < H_m − log m, hence
|H_m − log s − γ| ≤ log(1+1/m) ≤ 1/m and |x(H_m − log s − γ)| ≤ x/m ≤ 2s; and 0 ≤ x − m² ≤ 2s.
Since log x = 2 log s, Δ(x) = 2(S − xH_m) + 2x(H_m − log s − γ) + (x − m²), so |Δ(x)| ≤ 10√x for x ≥ 1.
Definitions `divisorSummatory` and `divisorError` restated locally (identical text); targeted imports.
Reusable helpers: `sum_divisors_card`, `card_mul_le`, `hyperbola`, `floor_bound`, `sum_floor_bound`,
`harmonic_log_bound`.

Axioms: `[propext, Classical.choice, Quot.sound]`
