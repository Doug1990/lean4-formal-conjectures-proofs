import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.Real.Irrational

namespace CongruentNumber

def congruentNumber (n : ℕ) : Prop :=
  ∃ (a b c : ℚ), a ^ 2 + b ^ 2 = c ^ 2 ∧ n = (2⁻¹ : ℚ) * a * b

/-- A positive factor of a square, coprime to its cofactor, is a square. -/
lemma sq_split {a b c : ℤ} (h : Int.gcd a b = 1) (heq : a * b = c ^ 2) (ha : 0 < a) :
    ∃ s, a = s ^ 2 := by
  obtain ⟨s, hs | hs⟩ := Int.sq_of_gcd_eq_one h heq
  · exact ⟨s, hs⟩
  · exfalso
    nlinarith [sq_nonneg s]

lemma odd_sq_mod {v : ℤ} (hv : v % 2 = 1) : v ^ 2 % 2 = 1 := by
  rw [sq, Int.mul_emod, hv]; decide

lemma odd_of_sq_odd {v n : ℤ} (hn : n = v ^ 2) (h : n % 2 = 1) : v % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one v with hv | hv
  · exfalso
    have : n % 2 = 0 := by rw [hn, sq, Int.mul_emod, hv]; decide
    omega
  · exact hv

/-- Descent from `x ^ 2 = v ^ 4 + 4 u ^ 4` to a smaller solution of `p⁴ - q⁴ = w²`. -/
lemma desc4 {x u v : ℤ} (hx : 0 < x) (hu : u ≠ 0) (hv : v ≠ 0) (hvo : v % 2 = 1)
    (hcop : Int.gcd (v ^ 2) (2 * u ^ 2) = 1) (h : x ^ 2 = v ^ 4 + 4 * u ^ 4) :
    ∃ p q w : ℤ, 0 < p ∧ p < x ∧ q ≠ 0 ∧ w ≠ 0 ∧ p ^ 4 - q ^ 4 = w ^ 2 := by
  have ht : PythagoreanTriple (v ^ 2) (2 * u ^ 2) x := by
    delta PythagoreanTriple
    linear_combination -h
  obtain ⟨a, b, h1, h2, h3, h4, _, h6⟩ := ht.coprime_classification' hcop (odd_sq_mod hvo) hx
  have hu2 : a * b = u ^ 2 := by linarith
  have hupos : 0 < u ^ 2 := by positivity
  have ha : 0 < a := by
    rcases lt_or_eq_of_le h6 with h' | h'
    · exact h'
    · subst h'; simp at hu2; omega
  have hb : 0 < b := by nlinarith
  obtain ⟨p, hp⟩ := sq_split h4 hu2 ha
  obtain ⟨q, hq⟩ := sq_split (by rw [Int.gcd_comm]; exact h4) (by rw [mul_comm]; exact hu2) hb
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp; omega
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq; omega
  refine ⟨|p|, q, v, abs_pos.mpr hp0, ?_, hq0, hv, ?_⟩
  · have hpa : |p| ^ 2 = a := by rw [sq_abs]; exact hp.symm
    have h1p : 1 ≤ |p| := Int.one_le_abs hp0
    nlinarith
  · have : |p| ^ 4 = p ^ 4 := by
      rw [show |p| ^ 4 = (|p| ^ 2) ^ 2 by ring, sq_abs]; ring
    rw [this]
    have : v ^ 2 = p ^ 4 - q ^ 4 := by rw [h1, hp, hq]; ring
    linarith

/-- One descent step for a coprime solution of `x⁴ - y⁴ = z²`. -/
lemma step {x y z : ℤ} (hx : 0 < x) (hy : y ≠ 0) (hz : 0 < z) (hxy : Int.gcd x y = 1)
    (h : x ^ 4 - y ^ 4 = z ^ 2) :
    ∃ p q w : ℤ, 0 < p ∧ p < x ∧ q ≠ 0 ∧ w ≠ 0 ∧ p ^ 4 - q ^ 4 = w ^ 2 := by
  have hc : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hxy
  have hcz : IsCoprime (y ^ 2) z := by
    have h1 : IsCoprime (y ^ 2) (x ^ 4) := hc.symm.pow
    have h2 : IsCoprime (y ^ 2) (z ^ 2) := by
      have := h1.add_mul_left_right (-y ^ 2)
      rw [show x ^ 4 + y ^ 2 * -y ^ 2 = z ^ 2 by linear_combination h] at this
      exact this
    exact (IsCoprime.pow_right_iff (by norm_num)).mp h2
  have hx2 : 0 < x ^ 2 := by positivity
  rcases Int.emod_two_eq_zero_or_one y with hye | hyo
  · -- y even, so x odd and z odd
    have hxo : x % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one x with hxe | hxo
      · exfalso
        have h1 : 2 ∣ (Int.gcd x y : ℤ) :=
          Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hxe) (Int.dvd_of_emod_eq_zero hye)
        rw [hxy] at h1
        revert h1; decide
      · exact hxo
    have hzo : z % 2 = 1 := by
      have hx' : Odd x := Int.odd_iff.mpr hxo
      have hy' : Even y := Int.even_iff.mpr hye
      have hz2 : Odd (z ^ 2) := by
        rw [← h]; exact (hx'.pow).sub_even (hy'.pow_of_ne_zero (by norm_num))
      rcases Int.emod_two_eq_zero_or_one z with h0 | h0
      · exfalso
        have : Even (z ^ 2) := (Int.even_iff.mpr h0).pow_of_ne_zero (by norm_num)
        exact (Int.not_even_iff_odd.mpr hz2) this
      · exact h0
    have ht : PythagoreanTriple z (y ^ 2) (x ^ 2) := by
      delta PythagoreanTriple
      linear_combination -h
    obtain ⟨m, n, h1, h2, h3, h4, h5, h6⟩ :=
      ht.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hcz.symm) hzo hx2
    have hy2 : 0 < y ^ 2 := by positivity
    have hm : 0 < m := by
      rcases lt_or_eq_of_le h6 with h' | h'
      · exact h'
      · subst h'; simp at h2; omega
    have hn : 0 < n := by nlinarith
    obtain ⟨y', rfl⟩ : 2 ∣ y := Int.dvd_of_emod_eq_zero hye
    have hy'0 : y' ≠ 0 := by rintro rfl; simp at hy
    rcases h5 with ⟨hme, hno⟩ | ⟨hmo, hne⟩
    · obtain ⟨m', rfl⟩ : 2 ∣ m := Int.dvd_of_emod_eq_zero hme
      have hk : m' * n = y' ^ 2 :=
        mul_left_cancel₀ (by norm_num : (4:ℤ) ≠ 0) (by linear_combination -h2)
      have hg : Int.gcd m' n = 1 := Int.isCoprime_iff_gcd_eq_one.mp
        ((Int.isCoprime_iff_gcd_eq_one.mpr h4).of_mul_left_right)
      have hm' : 0 < m' := by omega
      obtain ⟨u, hu⟩ := sq_split hg hk hm'
      obtain ⟨v, hv⟩ := sq_split (by rw [Int.gcd_comm]; exact hg) (by rw [mul_comm]; exact hk) hn
      have hu0 : u ≠ 0 := by rintro rfl; simp at hu; omega
      have hv0 : v ≠ 0 := by rintro rfl; simp at hv; omega
      exact desc4 hx hu0 hv0 (odd_of_sq_odd hv hno)
        (by rw [← hv, ← hu, Int.gcd_comm]; exact h4) (by rw [h3, hu, hv]; ring)
    · obtain ⟨n', rfl⟩ : 2 ∣ n := Int.dvd_of_emod_eq_zero hne
      have hk : m * n' = y' ^ 2 :=
        mul_left_cancel₀ (by norm_num : (4:ℤ) ≠ 0) (by linear_combination -h2)
      have hg : Int.gcd m n' = 1 := Int.isCoprime_iff_gcd_eq_one.mp
        ((Int.isCoprime_iff_gcd_eq_one.mpr h4).of_mul_right_right)
      have hn' : 0 < n' := by omega
      obtain ⟨u, hu⟩ := sq_split hg hk hm
      obtain ⟨v, hv⟩ := sq_split (by rw [Int.gcd_comm]; exact hg) (by rw [mul_comm]; exact hk) hn'
      have hu0 : u ≠ 0 := by rintro rfl; simp at hu; omega
      have hv0 : v ≠ 0 := by rintro rfl; simp at hv; omega
      exact desc4 hx hv0 hu0 (odd_of_sq_odd hu hmo)
        (by rw [← hv, ← hu]; exact h4) (by rw [h3, hu, hv]; ring)
  · -- y odd
    have ht : PythagoreanTriple (y ^ 2) z (x ^ 2) := by
      delta PythagoreanTriple
      linear_combination -h
    obtain ⟨m, n, h1, h2, h3, _, _, h6⟩ :=
      ht.coprime_classification' (Int.isCoprime_iff_gcd_eq_one.mp hcz) (odd_sq_mod hyo) hx2
    have hm : 0 < m := by
      rcases lt_or_eq_of_le h6 with h' | h'
      · exact h'
      · subst h'; simp at h2; omega
    have hn : n ≠ 0 := by rintro rfl; simp at h2; omega
    refine ⟨m, n, x * y, hm, ?_, hn, mul_ne_zero hx.ne' hy, ?_⟩
    · have : 0 < n ^ 2 := by positivity
      nlinarith
    · linear_combination (-y ^ 2) * h3 + (-(m ^ 2 + n ^ 2)) * h1

/-- Fermat: `x⁴ - y⁴ = z²` has no solution with `x > 0`, `y ≠ 0`, `z ≠ 0`. -/
theorem no_sol (N : ℕ) : ∀ x y z : ℤ, x.toNat = N → 0 < x → y ≠ 0 → z ≠ 0 →
    x ^ 4 - y ^ 4 = z ^ 2 → False := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro x y z hN hx hy hz h
  by_cases hxy : Int.gcd x y = 1
  · have hz' : 0 < |z| := abs_pos.mpr hz
    obtain ⟨p, q, w, hp, hpx, hq, hw, hpqw⟩ := step hx hy hz' hxy (by rw [sq_abs]; exact h)
    exact ih p.toNat (by omega) p q w rfl hp hq hw hpqw
  · obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hxy
    obtain ⟨x1, rfl⟩ := Int.natCast_dvd.mpr hpa
    obtain ⟨y1, rfl⟩ := Int.natCast_dvd.mpr hpb
    have hpc : (p : ℤ) ^ 2 ∣ z := by
      rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h]
      exact Dvd.intro (x1 ^ 4 - y1 ^ 4) (by ring)
    obtain ⟨z1, rfl⟩ := hpc
    have hp1 : (1:ℤ) < p := by exact_mod_cast hp.one_lt
    have hx1 : 0 < x1 := by nlinarith
    have hlt : x1 < (p : ℤ) * x1 := by nlinarith
    have hp0 : (p : ℤ) ≠ 0 := by omega
    exact ih x1.toNat (by omega) x1 y1 z1 rfl hx1 (right_ne_zero_of_mul hy)
      (right_ne_zero_of_mul hz)
      (mul_left_cancel₀ (pow_ne_zero 4 hp0) (by linear_combination h))

lemma no_sol' {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (h : x ^ 4 - y ^ 4 = z ^ 2) :
    False :=
  no_sol _ |x| y z rfl (abs_pos.mpr hx) hy hz
    (by rw [show |x| ^ 4 = (|x| ^ 2) ^ 2 by ring, sq_abs]; linear_combination h)

lemma rat_sq_int {t : ℚ} {n : ℤ} (h : t ^ 2 = n) : ∃ T : ℤ, (T : ℚ) = t := by
  have hd := congrArg Rat.den h
  rw [Rat.den_pow, Rat.den_intCast] at hd
  have h1 := t.den_pos
  have : t.den = 1 := by nlinarith
  exact ⟨t.num, (Rat.den_eq_one_iff t).mp this⟩

/-- 1 is not a congruent number, as proved by Fermat via infinite descent. -/
theorem not_congruentNumber_1 : ¬ congruentNumber 1 := by
  rintro ⟨a, b, c, h1, h2⟩
  have hab : a * b = 2 := by
    simp only [Nat.cast_one] at h2
    linear_combination -2 * h2
  have hd : c ^ 4 - 16 = (a ^ 2 - b ^ 2) ^ 2 := by
    linear_combination 4 * (a * b + 2) * hab - (c ^ 2 + a ^ 2 + b ^ 2) * h1
  have hs : a ^ 2 - b ^ 2 ≠ 0 := by
    intro h0
    have h4 : (a ^ 2 - 2) * (a ^ 2 + 2) = 0 := by
      linear_combination a ^ 2 * h0 + (a * b + 2) * hab
    have ha2 : a ^ 2 = 2 := by
      rcases mul_eq_zero.mp h4 with h | h
      · linarith
      · nlinarith [sq_nonneg a]
    have hr : ((a : ℝ)) ^ 2 = 2 := by exact_mod_cast ha2
    exact irrational_sqrt_two ⟨|a|, by rw [Rat.cast_abs, ← hr, Real.sqrt_sq_eq_abs]⟩
  have ht : ((a ^ 2 - b ^ 2) * (c.den : ℚ) ^ 2) ^ 2
      = ((c.num ^ 4 - (2 * (c.den : ℤ)) ^ 4 : ℤ) : ℚ) := by
    push_cast
    rw [← Rat.mul_den_eq_num]
    linear_combination (-(c.den : ℚ) ^ 4) * hd
  obtain ⟨T, hT⟩ := rat_sq_int ht
  have hD : (c.den : ℚ) ≠ 0 := by positivity
  have hc0 : c.num ≠ 0 := by
    intro h0
    rw [Rat.num_eq_zero] at h0
    subst h0
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  have hT0 : T ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero] at hT
    exact mul_ne_zero hs (pow_ne_zero 2 hD) hT.symm
  have key : ((T : ℚ)) ^ 2 = ((c.num ^ 4 - (2 * (c.den : ℤ)) ^ 4 : ℤ) : ℚ) := by
    rw [hT]; exact ht
  have hint : c.num ^ 4 - (2 * (c.den : ℤ)) ^ 4 = T ^ 2 := by exact_mod_cast key.symm
  exact no_sol' (y := 2 * (c.den : ℤ)) hc0 (by have := c.den_pos; omega) hT0 hint

end CongruentNumber

#print axioms CongruentNumber.not_congruentNumber_1
