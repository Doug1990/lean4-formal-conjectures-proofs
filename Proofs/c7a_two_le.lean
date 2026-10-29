import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.ENNReal.Basic

namespace Constant7a

open Real ENNReal Set NNReal

/-- The irrationality exponent of a real number. -/
noncomputable def irrationalityExponent (x : ℝ) : ℝ≥0∞ :=
  sSup ((↑) '' {p : ℝ≥0 | LiouvilleWith p x})

/-- Copied with its proof from the source (category API). -/
theorem le_irrationalityExponent_iff (x : ℝ) (y : ℝ≥0∞) :
    y ≤ irrationalityExponent x ↔ ∀ z : ℝ≥0, z < y → LiouvilleWith z x := by
  rw [irrationalityExponent, le_sSup_iff_forall_lt]
  refine ⟨fun h z zy ↦ ?_, fun h z zy ↦ ?_⟩
  · obtain ⟨a, ha, za⟩ := h z zy
    simp only [mem_image, mem_ofPred_eq] at ha
    obtain ⟨r, hr, ra⟩ := ha
    apply LiouvilleWith.mono hr
    simp only [NNReal.coe_le_coe]
    suffices (z : ℝ≥0∞) ≤ r by simpa
    grind
  · simp only [mem_image, mem_ofPred_eq, exists_exists_and_eq_and]
    rcases eq_or_ne y ⊤ with rfl | hy
    · simp_all only [coe_lt_top, forall_const, true_and]
      refine ⟨z.toNNReal + 1, ?_⟩
      rw [coe_add, ENNReal.coe_one, coe_toNNReal zy.ne]
      exact lt_add_right zy.ne one_ne_zero
    obtain ⟨a, za, ay⟩ := DenselyOrdered.dense z y zy
    refine ⟨a.toNNReal, ?_, ?_⟩
    · apply h
      rwa [ENNReal.coe_toNNReal (by grind)]
    · rwa [ENNReal.coe_toNNReal (by grind)]

/-- Dirichlet: an irrational number has infinitely many approximations `|x - j/k| < 1/k^2`. -/
lemma liouvilleWith_two {x : ℝ} (hx : Irrational x) : LiouvilleWith 2 x := by
  refine ⟨1, Filter.frequently_atTop.2 fun a => ?_⟩
  have hne : (Finset.Icc 1 (a + 1)).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  have hpos : ∀ k : ℕ, 0 < k → 0 < |(k : ℝ) * x - round ((k : ℝ) * x)| := by
    intro k hk
    rw [abs_pos, sub_ne_zero]
    intro h
    apply hx
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    refine ⟨(round ((k : ℝ) * x) : ℚ) / k, ?_⟩
    push_cast
    rw [← h, mul_div_cancel_left₀ _ hk']
  set δ := (Finset.Icc 1 (a + 1)).inf' hne
    (fun k : ℕ => |(k : ℝ) * x - round ((k : ℝ) * x)|) with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    intro k hk
    exact hpos k (Finset.mem_Icc.1 hk).1
  obtain ⟨n0, hn0⟩ := exists_nat_gt (1 / δ)
  obtain ⟨n, hn0n, han⟩ : ∃ n : ℕ, n0 ≤ n ∧ a + 1 ≤ n :=
    ⟨max n0 (a + 1), le_max_left _ _, le_max_right _ _⟩
  have hnpos : 0 < n := by omega
  obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le x hnpos
  lift k to ℕ using hk0.le
  push_cast at hjk
  have hkpos : 0 < k := by exact_mod_cast hk0
  have hkn' : k ≤ n := by exact_mod_cast hkn
  have hn0' : (n0 : ℝ) ≤ n := by exact_mod_cast hn0n
  have hsmall : |(k : ℝ) * x - j| < δ := by
    have h1 : 1 / ((n : ℝ) + 1) < δ := by
      have h2 : 1 / δ < (n : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hδpos] at h2
      rw [div_lt_iff₀ (by positivity)]
      linarith
    linarith
  have hkN : a ≤ k := by
    by_contra hlt
    push Not at hlt
    have hmem : k ∈ Finset.Icc 1 (a + 1) := Finset.mem_Icc.2 ⟨hkpos, by omega⟩
    have h1 : δ ≤ |(k : ℝ) * x - round ((k : ℝ) * x)| := Finset.inf'_le _ hmem
    have h2 := round_le ((k : ℝ) * x) j
    linarith
  refine ⟨k, hkN, j, ?_, ?_⟩
  · intro h
    apply hx
    exact ⟨(j : ℚ) / k, by push_cast; exact h.symm⟩
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hkpos
    rw [Real.rpow_two]
    have e : x - j / k = ((k : ℝ) * x - j) / k := by field_simp
    rw [e, abs_div, abs_of_pos hk', div_lt_div_iff₀ hk' (by positivity)]
    have hkn'' : (k : ℝ) ≤ n := by exact_mod_cast hkn'
    have hlt : |(k : ℝ) * x - j| * k < 1 := by
      calc |(k : ℝ) * x - j| * k ≤ 1 / ((n : ℝ) + 1) * k := by gcongr
        _ < 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
          linarith
    rw [sq, ← mul_assoc, one_mul]
    nlinarith

theorem two_le_irrationalityExponent {x : ℝ} (hx : Irrational x) :
    2 ≤ irrationalityExponent x := by
  rw [le_irrationalityExponent_iff]
  intro z hz
  have hz' : (z : ℝ) ≤ 2 := by
    have : z < 2 := by exact_mod_cast hz
    exact_mod_cast this.le
  exact (liouvilleWith_two hx).mono hz'

end Constant7a

#print axioms Constant7a.two_le_irrationalityExponent
