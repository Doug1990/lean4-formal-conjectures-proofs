import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

open Filter Asymptotics Real Finset

namespace DirichletDivisorProblem

/-- Restated from FormalConjectures/Wikipedia/DirichletDivisorProblem.lean -/
noncomputable def divisorSummatory (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)

/-- Restated from FormalConjectures/Wikipedia/DirichletDivisorProblem.lean -/
noncomputable def divisorError (x : ℝ) : ℝ :=
  divisorSummatory x - x * Real.log x - (2 * eulerMascheroniConstant - 1) * x

lemma card_divisors_eq (N n : ℕ) (hn : n ∈ Ioc 0 N) :
    n.divisors.card = #{a ∈ Ioc 0 N | a ∣ n} := by
  congr 1
  ext a
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
  constructor
  · rintro ⟨h, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos h hn.1, (Nat.le_of_dvd hn.1 h).trans hn.2⟩, h⟩
  · rintro ⟨_, h⟩
    exact ⟨h, by omega⟩

lemma sum_divisors_card (N : ℕ) :
    ∑ n ∈ Ioc 0 N, n.divisors.card = ∑ a ∈ Ioc 0 N, N / a := by
  rw [Finset.sum_congr rfl (fun n hn => card_divisors_eq N n hn)]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.card_filter, Nat.Ioc_filter_dvd_card_eq_div]

lemma card_mul_le (N a : ℕ) (ha : 0 < a) : #{b ∈ Ioc 0 N | a * b ≤ N} = N / a := by
  have : ({b ∈ Ioc 0 N | a * b ≤ N} : Finset ℕ) = Ioc 0 (N / a) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    rw [Nat.le_div_iff_mul_le ha]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, by rw [mul_comm]; exact h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, by rw [mul_comm]; exact h3⟩
      nlinarith
  rw [this, Nat.card_Ioc]
  simp

lemma sum_ite_out (s : Finset ℕ) (p : Prop) [Decidable p] (g : ℕ → ℤ) :
    ∑ b ∈ s, (if p then g b else 0) = if p then ∑ b ∈ s, g b else 0 := by
  split_ifs <;> simp

lemma sum_le_m (N m : ℕ) (hmN : m ≤ N) (f : ℕ → ℤ) :
    ∑ a ∈ Ioc 0 N, (if a ≤ m then f a else 0) = ∑ a ∈ Ioc 0 m, f a := by
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  omega

/-- Dirichlet's hyperbola identity. -/
lemma hyperbola (N m : ℕ) (h1 : m * m ≤ N) (h2 : N < (m + 1) * (m + 1)) :
    (∑ a ∈ Ioc 0 N, ((N / a : ℕ) : ℤ)) =
      2 * ∑ a ∈ Ioc 0 m, ((N / a : ℕ) : ℤ) - (m : ℤ) * m := by
  have hmN : m ≤ N := le_trans (Nat.le_mul_self m) h1
  have hA : ∀ a b : ℕ, a * b ≤ N → a ≤ m ∨ b ≤ m := by
    intro a b h
    by_contra h'
    push Not at h'
    have := Nat.mul_le_mul (Nat.succ_le_of_lt h'.1) (Nat.succ_le_of_lt h'.2)
    exact absurd (lt_of_le_of_lt (this.trans h) h2) (lt_irrefl _)
  have hB : ∀ a b : ℕ, a ≤ m → b ≤ m → a * b ≤ N :=
    fun a b ha hb => (Nat.mul_le_mul ha hb).trans h1
  have hrow : ∀ a ∈ Ioc 0 N, ((N / a : ℕ) : ℤ) =
      ∑ b ∈ Ioc 0 N, if a * b ≤ N then (1 : ℤ) else 0 := by
    intro a ha
    rw [Finset.sum_boole, card_mul_le N a (Finset.mem_Ioc.1 ha).1]
  have hcol : ∀ b ∈ Ioc 0 N, ((N / b : ℕ) : ℤ) =
      ∑ a ∈ Ioc 0 N, if a * b ≤ N then (1 : ℤ) else 0 := by
    intro b hb
    rw [hrow b hb]
    exact Finset.sum_congr rfl (fun a _ => by rw [mul_comm])
  have hpt : ∀ a b : ℕ, (if a * b ≤ N then (1 : ℤ) else 0) =
      (if a ≤ m then (if a * b ≤ N then (1 : ℤ) else 0) else 0)
      + (if b ≤ m then (if a * b ≤ N then (1 : ℤ) else 0) else 0)
      - (if a ≤ m then (if b ≤ m then (1 : ℤ) else 0) else 0) := by
    intro a b
    have h3 := hA a b
    have h4 := hB a b
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have hX : ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N,
      (if a ≤ m then (if a * b ≤ N then (1 : ℤ) else 0) else 0) =
      ∑ a ∈ Ioc 0 m, ((N / a : ℕ) : ℤ) := by
    simp only [sum_ite_out]
    rw [← sum_le_m N m hmN]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [← hrow a ha]
  have hY : ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N,
      (if b ≤ m then (if a * b ≤ N then (1 : ℤ) else 0) else 0) =
      ∑ a ∈ Ioc 0 m, ((N / a : ℕ) : ℤ) := by
    rw [Finset.sum_comm]
    simp only [sum_ite_out]
    rw [← sum_le_m N m hmN]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [← hcol b hb]
  have hZ : ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N,
      (if a ≤ m then (if b ≤ m then (1 : ℤ) else 0) else 0) = (m : ℤ) * m := by
    simp only [sum_ite_out]
    rw [sum_le_m N m hmN, sum_le_m N m hmN]
    simp
  calc (∑ a ∈ Ioc 0 N, ((N / a : ℕ) : ℤ))
      = ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N, if a * b ≤ N then (1 : ℤ) else 0 :=
        Finset.sum_congr rfl hrow
    _ = ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N,
        ((if a ≤ m then (if a * b ≤ N then (1 : ℤ) else 0) else 0)
        + (if b ≤ m then (if a * b ≤ N then (1 : ℤ) else 0) else 0)
        - (if a ≤ m then (if b ≤ m then (1 : ℤ) else 0) else 0)) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hpt a b))
    _ = 2 * ∑ a ∈ Ioc 0 m, ((N / a : ℕ) : ℤ) - (m : ℤ) * m := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [hX, hY, hZ]
        ring

lemma Icc_one_eq (k : ℕ) : Finset.Icc 1 k = Finset.Ioc 0 k := by
  ext a
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

lemma divisorSummatory_eq (x : ℝ) :
    divisorSummatory x = 2 * ∑ a ∈ Ioc 0 (Nat.sqrt ⌊x⌋₊), ((⌊x⌋₊ / a : ℕ) : ℝ)
      - (Nat.sqrt ⌊x⌋₊ : ℝ) * (Nat.sqrt ⌊x⌋₊ : ℝ) := by
  have hZ := hyperbola ⌊x⌋₊ (Nat.sqrt ⌊x⌋₊) (Nat.sqrt_le _)
    (by have := Nat.lt_succ_sqrt ⌊x⌋₊; simpa [Nat.succ_eq_add_one] using this)
  have h : divisorSummatory x = ((∑ a ∈ Ioc 0 ⌊x⌋₊, ((⌊x⌋₊ / a : ℕ) : ℤ) : ℤ) : ℝ) := by
    rw [divisorSummatory, Icc_one_eq]
    exact_mod_cast sum_divisors_card ⌊x⌋₊
  rw [h, hZ]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast, Int.cast_ofNat]

lemma floor_bound (N a : ℕ) (x : ℝ) (ha : 0 < a) (hN : (N : ℝ) ≤ x) (hx : x < N + 1) :
    |((N / a : ℕ) : ℝ) - x / a| ≤ 2 := by
  have h1 : N = a * (N / a) + N % a := (Nat.div_add_mod N a).symm
  have h2 : N % a < a := Nat.mod_lt _ ha
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have h1' : (N : ℝ) = a * ((N / a : ℕ) : ℝ) + ((N % a : ℕ) : ℝ) := by exact_mod_cast h1
  have h2' : ((N % a : ℕ) : ℝ) + 1 ≤ a := by exact_mod_cast h2
  have h3 : (0 : ℝ) ≤ ((N % a : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : |(a : ℝ) * ((N / a : ℕ) : ℝ) - x| ≤ 2 * a := by
    rw [abs_le]
    constructor <;> linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have e : ((N / a : ℕ) : ℝ) - x / a = ((a : ℝ) * ((N / a : ℕ) : ℝ) - x) / a := by
    field_simp
  rw [e, abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
  exact key

lemma sum_floor_bound (N m : ℕ) (x : ℝ) (hN : (N : ℝ) ≤ x) (hx : x < N + 1) :
    |∑ a ∈ Ioc 0 m, ((N / a : ℕ) : ℝ) - x * (harmonic m : ℝ)| ≤ 2 * m := by
  have hH : ∀ k : ℕ, (harmonic k : ℝ) = ∑ a ∈ Ioc 0 k, (1 / (a : ℝ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [harmonic_succ, Finset.sum_Ioc_succ_top (Nat.zero_le k), ← ih]
      push_cast
      ring
  rw [hH m, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ a ∈ Ioc 0 m, (((N / a : ℕ) : ℝ) - x * (1 / (a : ℝ)))|
      ≤ ∑ a ∈ Ioc 0 m, |((N / a : ℕ) : ℝ) - x * (1 / (a : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Ioc 0 m, (2 : ℝ) := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        rw [mul_one_div]
        exact floor_bound N a x (Finset.mem_Ioc.1 ha).1 hN hx
    _ = 2 * m := by simp [mul_comm]

lemma harmonic_log_bound (m : ℕ) (hm : 1 ≤ m) (s : ℝ) (hms : (m : ℝ) ≤ s) (hsm : s < m + 1) :
    |(harmonic m : ℝ) - Real.log s - eulerMascheroniConstant| ≤ 1 / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : m ≠ 0 := by omega
  have h1 := eulerMascheroniConstant_lt_eulerMascheroniSeq' m
  have h2 := eulerMascheroniSeq_lt_eulerMascheroniConstant m
  rw [eulerMascheroniSeq', if_neg hmne] at h1
  rw [eulerMascheroniSeq] at h2
  have l1 : Real.log m ≤ Real.log s := Real.log_le_log hm0 hms
  have l2 : Real.log s ≤ Real.log (m + 1) := Real.log_le_log (by linarith) hsm.le
  have l3 : Real.log (m + 1) - Real.log m ≤ 1 / m := by
    rw [← Real.log_div (by positivity) hm0.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m + 1) / m by positivity)
    have e : ((m : ℝ) + 1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  rw [abs_le]
  constructor <;> linarith

theorem divisor_error_dirichlet :
    divisorError =O[atTop] fun x => Real.sqrt x := by
  refine Asymptotics.IsBigO.of_bound 10 (Filter.eventually_atTop.2 ⟨1, fun x hx => ?_⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)]
  set N := ⌊x⌋₊ with hNdef
  set m := Nat.sqrt N with hmdef
  set s := Real.sqrt x with hsdef
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < N + 1 := Nat.lt_floor_add_one x
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hx)
  have hm1 : 1 ≤ m := by
    rw [hmdef, Nat.le_sqrt]
    simpa using hN1
  have hmm : m * m ≤ N := Nat.sqrt_le N
  have hmm' : N < (m + 1) * (m + 1) := by
    have := Nat.lt_succ_sqrt N; simpa [Nat.succ_eq_add_one] using this
  have hmmR : (m : ℝ) * m ≤ N := by exact_mod_cast hmm
  have hmmR' : (N : ℝ) + 1 ≤ (m + 1) * (m + 1) := by exact_mod_cast hmm'
  have hss : s * s = x := Real.mul_self_sqrt hx0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hms : (m : ℝ) ≤ s := by nlinarith
  have hsm : s < m + 1 := by nlinarith
  have hlog : Real.log x = 2 * Real.log s := by
    rw [← hss, Real.log_mul (by nlinarith) (by nlinarith)]
    ring
  have hS := sum_floor_bound N m x hNx hxN
  have hE := harmonic_log_bound m hm1 s hms hsm
  have hD := divisorSummatory_eq x
  set S := ∑ a ∈ Ioc 0 m, ((N / a : ℕ) : ℝ) with hSdef
  set H := (harmonic m : ℝ) with hHdef
  set γ := eulerMascheroniConstant with hγ
  have hid : divisorError x = 2 * (S - x * H) + 2 * (x * (H - Real.log s - γ))
      + (x - (m : ℝ) * m) := by
    rw [divisorError, hD, hlog]
    ring
  have hB : |x * (H - Real.log s - γ)| ≤ 2 * s := by
    rw [abs_mul, abs_of_nonneg hx0]
    have h1 : x * |H - Real.log s - γ| ≤ x * (1 / m) := mul_le_mul_of_nonneg_left hE hx0
    have h2 : x * (1 / (m : ℝ)) ≤ 2 * s := by
      rw [mul_one_div, div_le_iff₀ hm0]
      have h3 : s * s ≤ s * (2 * m) := mul_le_mul_of_nonneg_left (by linarith) hs0
      linarith
    linarith
  have hC1 : 0 ≤ x - (m : ℝ) * m := by linarith
  have hC2 : x - (m : ℝ) * m ≤ 2 * s := by nlinarith
  rw [hid]
  have t := abs_add_three (2 * (S - x * H)) (2 * (x * (H - Real.log s - γ))) (x - (m : ℝ) * m)
  rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hC1] at t
  have hms' : (m : ℝ) ≤ s := hms
  linarith

end DirichletDivisorProblem

#print axioms DirichletDivisorProblem.divisor_error_dirichlet
