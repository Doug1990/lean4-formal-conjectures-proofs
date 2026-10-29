import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.BigOperators.Intervals

open Complex Filter Topology Nat

namespace OeisA105751

noncomputable def a (n : ℕ) : ℤ :=
  let productTerm (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod productTerm).im)

/-- Gaussian-type ring `R[i]`, `i^2 = -1`. -/
abbrev GI (R : Type) [CommRing R] := QuadraticAlgebra R (-1) 0

/-- The factor `1 + k i`. -/
def gt (R : Type) [CommRing R] (k : ℕ) : GI R := ⟨1, (k : R)⟩

/-- `∏_{k < N} (1 + k i)` in `ℤ[i]`. -/
def P (N : ℕ) : GI ℤ := ∏ k ∈ Finset.range N, gt ℤ k

lemma prod_complex (N : ℕ) :
    (∏ k ∈ Finset.range N, (1 + (k : ℂ) * I)) = ((P N).re : ℂ) + ((P N).im : ℂ) * I := by
  induction N with
  | zero => simp [P, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  | succ N ih =>
    rw [Finset.prod_range_succ, ih]
    have : P (N + 1) = P N * gt ℤ N := Finset.prod_range_succ _ _
    rw [this]
    apply Complex.ext <;> simp [gt] <;> ring

lemma a_eq (n : ℕ) : a n = (P (n + 1)).im := by
  have h := prod_complex (n + 1)
  show ⌊(∏ k ∈ Finset.range (n + 1), (1 + (k : ℂ) * I)).im⌋ = _
  rw [h]
  simp

/-- Reduction `ℤ[i] → R[i]`. -/
def red (R : Type) [CommRing R] : GI ℤ →+* GI R where
  toFun z := ⟨(z.re : R), (z.im : R)⟩
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by ext <;> simp <;> ring
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

lemma red_im (R : Type) [CommRing R] (z : GI ℤ) : (red R z).im = (z.im : R) := rfl

lemma red_gt (R : Type) [CommRing R] (k : ℕ) : red R (gt ℤ k) = gt R k := by
  ext <;> simp [red, gt]

lemma red_P (R : Type) [CommRing R] (N : ℕ) :
    red R (P N) = ∏ k ∈ Finset.range N, gt R k := by
  simp [P, map_prod, red_gt]

lemma periodic_mul {M : Type*} (q : ℕ) (g : ℕ → M) (hg : ∀ k, g (k + q) = g k) (j x : ℕ) :
    g (j * q + x) = g x := by
  induction j with
  | zero => simp
  | succ j ihj =>
    rw [Nat.succ_mul, show j * q + q + x = (j * q + x) + q by ring, hg, ihj]

lemma prod_periodic {M : Type*} [CommMonoid M] (q : ℕ) (g : ℕ → M)
    (hg : ∀ k, g (k + q) = g k) (m : ℕ) :
    ∏ k ∈ Finset.range (m * q), g k = (∏ k ∈ Finset.range q, g k) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.prod_range_add, ih, pow_succ]
    congr 1
    exact Finset.prod_congr rfl (fun x _ => periodic_mul q g hg m x)

lemma gt_periodic (q : ℕ) (k : ℕ) : gt (ZMod q) (k + q) = gt (ZMod q) k := by
  simp [gt, ZMod.natCast_self]

lemma prod_range_eq_univ (p : ℕ) [NeZero p] {M : Type*} [CommMonoid M] (f : ZMod p → M) :
    ∏ k ∈ Finset.range p, f (k : ZMod p) = ∏ j : ZMod p, f j := by
  refine Finset.prod_nbij' (fun k : ℕ => (k : ZMod p)) (fun j => j.val) ?_ ?_ ?_ ?_ ?_
  · intro x _; simp
  · intro j _; simpa using ZMod.val_lt j
  · intro x hx
    simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range] at hx
    exact ZMod.val_cast_of_lt hx
  · intro j _; exact ZMod.natCast_zmod_val j
  · intro x _; rfl

lemma Q_im (p : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) :
    (∏ k ∈ Finset.range p, gt (ZMod p) k).im = 0 := by
  have e : ∏ k ∈ Finset.range p, gt (ZMod p) k = ∏ j : ZMod p, (⟨1, j⟩ : GI (ZMod p)) :=
    prod_range_eq_univ p (fun j => (⟨1, j⟩ : GI (ZMod p)))
  rw [e]
  set Q := ∏ j : ZMod p, (⟨1, j⟩ : GI (ZMod p)) with hQ
  have hs : star Q = Q := by
    rw [hQ, ← starRingEnd_apply, map_prod]
    refine Fintype.prod_equiv (Equiv.neg (ZMod p)) _ _ ?_
    intro j
    ext <;> simp [starRingEnd_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  have h1 : (star Q).im = -Q.im := QuadraticAlgebra.im_star Q
  rw [hs] at h1
  have h2m : (2 : ZMod p) * Q.im = 0 := by
    calc (2 : ZMod p) * Q.im = Q.im + Q.im := two_mul _
      _ = Q.im + -Q.im := by rw [← h1]
      _ = 0 := add_neg_cancel _
  have hc : (((p + 1) / 2 : ℕ) : ZMod p) * 2 = 1 := by
    have hodd := hp.out.eq_two_or_odd.resolve_left h2
    have h'' : (p + 1) / 2 * 2 = p + 1 := by omega
    have h' : (((p + 1) / 2 * 2 : ℕ) : ZMod p) = ((p + 1 : ℕ) : ZMod p) := by rw [h'']
    rw [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one,
      Nat.cast_ofNat] at h'
    exact h'
  calc Q.im = ((((p + 1) / 2 : ℕ) : ZMod p) * 2) * Q.im := by rw [hc, one_mul]
    _ = (((p + 1) / 2 : ℕ) : ZMod p) * (2 * Q.im) := mul_assoc _ _ _
    _ = 0 := by rw [h2m, mul_zero]

lemma dvd_part (p : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) (m : ℕ) :
    (p : ℤ) ∣ (P (m * p)).im := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← red_im, red_P,
    prod_periodic p (gt (ZMod p)) (gt_periodic p) m]
  have hQ := Q_im p h2
  set Q := ∏ k ∈ Finset.range p, gt (ZMod p) k
  have hQ' : Q = algebraMap (ZMod p) (GI (ZMod p)) Q.re := by
    ext
    · rfl
    · exact hQ
  rw [hQ', ← map_pow]
  rfl

lemma not_three (m : ℕ) : ((P (m * 3 + 2)).im : ZMod 3) ≠ 0 := by
  rw [← red_im, red_P, Finset.prod_range_add, prod_periodic 3 (gt (ZMod 3)) (gt_periodic 3) m]
  rw [Finset.prod_congr rfl (fun x _ => periodic_mul 3 (gt (ZMod 3)) (gt_periodic 3) m x)]
  have h3 : ∏ k ∈ Finset.range 3, gt (ZMod 3) k = algebraMap (ZMod 3) (GI (ZMod 3)) 2 := by
    ext <;> decide
  have h2 : ∏ k ∈ Finset.range 2, gt (ZMod 3) k = ⟨1, 1⟩ := by
    ext <;> decide
  rw [h3, h2, ← map_pow, QuadraticAlgebra.algebraMap_eq]
  simp only [QuadraticAlgebra.im_mul]
  have : (2 : ZMod 3) ^ m ≠ 0 := by
    intro h0
    have h4 : ((2 : ZMod 3) * 2) ^ m = 1 := by
      rw [show (2 : ZMod 3) * 2 = 1 by decide, one_pow]
    rw [mul_pow, h0, zero_mul] at h4
    exact absurd h4 (by decide)
  simpa using this

lemma a_two : a 2 = 3 := by
  rw [a_eq]; decide

lemma a_four : a 4 = -40 := by
  rw [a_eq]; decide

theorem prime_divides_some_term (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, a n ≠ 0 ∧ (p : ℤ) ∣ a n := by
  haveI := Fact.mk hp
  by_cases h2 : p = 2
  · subst h2; refine ⟨4, ?_, ?_⟩ <;> rw [a_four] <;> norm_num
  by_cases h3 : p = 3
  · subst h3; refine ⟨2, ?_, ?_⟩ <;> rw [a_two] <;> norm_num
  have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have : ¬ 3 ∣ p := fun h => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
    omega
  obtain ⟨m, j, hj⟩ : ∃ m j : ℕ, m * p = j * 3 + 2 := by
    rcases hp3 with h | h
    · exact ⟨2, 2 * (p / 3), by omega⟩
    · exact ⟨1, p / 3, by omega⟩
  refine ⟨j * 3 + 1, ?_, ?_⟩
  · intro h
    rw [a_eq, show j * 3 + 1 + 1 = j * 3 + 2 by ring] at h
    apply not_three j
    rw [h]
    simp
  · rw [a_eq, show j * 3 + 1 + 1 = j * 3 + 2 by ring, ← hj]
    exact dvd_part p h2 m

end OeisA105751

#print axioms OeisA105751.prime_divides_some_term
