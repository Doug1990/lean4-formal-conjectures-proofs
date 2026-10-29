import Mathlib.LinearAlgebra.Lagrange
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

open Polynomial Finset

namespace WolstenholmePrime

/-- The polynomial `(X + 1) (X + 2) ⋯ (X + (p - 1))` over `ℤ`. -/
noncomputable def wg (p : ℕ) : ℤ[X] := ∏ i ∈ range (p - 1), (X + C ((i : ℤ) + 1))

/-- `t ^ 3` divides `g t` minus the quadratic Taylor part of `g` at `0`. -/
lemma cube_dvd_eval_sub (g : ℤ[X]) (t : ℤ) :
    t ^ 3 ∣ g.eval t - (g.coeff 0 + g.coeff 1 * t + g.coeff 2 * t ^ 2) := by
  have h : (X : ℤ[X]) ^ 3 ∣
      g - (C (g.coeff 0) + C (g.coeff 1) * X + C (g.coeff 2) * X ^ 2) := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d <;>
      simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow] <;> norm_num
  obtain ⟨q, hq⟩ := h
  refine ⟨q.eval t, ?_⟩
  have := congrArg (eval t) hq
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_pow] at this
  exact this

/-- Over `ZMod p`, `(X + 1) ⋯ (X + (p - 1)) = X ^ (p - 1) - 1`. -/
lemma prod_eq_X_pow_sub_one (p : ℕ) [hp : Fact p.Prime] :
    (∏ i ∈ range (p - 1), (X + C ((i : ZMod p) + 1))) = X ^ (p - 1) - C 1 := by
  have hmon : (∏ i ∈ range (p - 1), (X + C ((i : ZMod p) + 1))).Monic :=
    monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _)
  have hnd : (∏ i ∈ range (p - 1), (X + C ((i : ZMod p) + 1))).natDegree = p - 1 := by
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]
    simp only [natDegree_X_add_C, sum_const, card_range, smul_eq_mul, mul_one]
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  have hdeg2 : (X ^ (p - 1) - C (1 : ZMod p)).degree = ((p - 1 : ℕ) : WithBot ℕ) :=
    degree_X_pow_sub_C hp1 _
  have hmon2 : (X ^ (p - 1) - C (1 : ZMod p)).Monic := monic_X_pow_sub_C _ hp1.ne'
  have hcard : #(univ.erase (0 : ZMod p)) = p - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  refine eq_of_degree_le_of_eval_finset_eq (univ.erase (0 : ZMod p)) ?_ ?_ ?_ ?_
  · rw [degree_eq_natDegree hmon.ne_zero, hnd, hcard]
  · rw [degree_eq_natDegree hmon.ne_zero, hnd, hdeg2]
  · rw [hmon.leadingCoeff, hmon2.leadingCoeff]
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_mem_erase hx
    rw [eval_sub, eval_pow, eval_X, eval_C, ZMod.pow_card_sub_one_eq_one hx0, sub_self,
      eval_prod]
    have hv : 1 ≤ x.val :=
      Nat.one_le_iff_ne_zero.mpr (fun h0 => hx0 ((ZMod.val_eq_zero x).mp h0))
    have hvp : x.val < p := ZMod.val_lt x
    apply prod_eq_zero (i := p - 1 - x.val)
    · rw [mem_range]; omega
    · rw [eval_add, eval_X, eval_C]
      have : ((p - 1 - x.val : ℕ) : ZMod p) + 1 = ((p - x.val : ℕ) : ZMod p) := by
        rw [← Nat.cast_succ]; congr 1; omega
      rw [this, Nat.cast_sub hvp.le, ZMod.natCast_self, ZMod.natCast_zmod_val]
      ring

lemma dvd_coeff_two (p : ℕ) [hp : Fact p.Prime] (h : p > 3) :
    (p : ℤ) ∣ (wg p).coeff 2 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hm : (wg p).map (Int.castRingHom (ZMod p)) =
      ∏ i ∈ range (p - 1), (X + C ((i : ZMod p) + 1)) := by
    simp [wg, Polynomial.map_prod]
  have := congrArg (fun f => f.coeff 2) hm
  simp only [coeff_map, eq_intCast] at this
  rw [this, prod_eq_X_pow_sub_one p, coeff_sub, coeff_X_pow, coeff_C,
    if_neg (by omega), if_neg (by norm_num), sub_zero]

lemma eval_zero_wg (p : ℕ) : (wg p).eval 0 = ((p - 1).factorial : ℤ) := by
  simp only [wg, eval_prod, eval_add, eval_X, eval_C, zero_add]
  rw [← Finset.prod_range_add_one_eq_factorial]
  push_cast
  rfl

lemma eval_neg_wg (p : ℕ) [hp : Fact p.Prime] (h : p > 3) :
    (wg p).eval (-(p : ℤ)) = (wg p).eval 0 := by
  simp only [wg, eval_prod, eval_add, eval_X, eval_C, zero_add]
  have h1 : ∀ i ∈ range (p - 1),
      (-(p : ℤ) + ((i : ℤ) + 1)) = (-1) * (((p - 1 - 1 - i : ℕ) : ℤ) + 1) := by
    intro i hi
    rw [mem_range] at hi
    have : ((p - 1 - 1 - i : ℕ) : ℤ) = (p : ℤ) - 2 - i := by omega
    rw [this]; ring
  have hr := prod_range_reflect (fun j : ℕ => (j : ℤ) + 1) (p - 1)
  rw [prod_congr rfl h1, prod_mul_distrib, prod_const, card_range, hr]
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have hev : Even (p - 1) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  rw [hev.neg_one_pow, one_mul]

lemma eval_p_wg (p : ℕ) (h : p > 3) :
    (wg p).eval (p : ℤ) = (((p - 1).factorial * (2 * p - 1).choose (p - 1) : ℕ) : ℤ) := by
  have h2 : 2 * p - 1 = p + (p - 1) := by omega
  rw [h2, ← Nat.ascFactorial_eq_factorial_mul_choose, Nat.ascFactorial_eq_prod_range]
  simp only [wg, eval_prod, eval_add, eval_X, eval_C]
  push_cast
  exact prod_congr rfl (fun i _ => by ring)

theorem wolstenholme_theorem (p : ℕ) (h : p > 3) (hp : Nat.Prime p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by
  have := Fact.mk hp
  obtain ⟨u, hu⟩ := cube_dvd_eval_sub (wg p) p
  obtain ⟨v, hv⟩ := cube_dvd_eval_sub (wg p) (-p)
  obtain ⟨b, hb⟩ := dvd_coeff_two p h
  have h0 : (wg p).coeff 0 = (wg p).eval 0 := coeff_zero_eq_eval_zero _
  rw [h0, hb] at hu hv
  rw [eval_neg_wg p h] at hv
  have key : (wg p).eval (p : ℤ) - (wg p).eval 0 = (p : ℤ) ^ 3 * (u + 2 * b - v) := by
    linear_combination hu + hv
  rw [eval_p_wg p h, eval_zero_wg p] at key
  have hcop : Nat.gcd (p ^ 3) (p - 1).factorial = 1 := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp, Nat.Prime.dvd_factorial hp]
    omega
  apply Nat.ModEq.cancel_left_of_coprime hcop
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
  refine ⟨u + 2 * b - v, ?_⟩
  push_cast at key ⊢
  linear_combination key

end WolstenholmePrime

#print axioms WolstenholmePrime.wolstenholme_theorem
