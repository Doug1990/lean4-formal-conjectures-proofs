import Mathlib.LinearAlgebra.Lagrange
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Rat.Lemmas

open Polynomial Finset

namespace WolstenholmePrime

def IsWolstenholmePrime (p : ℕ) : Prop :=
  p > 7 ∧ p.Prime ∧ (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4]

/-- The polynomial `(X + 1) (X + 2) ⋯ (X + n)` over `ℤ`. -/
noncomputable def wf (n : ℕ) : ℤ[X] := ∏ i ∈ range n, (X + C ((i : ℤ) + 1))

/-- The polynomial `(X + 1) (X + 2) ⋯ (X + (p - 1))` over `ℤ`. -/
noncomputable def wg (p : ℕ) : ℤ[X] := wf (p - 1)

lemma wf_coeff01 (n : ℕ) :
    (wf n).coeff 0 = (n.factorial : ℤ) ∧
      ((wf n).coeff 1 : ℚ) = (n.factorial : ℚ) * harmonic n := by
  induction n with
  | zero => simp [wf, coeff_one]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have hs : wf (n + 1) = wf n * X + wf n * C ((n : ℤ) + 1) := by
      rw [wf, prod_range_succ, ← wf, mul_add]
    have c0 : (wf (n + 1)).coeff 0 = (wf n).coeff 0 * ((n : ℤ) + 1) := by
      rw [hs, coeff_add, coeff_mul_X_zero, coeff_mul_C, zero_add]
    have c1 : (wf (n + 1)).coeff 1 = (wf n).coeff 0 + (wf n).coeff 1 * ((n : ℤ) + 1) := by
      rw [hs, coeff_add, coeff_mul_X, coeff_mul_C]
    refine ⟨?_, ?_⟩
    · rw [c0, h0, Nat.factorial_succ]; push_cast; ring
    · rw [c1]; push_cast; rw [h0, h1, harmonic_succ, Nat.factorial_succ]; push_cast
      field_simp
      ring

/-- `t ^ 4` divides `g t` minus the cubic Taylor part of `g` at `0`. -/
lemma pow4_dvd_eval_sub (g : ℤ[X]) (t : ℤ) :
    t ^ 4 ∣ g.eval t - (g.coeff 0 + g.coeff 1 * t + g.coeff 2 * t ^ 2 + g.coeff 3 * t ^ 3) := by
  have h : (X : ℤ[X]) ^ 4 ∣
      g - (C (g.coeff 0) + C (g.coeff 1) * X + C (g.coeff 2) * X ^ 2
        + C (g.coeff 3) * X ^ 3) := by
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

lemma dvd_coeff (p : ℕ) [hp : Fact p.Prime] (j : ℕ) (hj0 : j ≠ 0) (hj : j ≠ p - 1) :
    (p : ℤ) ∣ (wg p).coeff j := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hm : (wg p).map (Int.castRingHom (ZMod p)) =
      ∏ i ∈ range (p - 1), (X + C ((i : ZMod p) + 1)) := by
    simp [wg, wf, Polynomial.map_prod]
  have := congrArg (fun f => f.coeff j) hm
  simp only [coeff_map, eq_intCast] at this
  rw [this, prod_eq_X_pow_sub_one p, coeff_sub, coeff_X_pow, coeff_C,
    if_neg hj, if_neg hj0, sub_zero]

lemma eval_zero_wg (p : ℕ) : (wg p).eval 0 = ((p - 1).factorial : ℤ) := by
  simp only [wg, wf, eval_prod, eval_add, eval_X, eval_C, zero_add]
  rw [← Finset.prod_range_add_one_eq_factorial]
  push_cast
  rfl

lemma eval_neg_wg (p : ℕ) [hp : Fact p.Prime] (h : p > 3) :
    (wg p).eval (-(p : ℤ)) = (wg p).eval 0 := by
  simp only [wg, wf, eval_prod, eval_add, eval_X, eval_C, zero_add]
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
  simp only [wg, wf, eval_prod, eval_add, eval_X, eval_C]
  push_cast
  exact prod_congr rfl (fun i _ => by ring)

/-- `(p-1)! (C(2p-1,p-1) - 1) = 2 p c₁ + p⁴ K`. -/
lemma key_identity (p : ℕ) [hp : Fact p.Prime] (h : p > 7) :
    ∃ K : ℤ, ((p - 1).factorial : ℤ) * (((2 * p - 1).choose (p - 1) : ℕ) - 1) =
      2 * p * (wg p).coeff 1 + (p : ℤ) ^ 4 * K := by
  obtain ⟨u, hu⟩ := pow4_dvd_eval_sub (wg p) p
  obtain ⟨v, hv⟩ := pow4_dvd_eval_sub (wg p) (-p)
  obtain ⟨b, hb⟩ := dvd_coeff p 3 (by norm_num) (by omega)
  have h0 : (wg p).coeff 0 = (wg p).eval 0 := coeff_zero_eq_eval_zero _
  rw [h0, hb] at hu hv
  rw [eval_neg_wg p (by omega)] at hv
  rw [eval_p_wg p (by omega), eval_zero_wg p] at hu
  rw [eval_zero_wg p] at hv
  refine ⟨2 * b + u - v, ?_⟩
  push_cast at hu hv ⊢
  linear_combination hu - hv

lemma coprime_fact (p : ℕ) (hp : p.Prime) (k : ℕ) :
    IsCoprime ((p : ℤ) ^ k) ((p - 1).factorial : ℤ) := by
  have : Nat.Coprime (p ^ k) (p - 1).factorial := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp, Nat.Prime.dvd_factorial hp]
    have := hp.one_lt
    omega
  have := Nat.isCoprime_iff_coprime.mpr this
  push_cast at this
  exact this

lemma partA (p : ℕ) (hp : p.Prime) (h : p > 7) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4] ↔ (p : ℤ) ^ 3 ∣ (wg p).coeff 1 := by
  have := Fact.mk hp
  obtain ⟨K, hK⟩ := key_identity p h
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
  push_cast
  have hc := coprime_fact p hp 4
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h2 : IsCoprime ((p : ℤ) ^ 3) 2 := by
    have : Nat.Coprime (p ^ 3) 2 :=
      Nat.Coprime.pow_left 3 ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    have := Nat.isCoprime_iff_coprime.mpr this
    push_cast at this
    exact this
  have e1 : (p : ℤ) ^ 4 ∣ (((2 * p - 1).choose (p - 1) : ℕ) : ℤ) - 1 ↔
      (p : ℤ) ^ 4 ∣ 2 * p * (wg p).coeff 1 := by
    have hh : (p : ℤ) ^ 4 ∣ 2 * p * (wg p).coeff 1 + (p : ℤ) ^ 4 * K ↔
        (p : ℤ) ^ 4 ∣ 2 * p * (wg p).coeff 1 := dvd_add_left (dvd_mul_right _ K)
    rw [← hK] at hh
    rw [← hh]
    constructor
    · intro hd; exact dvd_mul_of_dvd_right hd _
    · intro hd; exact hc.dvd_of_dvd_mul_left hd
  rw [e1]
  have e2 : (p : ℤ) ^ 4 ∣ 2 * p * (wg p).coeff 1 ↔ (p : ℤ) ^ 3 ∣ 2 * (wg p).coeff 1 := by
    rw [show (p : ℤ) ^ 4 = p * p ^ 3 by ring,
      show 2 * (p : ℤ) * (wg p).coeff 1 = p * (2 * (wg p).coeff 1) by ring,
      mul_dvd_mul_iff_left hp0]
  rw [e2]
  constructor
  · intro hd; exact h2.dvd_of_dvd_mul_left hd
  · intro hd; exact dvd_mul_of_dvd_right hd _

lemma partB (p : ℕ) (hp : p.Prime) :
    (p : ℤ) ^ 3 ∣ (wg p).coeff 1 ↔ (p : ℤ) ^ 3 ∣ (harmonic (p - 1)).num := by
  set H := harmonic (p - 1) with hH
  have hc1 : ((wg p).coeff 1 : ℚ) = ((p - 1).factorial : ℚ) * H := (wf_coeff01 (p - 1)).2
  have e := Rat.num_div_den H
  have hD : (H.den : ℚ) ≠ 0 := by exact_mod_cast H.den_ne_zero
  rw [div_eq_iff hD] at e
  have hq : ((wg p).coeff 1 : ℚ) * H.den = H.num * ((p - 1).factorial : ℚ) := by
    rw [hc1, e]; ring
  have hz : (wg p).coeff 1 * H.den = H.num * ((p - 1).factorial : ℤ) := by
    exact_mod_cast hq
  have hc := coprime_fact p hp 3
  constructor
  · intro hd
    have : (p : ℤ) ^ 3 ∣ H.num * ((p - 1).factorial : ℤ) := by
      rw [← hz]; exact dvd_mul_of_dvd_left hd _
    exact hc.dvd_of_dvd_mul_right this
  · intro hd
    have hpD : ¬ p ∣ H.den := by
      intro hpd
      have hpn : (p : ℤ) ∣ H.num := dvd_trans (dvd_pow_self _ (by norm_num)) hd
      have hpn' : p ∣ H.num.natAbs := Int.ofNat_dvd_left.mp hpn
      have := Nat.eq_one_of_dvd_coprimes H.reduced hpn' hpd
      exact hp.one_lt.ne' this
    have hcD : IsCoprime ((p : ℤ) ^ 3) (H.den : ℤ) := by
      have : Nat.Coprime (p ^ 3) H.den :=
        Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpD)
      have := Nat.isCoprime_iff_coprime.mpr this
      push_cast at this
      exact this
    have : (p : ℤ) ^ 3 ∣ (wg p).coeff 1 * H.den := by
      rw [hz]; exact dvd_mul_of_dvd_left hd _
    exact hcD.dvd_of_dvd_mul_right this

theorem wolstenholme_harmonic (p : ℕ) : IsWolstenholmePrime p ↔
    (p > 7) ∧ Nat.Prime p ∧ ↑(p ^ 3) ∣ (harmonic (p - 1)).num := by
  unfold IsWolstenholmePrime
  constructor
  · rintro ⟨h7, hp, hm⟩
    refine ⟨h7, hp, ?_⟩
    push_cast
    exact (partB p hp).mp ((partA p hp h7).mp hm)
  · rintro ⟨h7, hp, hd⟩
    refine ⟨h7, hp, ?_⟩
    push_cast at hd
    exact (partA p hp h7).mpr ((partB p hp).mpr hd)

end WolstenholmePrime

#print axioms WolstenholmePrime.wolstenholme_harmonic
