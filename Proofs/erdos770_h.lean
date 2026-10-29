import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.GCDMonoid.Finset

open Set ENat Filter

namespace Erdos770

/-- Let $h n$ be the minimal number such that $2 ^ n - 1, \dots, h(n) ^ n - 1$
are collectively coprime. -/
noncomputable def h (n : ℕ) : ℕ∞ := sInf {m | 2 < m ∧
  ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1}

lemma gcd_eq_one_iff (n m : ℕ) :
    ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id = 1 ↔
      ∀ q : ℕ, q.Prime → ¬ ∀ i ∈ Finset.Icc 2 m, q ∣ i ^ n - 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  simp only [Finset.dvd_gcd_iff, Finset.forall_mem_image, id]

lemma roots_of_dvd {n m q : ℕ} (hn : 1 ≤ n) (hq : q.Prime)
    (H : ∀ i ∈ Finset.Icc 2 m, q ∣ i ^ n - 1) :
    m < q ∧ ∀ i ∈ Finset.Icc 1 m, ((i : ℕ) : ZMod q) ^ n = 1 := by
  have key : ∀ i ∈ Finset.Icc 2 m, ((i : ℕ) : ZMod q) ^ n = 1 := by
    intro i hi
    have h1 : 1 ≤ i ^ n := Nat.one_le_pow _ _ (by simp at hi; omega)
    have := (ZMod.natCast_eq_zero_iff _ _).mpr (H i hi)
    rw [Nat.cast_sub h1] at this
    push_cast at this
    exact sub_eq_zero.mp this
  refine ⟨?_, ?_⟩
  · have := Fact.mk hq
    by_contra hlt
    have hlt' : q ≤ m := by omega
    have hq2 := hq.two_le
    have := key q (Finset.mem_Icc.mpr ⟨hq2, hlt'⟩)
    rw [ZMod.natCast_self, zero_pow (by omega)] at this
    exact zero_ne_one this
  · intro i hi
    rcases Finset.mem_Icc.mp hi with ⟨h1, h2⟩
    rcases Nat.lt_or_ge i 2 with h | h
    · have : i = 1 := by omega
      subst this; simp
    · exact key i (Finset.mem_Icc.mpr ⟨h, h2⟩)

lemma le_of_roots {n M q : ℕ} [Fact q.Prime] (hn : 1 ≤ n) (hMq : M < q)
    (H : ∀ i ∈ Finset.Icc 1 M, ((i : ℕ) : ZMod q) ^ n = 1) : M ≤ n := by
  classical
  have hinj : Set.InjOn (fun i : ℕ => ((i : ℕ) : ZMod q)) (Finset.Icc 1 M : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' a b q).mp hab
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hsub : (Finset.Icc 1 M).image (fun i : ℕ => ((i : ℕ) : ZMod q)) ⊆
      (Polynomial.nthRoots n (1 : ZMod q)).toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
    exact H i hi
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Nat.card_Icc] at this
  calc M = M + 1 - 1 := by omega
    _ ≤ _ := this
    _ ≤ Multiset.card (Polynomial.nthRoots n (1 : ZMod q)) := Multiset.toFinset_card_le _
    _ ≤ n := Polynomial.card_nthRoots n 1

lemma gcd_eq_one_of_le {n m : ℕ} (hn : 1 ≤ n) (hm : n + 1 ≤ m) :
    ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id = 1 := by
  rw [gcd_eq_one_iff]
  intro q hq H
  have := Fact.mk hq
  obtain ⟨hlt, hr⟩ := roots_of_dvd hn hq H
  have := le_of_roots hn hlt hr
  omega

lemma gcd_ne_one_of_prime {n m : ℕ} (hp : (n + 1).Prime) (hm : m ≤ n) :
    ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id ≠ 1 := by
  rw [Ne, gcd_eq_one_iff]
  push Not
  refine ⟨n + 1, hp, fun i hi => ?_⟩
  have := Fact.mk hp
  rcases Finset.mem_Icc.mp hi with ⟨h1, h2⟩
  have hi0 : ((i : ℕ) : ZMod (n + 1)) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by omega) h0
    omega
  have hf := ZMod.pow_card_sub_one_eq_one hi0
  rw [show n + 1 - 1 = n by omega] at hf
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
  push_cast
  rw [hf, sub_self]

lemma gcd_eq_one_of_composite {n : ℕ} (hn : 2 < n) (hp : ¬ (n + 1).Prime) :
    ((Finset.Icc 2 n).image fun i => (i ^ n - 1)).gcd id = 1 := by
  rw [gcd_eq_one_iff]
  intro q hq H
  have := Fact.mk hq
  obtain ⟨hlt, hr⟩ := roots_of_dvd (by omega) hq H
  obtain ⟨a, ⟨b, hab⟩, ha2, han⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hp
  have hb2 : 2 ≤ b := by
    by_contra hb
    have hb' : b ≤ 1 := by omega
    interval_cases b
    · simp at hab
    · simp at hab; omega
  have hbn : b ≤ n := by nlinarith
  have hq' : n + 1 < q := by
    rcases Nat.lt_or_ge (n + 1) q with h | h
    · exact h
    · exfalso
      have : q = n + 1 := by omega
      exact hp (this ▸ hq)
  have hr' : ∀ i ∈ Finset.Icc 1 (n + 1), ((i : ℕ) : ZMod q) ^ n = 1 := by
    intro i hi
    rcases Finset.mem_Icc.mp hi with ⟨h1, h2⟩
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact hr i (Finset.mem_Icc.mpr ⟨h1, by omega⟩)
    · have hi : i = a * b := by omega
      rw [hi, Nat.cast_mul, mul_pow, hr a (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
        hr b (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), one_mul]
  have := le_of_roots (by omega) hq' hr'
  omega

lemma mem_iff (n m : ℕ) : ((m : ℕ∞) ∈ {m : ℕ∞ | 2 < m ∧
    ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1}) ↔
      2 < m ∧ ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id = 1 := by
  change (2 < (m : ℕ∞) ∧ _) ↔ _
  rw [ENat.toNat_natCast]
  norm_cast

/-- `n + 1` is prime iff `h n = n + 1`. This is described as 'easy to see' in [Er74b]. -/
theorem Nat.Prime.h_eq_add_one {n : ℕ} (hn : 2 < n) : h n = n + 1 ↔ (n + 1).Prime := by
  have hS : ∀ m : ℕ, 2 < m → ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id = 1 →
      h n ≤ (m : ℕ∞) := by
    intro m hm hg
    apply sInf_le
    exact (mem_iff n m).mpr ⟨hm, hg⟩
  have hcast : ((n : ℕ∞) + 1) = ((n + 1 : ℕ) : ℕ∞) := by push_cast; rfl
  rw [hcast]
  constructor
  · intro heq
    by_contra hp
    have := hS n hn (gcd_eq_one_of_composite hn hp)
    rw [heq] at this
    have := ENat.natCast_le_natCast.mp this
    omega
  · intro hp
    apply le_antisymm
    · exact hS (n + 1) (by omega) (gcd_eq_one_of_le (by omega) le_rfl)
    · apply le_sInf
      intro x hx
      induction x using ENat.recTopCoe with
      | top => exact le_top
      | coe m =>
        obtain ⟨hm, hg⟩ := (mem_iff n m).mp hx
        apply ENat.natCast_le_natCast.mpr
        by_contra hlt
        exact gcd_ne_one_of_prime hp (by omega) hg

#print axioms Nat.Prime.h_eq_add_one

end Erdos770
