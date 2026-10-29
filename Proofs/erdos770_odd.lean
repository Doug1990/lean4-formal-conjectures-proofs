import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Factorization.Induction

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

lemma mem_iff (n m : ℕ) : ((m : ℕ∞) ∈ {m : ℕ∞ | 2 < m ∧
    ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1}) ↔
      2 < m ∧ ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id = 1 := by
  change (2 < (m : ℕ∞) ∧ _) ↔ _
  rw [ENat.toNat_natCast]
  norm_cast

/-- `h n ≤ n + 1` for `n ≥ 2`. -/
lemma h_le {n : ℕ} (hn : 2 ≤ n) : h n ≤ ((n + 1 : ℕ) : ℕ∞) := by
  apply sInf_le
  exact (mem_iff n (n + 1)).mpr ⟨by omega, gcd_eq_one_of_le (by omega) le_rfl⟩

/-- A prime dividing all `i ^ n - 1` for `2 ≤ i ≤ m` forces `h n > m`. -/
lemma h_ge {n m p : ℕ} (hp : p.Prime) (H : ∀ i ∈ Finset.Icc 2 m, p ∣ i ^ n - 1) :
    ((m + 1 : ℕ) : ℕ∞) ≤ h n := by
  apply le_sInf
  intro x hx
  induction x using ENat.recTopCoe with
  | top => exact le_top
  | coe k =>
    obtain ⟨hk, hg⟩ := (mem_iff n k).mp hx
    apply ENat.natCast_le_natCast.mpr
    by_contra hlt
    exact (gcd_eq_one_iff n k).mp hg p hp (fun i hi => H i (by
      rcases Finset.mem_Icc.mp hi with ⟨h1, h2⟩; exact Finset.mem_Icc.mpr ⟨h1, by omega⟩))

/-- If `p ≡ 7 mod 8` and `ℓ ∣ p + 1`, then the prime `ℓ` is a square mod `p`. -/
lemma isSquare_prime {p ℓ : ℕ} [Fact p.Prime] (hℓ : ℓ.Prime) (hp8 : p % 8 = 7)
    (hdvd : ℓ ∣ p + 1) : IsSquare (ℓ : ZMod p) := by
  have hp3 : p % 4 = 3 := by omega
  have hp2 : p ≠ 2 := by omega
  rcases hℓ.eq_two_or_odd with rfl | hodd
  · simp only [Nat.cast_ofNat]
    exact (ZMod.exists_sq_eq_two_iff hp2).mpr (Or.inr hp8)
  · have := Fact.mk hℓ
    have hpl : (p : ZMod ℓ) = -1 := by
      have h0 : ((p + 1 : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      push_cast at h0
      exact eq_neg_of_add_eq_zero_left h0
    have hlp : ℓ ≠ p := by
      intro e
      subst e
      have := (Nat.dvd_add_right (dvd_refl ℓ)).mp hdvd
      have := Nat.le_of_dvd one_pos this
      have := hℓ.two_le
      omega
    rcases (show ℓ % 4 = 1 ∨ ℓ % 4 = 3 by omega) with h1 | h3
    · have hsq : IsSquare (p : ZMod ℓ) := by
        rw [hpl]
        exact ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
      exact (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one h1 hp2).mp hsq
    · apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hp3 h3 hlp.symm).mpr
      rw [hpl]
      intro hsq
      exact ZMod.exists_sq_eq_neg_one_iff.mp hsq h3

lemma isSquare_le {p m : ℕ} [Fact p.Prime] (hp8 : p % 8 = 7) (hdvd : m.factorial ∣ p + 1) :
    ∀ i, 1 ≤ i → i ≤ m → IsSquare (i : ZMod p) := by
  intro i
  induction i using Nat.recOnMul with
  | zero => intro h; omega
  | one => intro _ _; exact ⟨1, by simp⟩
  | prime ℓ hℓ =>
    intro _ hle
    exact isSquare_prime hℓ hp8 ((Nat.dvd_factorial hℓ.pos hle).trans hdvd)
  | mul a b iha ihb =>
    intro h1 hle
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    have hab : a ≤ a * b := Nat.le_mul_of_pos_right a hb
    have hba : b ≤ a * b := Nat.le_mul_of_pos_left b ha
    rw [Nat.cast_mul]
    exact (iha ha (by omega)).mul (ihb hb (by omega))

lemma exists_odd_h_ge (m : ℕ) : ∃ n, 2 ≤ n ∧ Odd n ∧ ((m + 1 : ℕ) : ℕ∞) ≤ h n := by
  have hM : NeZero (8 * m.factorial) := ⟨by positivity⟩
  obtain ⟨p, hpgt, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    (q := 8 * m.factorial) (a := -1) isUnit_one.neg (m + 5)
  have := Fact.mk hp
  have hdvd : 8 * m.factorial ∣ p + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hpmod]
    simp
  have hp8 : p % 8 = 7 := by
    have := (Dvd.intro _ rfl : 8 ∣ 8 * m.factorial).trans hdvd
    omega
  have hfac : m.factorial ∣ p + 1 := (Dvd.intro_left _ rfl).trans hdvd
  refine ⟨p / 2, by omega, Nat.odd_iff.mpr (by omega), h_ge hp (fun i hi => ?_)⟩
  rcases Finset.mem_Icc.mp hi with ⟨h1, h2⟩
  have hsq := isSquare_le hp8 hfac i (by omega) h2
  have hi0 : (i : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have he := (ZMod.euler_criterion (p := p) hi0).mp hsq
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
  push_cast
  rw [he, sub_self]

/-- For odd `n`, the values of `h n` form an unbounded set.
This is described as 'easy to see' in [Er74b]. -/
theorem erdos_770.variants.odd_h_unbounded : Unbounded (· ≤ ·) (ENat.toNat '' (h '' Odd)):= by
  intro a
  obtain ⟨n, hn2, hodd, hge⟩ := exists_odd_h_ge a
  have hle : h n ≤ ((n + 1 : ℕ) : ℕ∞) := h_le hn2
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hle)
  refine ⟨j, ⟨h n, ⟨n, hodd, rfl⟩, by rw [← hj, ENat.toNat_natCast]⟩, ?_⟩
  rw [← hj] at hge
  have := ENat.natCast_le_natCast.mp hge
  show ¬ j ≤ a
  omega

#print axioms erdos_770.variants.odd_h_unbounded

end Erdos770
