import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Nat

namespace Erdos780

/-- Colour of an edge: `min (t-1) (min' e / (k-1))`. -/
lemma sharp_aux (N k r t : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hN : N = k * r - 1 + (t - 1) * (k - 1)) :
    ∃ c : {e : Finset (Fin N) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin N) // e.card = r}),
        (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1 := by
  have hne : ∀ e : {e : Finset (Fin N) // e.card = r}, e.1.Nonempty := fun e =>
    Finset.card_pos.mp (by rw [e.2]; omega)
  refine ⟨fun e => ⟨min (t - 1) ((e.1.min' (hne e)).val / (k - 1)), by omega⟩, ?_⟩
  rintro ⟨i, e, hc, hdisj⟩
  have hq : ∀ j, min (t - 1) (((e j).1.min' (hne (e j))).val / (k - 1)) = i := fun j =>
    congrArg Fin.val (hc j)
  have hk1 : 0 < k - 1 := by omega
  by_cases hi : (i : ℕ) < t - 1
  · -- all minima lie in one block of size k - 1
    have hdiv : ∀ j, ((e j).1.min' (hne (e j))).val / (k - 1) = i := by
      intro j; have := hq j; omega
    let f : Fin k → Fin (k - 1) := fun j =>
      ⟨((e j).1.min' (hne (e j))).val % (k - 1), Nat.mod_lt _ hk1⟩
    have hf : Function.Injective f := by
      intro a b hab
      by_contra hne'
      have h1 : ((e a).1.min' (hne (e a))).val % (k - 1)
          = ((e b).1.min' (hne (e b))).val % (k - 1) := congrArg Fin.val hab
      have h2 : (e a).1.min' (hne (e a)) = (e b).1.min' (hne (e b)) := by
        apply Fin.ext
        rw [← Nat.div_add_mod ((e a).1.min' (hne (e a))).val (k - 1),
          ← Nat.div_add_mod ((e b).1.min' (hne (e b))).val (k - 1), h1, hdiv a, hdiv b]
      have hma := (e a).1.min'_mem (hne (e a))
      have hmb := (e b).1.min'_mem (hne (e b))
      rw [h2] at hma
      exact Finset.disjoint_left.mp (hdisj hne') hma hmb
    have := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at this
    omega
  · -- all edges lie in the last block, of size k * r - 1
    have hlow : ∀ j, ∀ x ∈ (e j).1, (t - 1) * (k - 1) ≤ x.val := by
      intro j x hx
      have h1 : t - 1 ≤ ((e j).1.min' (hne (e j))).val / (k - 1) := by
        have := hq j; omega
      rw [Nat.le_div_iff_mul_le hk1] at h1
      have h2 := (e j).1.min'_le x hx
      have h3 : ((e j).1.min' (hne (e j))).val ≤ x.val := h2
      omega
    set S := Finset.univ.biUnion (fun j => (e j).1) with hS
    have hcard : S.card = k * r := by
      rw [hS, Finset.card_biUnion]
      · simp only [(e _).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      · intro a _ b _ hab
        exact hdisj hab
    have hle : S.card ≤ (Finset.range (k * r - 1)).card := by
      apply Finset.card_le_card_of_injOn (fun x : Fin N => x.val - (t - 1) * (k - 1))
      · intro x hx
        simp only [hS, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
          Set.mem_iUnion, Finset.mem_coe] at hx
        obtain ⟨j, hj⟩ := hx
        have := hlow j x hj
        have := x.isLt
        simp only [Finset.coe_range, Set.mem_Iio]
        omega
      · intro x hx y hy hxy
        simp only [hS, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
          Set.mem_iUnion, Finset.mem_coe] at hx hy
        obtain ⟨j, hj⟩ := hx
        obtain ⟨j', hj'⟩ := hy
        have := hlow j x hj
        have := hlow j' y hj'
        apply Fin.ext
        simp only at hxy
        omega
    rw [hcard, Finset.card_range] at hle
    have : 0 < k * r := Nat.mul_pos (by omega) (by omega)
    omega

theorem erdos_780.variants.sharp (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1 := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    refine ⟨fun _ => ⟨0, ht⟩, ?_⟩
    rintro ⟨i, e, -, -⟩
    have h1 := Finset.card_le_univ (e 0).1
    rw [(e 0).2, Fintype.card_fin] at h1
    omega
  · exact sharp_aux _ k r t hk2 hr ht rfl

end Erdos780

#print axioms Erdos780.erdos_780.variants.sharp
