import Mathlib

namespace LeinsterGroup

open scoped Classical in
def IsLeinster (G : Type*) [Group G] [Fintype G] : Prop :=
  ∑ H : {H : Subgroup G // H.Normal}, Nat.card H = 2 * Fintype.card G

/-- In a finite cyclic group, two subgroups of the same order coincide. -/
lemma subgroup_eq_of_card_eq {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (H K : Subgroup G) (h : Nat.card H = Nat.card K) : H = K := by
  classical
  have hdpos : 0 < Nat.card K := Nat.card_pos
  -- `K` is exactly the set of solutions of `x ^ d = 1`
  have hK : ∀ x : G, x ^ Nat.card K = 1 → x ∈ K := by
    intro x hx
    by_contra hxK
    have hsub : (insert x (Finset.univ.filter (fun y : G => y ∈ K))) ⊆
        Finset.univ.filter (fun y : G => y ^ Nat.card K = 1) := by
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · simpa using hx
      · rw [Finset.mem_filter] at hy ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have h1 : ((⟨y, hy.2⟩ : K) ^ Nat.card K) = 1 := pow_card_eq_one'
        have h2 := congrArg Subtype.val h1
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
    have hcard := Finset.card_le_card hsub
    have hle := IsCyclic.card_pow_eq_one_le (α := G) hdpos
    rw [Finset.card_insert_of_notMem (by simpa using hxK)] at hcard
    have : (Finset.univ.filter (fun y : G => y ∈ K)).card = Nat.card K := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    omega
  have hle : H ≤ K := by
    intro x hx
    apply hK
    rw [← h]
    have h1 : ((⟨x, hx⟩ : H) ^ Nat.card H) = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h])

theorem cyclic_of_perfect_is_leinster (G : Type*) [Group G] [Fintype G]
    [IsCyclic G] (h_perfect : Nat.Perfect (Fintype.card G)) :
    IsLeinster G := by
  classical
  unfold IsLeinster
  have hn := (Nat.perfect_iff_sum_divisors_eq_two_mul Fintype.card_pos).mp h_perfect
  rw [← hn]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  refine Finset.sum_bij (fun H _ => Nat.card H.1) ?_ ?_ ?_ ?_
  · intro H _
    rw [Nat.mem_divisors]
    refine ⟨?_, Fintype.card_ne_zero⟩
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card H.1
  · intro H _ K _ hHK
    exact Subtype.ext (subgroup_eq_of_card_eq H.1 K.1 hHK)
  · intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨⟨m, hm⟩, hne⟩ := hd
    have hmpos : m ≠ 0 := by
      rintro rfl; simp_all
    refine ⟨⟨Subgroup.zpowers (g ^ m), ?_⟩, Finset.mem_univ _, ?_⟩
    · constructor
      intro x hx y
      have hc : ∀ a b : G, a * b = b * a := fun a b =>
        (IsCyclic.isMulCommutative (α := G)).is_comm.comm a b
      rw [hc y x, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    · simp only
      rw [Nat.card_zpowers, orderOf_pow_of_dvd hmpos, hg, Nat.card_eq_fintype_card, hm,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hmpos)]
      rw [hg, Nat.card_eq_fintype_card, hm]
      exact Dvd.intro_left _ rfl
  · intro H _
    rfl

end LeinsterGroup

#print axioms LeinsterGroup.cyclic_of_perfect_is_leinster
