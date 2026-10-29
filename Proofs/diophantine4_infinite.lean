import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace DiophantineTuple

variable {R : Type*} [Semiring R]

def IsDiophantineTuple (s : Finset R) : Prop :=
  (∀ x ∈ s, x ≠ 0) ∧
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsSquare (x * y + 1)

abbrev IsIntegralDiophantineTuple (s : Finset ℕ) : Prop := IsDiophantineTuple (R := ℕ) s

def integralDiophantine4Tuple : Set (Finset ℕ) :=
  { s | IsIntegralDiophantineTuple s ∧ s.card = 4 }

/-- The family `{n, n + 2, 4n + 4, 16n³ + 48n² + 44n + 12}`. -/
def family (n : ℕ) : Finset ℕ :=
  {n, n + 2, 4 * n + 4, 16 * n ^ 3 + 48 * n ^ 2 + 44 * n + 12}

lemma family_mem (n : ℕ) (hn : 1 ≤ n) : family n ∈ integralDiophantine4Tuple := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [family, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx] <;> omega
  · intro x hx y hy hxy
    simp only [family, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
      rw [hx, hy] at hxy ⊢ <;>
      first
      | exact absurd rfl hxy
      | (refine ⟨n + 1, ?_⟩; ring1)
      | (refine ⟨2 * n + 1, ?_⟩; ring1)
      | (refine ⟨2 * n + 3, ?_⟩; ring1)
      | (refine ⟨4 * n ^ 2 + 6 * n + 1, ?_⟩; ring1)
      | (refine ⟨4 * n ^ 2 + 10 * n + 5, ?_⟩; ring1)
      | (refine ⟨8 * n ^ 2 + 16 * n + 7, ?_⟩; ring1)
  · have h1 : n ∉ ({n + 2, 4 * n + 4, 16 * n ^ 3 + 48 * n ^ 2 + 44 * n + 12} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      generalize n ^ 3 = c
      generalize n ^ 2 = s
      omega
    have h2 : n + 2 ∉ ({4 * n + 4, 16 * n ^ 3 + 48 * n ^ 2 + 44 * n + 12} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      generalize n ^ 3 = c
      generalize n ^ 2 = s
      omega
    have h3 : 4 * n + 4 ≠ 16 * n ^ 3 + 48 * n ^ 2 + 44 * n + 12 := by
      generalize n ^ 3 = c
      generalize n ^ 2 = s
      omega
    simp only [family]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_pair h3]

lemma family_injective : Function.Injective (fun k : ℕ => family (k + 1)) := by
  have key : ∀ a b : ℕ, a < b → a + 1 ∉ family (b + 1) := by
    intro a b hab h
    simp only [family, Finset.mem_insert, Finset.mem_singleton] at h
    generalize (b + 1) ^ 3 = c at h
    generalize (b + 1) ^ 2 = s at h
    omega
  intro a b h
  simp only at h
  rcases lt_trichotomy a b with hab | hab | hab
  · have : a + 1 ∈ family (b + 1) := by rw [← h]; simp [family]
    exact absurd this (key a b hab)
  · exact hab
  · have : b + 1 ∈ family (a + 1) := by rw [h]; simp [family]
    exact absurd this (key b a hab)

/-- The source states this as an anonymous `example`; it is named here for `#print axioms`. -/
theorem integralDiophantine4Tuple_encard_eq_top : integralDiophantine4Tuple.encard = ⊤ := by
  apply Set.Infinite.encard_eq
  exact Set.infinite_of_injective_forall_mem family_injective
    (fun k => family_mem (k + 1) (by omega))

end DiophantineTuple

#print axioms DiophantineTuple.integralDiophantine4Tuple_encard_eq_top
