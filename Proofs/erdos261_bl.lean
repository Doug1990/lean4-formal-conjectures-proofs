import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Erdos261

def Erdos261Prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)

/-- Telescoping tail sum: `∑_{a < k ≤ a + j} k / 2^k = (a+2)/2^a - (a+j+2)/2^(a+j)`. -/
lemma sum_Ioc_tail (a j : ℕ) :
    ∑ k ∈ Finset.Ioc a (a + j), (k : ℚ) / 2 ^ k
      = ((a : ℚ) + 2) / 2 ^ a - ((a : ℚ) + j + 2) / 2 ^ (a + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← Nat.add_assoc, Finset.sum_Ioc_succ_top (by omega), ih]
    push_cast
    rw [pow_succ]
    field_simp
    ring

/-- Reindex a sum over `Ioc a (a + j)` as a sum over `Fin j`. -/
lemma sum_Ioc_eq_sum_fin (f : ℕ → ℚ) (a j : ℕ) :
    ∑ k ∈ Finset.Ioc a (a + j), f k = ∑ i : Fin j, f (a + 1 + i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← Nat.add_assoc, Finset.sum_Ioc_succ_top (by omega), ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    congr 2
    omega

/-- `n + m + 2 = 2^(m+1)` for `n = 2^(m+1) - m - 2`. -/
lemma key (m : ℕ) : 2 ^ (m + 1) - m - 2 + m + 2 = 2 ^ (m + 1) := by
  have : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
  omega

theorem erdos_261.variants.borwein_loring (m : ℕ) (hm : 0 < m) :
    let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ) := by
  -- the identity holds for every `m`; the hypothesis is not needed
  clear hm
  intro n
  rw [sum_Ioc_tail]
  have h : ((n : ℕ) : ℚ) + m + 2 = 2 * 2 ^ m := by
    have := key m
    have h2 : ((n + m + 2 : ℕ) : ℚ) = ((2 ^ (m + 1) : ℕ) : ℚ) := by
      exact_mod_cast this
    push_cast at h2
    rw [h2, pow_succ]; ring
  rw [h, pow_add]
  field_simp
  ring

theorem erdos_261.variants.borwein_loring_property (m : ℕ) (hm : 2 ≤ m) :
    Erdos261Prop (2 ^ (m + 1) - m - 2) := by
  set n := 2 ^ (m + 1) - m - 2 with hn
  refine ⟨m, hm, fun i => n + 1 + i, ?_, ?_, ?_⟩
  · intro i j hij
    exact Fin.ext (by simpa using hij)
  · intro i
    show 1 ≤ n + 1 + (i : ℕ)
    omega
  · rw [erdos_261.variants.borwein_loring m (by omega), sum_Ioc_eq_sum_fin]

theorem erdos_261.parts.i : {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite := by
  have hmono : StrictMono (fun m : ℕ => 2 ^ (m + 3) - (m + 2) - 2) := by
    apply strictMono_nat_of_lt_succ
    intro m
    have h1 : m + 3 < 2 ^ (m + 3) := Nat.lt_two_pow_self
    have h2 : 2 ^ (m + 1 + 3) = 2 * 2 ^ (m + 3) := by ring
    show 2 ^ (m + 3) - (m + 2) - 2 < 2 ^ (m + 1 + 3) - (m + 1 + 2) - 2
    omega
  refine Set.infinite_of_injective_forall_mem hmono.injective ?_
  intro m
  refine ⟨?_, erdos_261.variants.borwein_loring_property (m + 2) (by omega)⟩
  have h1 : m + 3 < 2 ^ (m + 3) := Nat.lt_two_pow_self
  have h2 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
  have h3 : m < 2 ^ m := Nat.lt_two_pow_self
  show 0 < 2 ^ (m + 2 + 1) - (m + 2) - 2
  rw [show m + 2 + 1 = m + 3 by omega]
  omega

end Erdos261

#print axioms Erdos261.erdos_261.variants.borwein_loring
#print axioms Erdos261.erdos_261.variants.borwein_loring_property
#print axioms Erdos261.erdos_261.parts.i
