import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Order.Interval.Finset.Nat

open Filter Real
open scoped Pointwise

/-- Local copy of `IsSumFree` from `FormalConjecturesForMathlib.Combinatorics.Basic`. -/
def IsSumFree {M : Type*} [Add M] (S : Set M) : Prop := Disjoint (S + S) S

namespace Erdos748

open scoped Classical in
noncomputable def f (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ)).card

lemma sumFree_of_subset (n : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Ioc (n / 2) n) :
    IsSumFree (A : Set ℕ) := by
  rw [IsSumFree, Set.disjoint_left]
  rintro z ⟨x, hx, y, hy, rfl⟩ hz
  beta_reduce at hz
  have hx' := Finset.mem_Ioc.mp (hA hx)
  have hy' := Finset.mem_Ioc.mp (hA hy)
  have hz' := Finset.mem_Ioc.mp (hA hz)
  omega

lemma pow_le_f (n : ℕ) : 2 ^ (n - n / 2) ≤ f n := by
  classical
  unfold f
  have h1 : (Finset.Ioc (n / 2) n).powerset ⊆
      ((Finset.Icc 1 n).powerset.filter fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ)) := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun x hx => ?_, sumFree_of_subset n A hA⟩
    have := Finset.mem_Ioc.mp (hA hx)
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  have h2 := Finset.card_le_card h1
  rw [Finset.card_powerset, Nat.card_Ioc] at h2
  convert h2 using 2

theorem erdos_748.variants.lower_bound (n : ℕ) :
    (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (f n : ℝ) := by
  have h1 : (n : ℝ) / 2 ≤ ((n - n / 2 : ℕ) : ℝ) := by
    have h3 : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
    have h4 : ((n / 2 : ℕ) : ℝ) * 2 ≤ n := by exact_mod_cast h3
    rw [Nat.cast_sub (Nat.div_le_self n 2)]
    linarith
  calc (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (2 : ℝ) ^ (((n - n / 2 : ℕ)) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = ((2 ^ (n - n / 2) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
    _ ≤ (f n : ℝ) := by exact_mod_cast pow_le_f n

end Erdos748

#print axioms Erdos748.erdos_748.variants.lower_bound
