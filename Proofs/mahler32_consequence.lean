import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Real.Pointwise
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Filter.AtTopBot.Basic

/-- Restated from FormalConjecturesForMathlib/NumberTheory/DiophantineApproximation/ZNumber.lean -/
def IsZNumber (ξ : ℝ) : Prop :=
  0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → Int.fract (ξ * (3 / 2 : ℝ) ^ n) < 1 / 2

namespace Mahler32

noncomputable def Ω (α : ℝ) : ℝ :=
  sInf {Filter.atTop.limsup (fun n ↦ Int.fract (θ * α ^ n))
    - Filter.atTop.liminf (fun n ↦ Int.fract (θ * α ^ n)) | (θ : ℝ) (_ : 0 < θ)}

/-- For a Z-number `x`, the oscillation of `{x (3/2)^n}` is at most `1/2`. -/
lemma osc_le_half {x : ℝ} (hx : IsZNumber x) :
    Filter.atTop.limsup (fun n : ℕ ↦ Int.fract (x * (3 / 2 : ℝ) ^ n))
      - Filter.atTop.liminf (fun n : ℕ ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) ≤ 1 / 2 := by
  have h1 : Filter.atTop.limsup (fun n : ℕ ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) ≤ 1 / 2 := by
    apply Filter.limsup_le_of_le
      (Filter.isCoboundedUnder_le_of_le Filter.atTop (fun n => Int.fract_nonneg _))
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (hx.2 n hn).le
  have h2 : (0 : ℝ) ≤ Filter.atTop.liminf (fun n : ℕ ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) := by
    apply Filter.le_liminf_of_le
      (Filter.isCoboundedUnder_ge_of_le Filter.atTop (fun n => (Int.fract_lt_one _).le))
    exact Filter.Eventually.of_forall (fun n => Int.fract_nonneg _)
  linarith

theorem mahler_conjecture.variants.consequence (H : 1 / 2 < Ω (3 / 2)) :
    -- `type_of% mahler_conjecture`, spelled out (the open conjecture itself is not restated here)
    ∀ (x : ℝ) (_hx : IsZNumber x), False := by
  intro x hx
  have hmem : Filter.atTop.limsup (fun n : ℕ ↦ Int.fract (x * (3 / 2 : ℝ) ^ n))
      - Filter.atTop.liminf (fun n : ℕ ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) ∈
      {Filter.atTop.limsup (fun n ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n))
        - Filter.atTop.liminf (fun n ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n)) |
        (θ : ℝ) (_ : 0 < θ)} := ⟨x, hx.1, rfl⟩
  by_cases hb : BddBelow {Filter.atTop.limsup (fun n ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n))
        - Filter.atTop.liminf (fun n ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n)) |
        (θ : ℝ) (_ : 0 < θ)}
  · have := csInf_le hb hmem
    have := osc_le_half hx
    unfold Ω at H
    linarith
  · unfold Ω at H
    rw [Real.sInf_of_not_bddBelow hb] at H
    norm_num at H

end Mahler32

#print axioms Mahler32.mahler_conjecture.variants.consequence
