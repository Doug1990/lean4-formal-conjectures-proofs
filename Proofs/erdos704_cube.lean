import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Filter
open scoped Topology

namespace Erdos704

def unitDistanceGraph (n : ℕ) : SimpleGraph (EuclideanSpace ℝ (Fin n)) where
  Adj x y := dist x y = 1
  symm.symm x y := by simp [dist_comm]

/-- If the cube indices agree mod `m ≥ t + 1`, either they agree or the points are far apart. -/
lemma key (t : ℝ) (m : ℕ) (ht : 0 < t) (hm : t + 1 ≤ m) (a b : ℝ)
    (h : (m : ℤ) ∣ ⌊b * t⌋ - ⌊a * t⌋) : ⌊a * t⌋ = ⌊b * t⌋ ∨ 1 < |a - b| := by
  obtain ⟨c, hc⟩ := h
  have ha1 := Int.floor_le (a * t)
  have ha2 := Int.lt_floor_add_one (a * t)
  have hb1 := Int.floor_le (b * t)
  have hb2 := Int.lt_floor_add_one (b * t)
  rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
  · right
    have hc' : c ≤ -1 := by omega
    have : ⌊b * t⌋ - ⌊a * t⌋ ≤ -(m : ℤ) := by rw [hc]; nlinarith
    have hR : ((⌊b * t⌋ : ℤ) : ℝ) - ⌊a * t⌋ ≤ -(m : ℝ) := by exact_mod_cast this
    have h2 : (a - b) * t > 1 * t := by nlinarith
    have h3 : 1 < a - b := lt_of_mul_lt_mul_right h2 ht.le
    exact lt_abs.mpr (Or.inl h3)
  · left
    subst hc0
    omega
  · right
    have hc' : 1 ≤ c := by omega
    have : (m : ℤ) ≤ ⌊b * t⌋ - ⌊a * t⌋ := by rw [hc]; nlinarith
    have hR : (m : ℝ) ≤ ((⌊b * t⌋ : ℤ) : ℝ) - ⌊a * t⌋ := by exact_mod_cast this
    have h2 : (b - a) * t > 1 * t := by nlinarith
    have h3 : 1 < b - a := lt_of_mul_lt_mul_right h2 ht.le
    rw [abs_sub_comm]
    exact lt_abs.mpr (Or.inl h3)

/-- Points in the same cube of side `1 / t` are close in each coordinate. -/
lemma key2 (t a b : ℝ) (h : ⌊a * t⌋ = ⌊b * t⌋) : (a - b) ^ 2 * t ^ 2 < 1 := by
  have ha1 := Int.floor_le (a * t)
  have ha2 := Int.lt_floor_add_one (a * t)
  have hb1 := Int.floor_le (b * t)
  have hb2 := Int.lt_floor_add_one (b * t)
  rw [h] at ha1 ha2
  have e : (a - b) ^ 2 * t ^ 2 = (a * t - b * t) ^ 2 := by ring
  rw [e]
  have h1 : a * t - b * t < 1 := by linarith
  have h2 : -1 < a * t - b * t := by linarith
  nlinarith [mul_pos (sub_pos.mpr h1) (neg_lt_iff_pos_add.mp h2)]

lemma colour (n t : ℕ) (ht : (n : ℝ) < (t : ℝ) ^ 2) (ht0 : 0 < t) :
    (unitDistanceGraph n).Colorable ((t + 1) ^ n) := by
  have : NeZero (t + 1) := ⟨by omega⟩
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  let C : (unitDistanceGraph n).Coloring (Fin n → ZMod (t + 1)) :=
    SimpleGraph.Coloring.mk (fun x i => ((⌊x i * (t : ℝ)⌋ : ℤ) : ZMod (t + 1))) (by
      intro x y hxy heq
      have hd : dist x y = 1 := hxy
      have hsq : ∑ i, (x i - y i) ^ 2 = 1 := by
        have := EuclideanSpace.dist_sq_eq x y
        rw [hd] at this
        simp only [Real.dist_eq, sq_abs] at this
        linarith
      have hfl : ∀ i, ⌊x i * (t : ℝ)⌋ = ⌊y i * (t : ℝ)⌋ := by
        intro i
        have hi := congrFun heq i
        simp only at hi
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
        have hle : (x i - y i) ^ 2 ≤ 1 := hsq ▸ Finset.single_le_sum
          (f := fun j => (x j - y j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        rcases key (t : ℝ) (t + 1) htR (by push_cast; exact le_refl _) (x i) (y i) hi with h | h
        · exact h
        · exfalso
          have h0 : (0 : ℝ) ≤ |x i - y i| := abs_nonneg _
          have : 1 < (x i - y i) ^ 2 := by
            rw [← sq_abs]; nlinarith
          linarith
      have hlt : ∀ i, (x i - y i) ^ 2 * (t : ℝ) ^ 2 < 1 := fun i => key2 _ _ _ (hfl i)
      have hs : ∑ i, (x i - y i) ^ 2 * (t : ℝ) ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (hlt i).le)
      rw [← Finset.sum_mul, hsq] at hs
      simp at hs
      linarith)
  have := C.colorable
  simpa [ZMod.card, Fintype.card_fun] using this

theorem erdos_704.variants.cube_colouring :
    ∀ n : ℕ, ∃ k : ℕ, (unitDistanceGraph n).Colorable k ∧
      (k : ℝ) ≤ (2 + Real.sqrt n) ^ n := by
  intro n
  refine ⟨(Nat.sqrt n + 1 + 1) ^ n, colour n _ ?_ (by omega), ?_⟩
  · have h := Real.real_sqrt_lt_nat_sqrt_succ (a := n)
    have h0 := Real.sqrt_nonneg (n : ℝ)
    have h1 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
    push_cast
    nlinarith
  · have h := Real.nat_sqrt_le_real_sqrt (a := n)
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by linarith) n

end Erdos704

#print axioms Erdos704.erdos_704.variants.cube_colouring
