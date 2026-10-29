import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Metric Bornology

scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

open scoped EuclideanGeometry

namespace Borsuk

variable {E : Type*} [PseudoEMetricSpace E]

def HasBorsukCover (k : ℕ) (s : Set E) : Prop :=
  ∃ c : Fin k → Set E, s ⊆ ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam s

def BorsukConjecture (n : ℕ) : Prop :=
  ∀ s : Set (ℝ^n), IsBounded s → s.Nontrivial → HasBorsukCover (n + 1) s

/-- The coordinate map `ℝ^1 → ℝ`. -/
def proj1 (x : ℝ^1) : ℝ := x.ofLp 0

theorem proj1_isometry : Isometry proj1 := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.sqrt_sq dist_nonneg]
  rfl

theorem ediam_half_lt {a b : ℝ} (hab : a < b) :
    ENNReal.ofReal ((b - a) / 2) < ENNReal.ofReal (b - a) := by
  rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
  linarith

/-- Transfer a small real interval through an isometry `f : E → ℝ`. -/
theorem ediam_preimage_lt {f : E → ℝ} (hf : Isometry f) {s : Set E} {a b : ℝ}
    (hs : ediam s = ENNReal.ofReal (b - a)) (hab : a < b) (I : Set ℝ)
    (hI : ediam I ≤ ENNReal.ofReal ((b - a) / 2)) :
    ediam (s ∩ f ⁻¹' I) < ediam s := by
  rw [← hf.ediam_image, hs]
  calc ediam (f '' (s ∩ f ⁻¹' I)) ≤ ediam I :=
        ediam_mono (Set.image_subset_iff.mpr Set.inter_subset_right)
    _ ≤ ENNReal.ofReal ((b - a) / 2) := hI
    _ < ENNReal.ofReal (b - a) := ediam_half_lt hab

theorem borsuk_conjecture.one : BorsukConjecture 1 := by
  intro s hs hnt
  have hf : Isometry proj1 := proj1_isometry
  have ht : IsBounded (proj1 '' s) := hf.lipschitz.isBounded_image hs
  obtain ⟨x, hx, y, hy, hxy⟩ := hnt
  have hab : sInf (proj1 '' s) < sSup (proj1 '' s) := by
    have h1 : proj1 x ∈ proj1 '' s := ⟨x, hx, rfl⟩
    have h2 : proj1 y ∈ proj1 '' s := ⟨y, hy, rfl⟩
    have hne : proj1 x ≠ proj1 y := fun h => hxy (hf.injective h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact lt_of_le_of_lt (csInf_le ht.bddBelow h1)
        (lt_of_lt_of_le h (le_csSup ht.bddAbove h2))
    · exact lt_of_le_of_lt (csInf_le ht.bddBelow h2)
        (lt_of_lt_of_le h (le_csSup ht.bddAbove h1))
  have hs_eq : ediam s = ENNReal.ofReal (sSup (proj1 '' s) - sInf (proj1 '' s)) := by
    rw [← hf.ediam_image s, Real.ediam_eq ht]
  have hlo : ∀ z ∈ s, sInf (proj1 '' s) ≤ proj1 z := fun z hz =>
    csInf_le ht.bddBelow ⟨z, hz, rfl⟩
  have hhi : ∀ z ∈ s, proj1 z ≤ sSup (proj1 '' s) := fun z hz =>
    le_csSup ht.bddAbove ⟨z, hz, rfl⟩
  generalize sInf (proj1 '' s) = a at hab hs_eq hlo
  generalize sSup (proj1 '' s) = b at hab hs_eq hhi
  refine ⟨![s ∩ proj1 ⁻¹' Set.Icc a ((a + b) / 2), s ∩ proj1 ⁻¹' Set.Icc ((a + b) / 2) b],
    ?_, ?_⟩
  · intro z hz
    rcases le_total (proj1 z) ((a + b) / 2) with h | h
    · exact Set.mem_iUnion.mpr ⟨0, ⟨hz, hlo z hz, h⟩⟩
    · exact Set.mem_iUnion.mpr ⟨1, ⟨hz, h, hhi z hz⟩⟩
  · intro i
    fin_cases i
    · refine ediam_preimage_lt hf hs_eq hab _ ?_
      rw [Real.ediam_Icc]
      exact le_of_eq (congrArg ENNReal.ofReal (by ring))
    · refine ediam_preimage_lt hf hs_eq hab _ ?_
      rw [Real.ediam_Icc]
      exact le_of_eq (congrArg ENNReal.ofReal (by ring))

end Borsuk

#print axioms Borsuk.borsuk_conjecture.one
