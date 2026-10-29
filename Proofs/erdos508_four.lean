import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

open SimpleGraph

namespace SimpleGraph

def UnitDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj x y := dist x y = 1
  symm.symm x y := by simp [dist_comm]

end SimpleGraph

namespace Erdos508

scoped notation "χ(ℝ²)" => SimpleGraph.chromaticNumber (UnitDistancePlaneGraph Set.univ)

lemma unit (a b c d : ℝ) (h : (a - c) ^ 2 + (b - d) ^ 2 = 1) :
    dist (!₂[a, b]) (!₂[c, d]) = 1 := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs]
  simp [h]

lemma col (a b c d e f g : Fin 3)
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) (h4 : b ≠ d) (h5 : c ≠ d)
    (h6 : a ≠ e) (h7 : a ≠ f) (h8 : e ≠ f) (h9 : e ≠ g) (h10 : f ≠ g) (h11 : d ≠ g) :
    False := by
  simp only [ne_eq, Fin.ext_iff] at *
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  have := e.isLt; have := f.isLt; have := g.isLt
  omega

theorem HadwigerNelsonAtLeast4 : 4 ≤ χ(ℝ²) := by
  refine le_of_not_gt fun h ↦ ?_
  obtain ⟨c⟩ := chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_add_one h)
  set s : ℝ := Real.sqrt 3 with hs_def
  set t : ℝ := Real.sqrt 11 with ht_def
  have hs : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ht : t ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  let P : ℝ → ℝ → (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) :=
    fun x y => ⟨!₂[x, y], Set.mem_univ _⟩
  have adj : ∀ a b x y : ℝ, (a - x) ^ 2 + (b - y) ^ 2 = 1 → c (P a b) ≠ c (P x y) :=
    fun a b x y hh => c.valid (unit a b x y hh)
  refine col (c (P 0 0)) (c (P (s/2) (1/2))) (c (P (s/2) (-1/2))) (c (P s 0))
    (c (P (5*s/12 - t/12) (s*t/12 + 5/12))) (c (P (5*s/12 + t/12) (s*t/12 - 5/12)))
    (c (P (5*s/6) (s*t/6))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  · apply adj
    ring_nf <;> (try simp only [hs, ht]) <;> norm_num

end Erdos508

#print axioms Erdos508.HadwigerNelsonAtLeast4
