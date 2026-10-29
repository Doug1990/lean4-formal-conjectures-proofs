import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open SimpleGraph

namespace SimpleGraph

def UnitDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj x y := dist x y = 1
  symm.symm x y := by simp [dist_comm]

end SimpleGraph

namespace Erdos508

scoped notation "χ(ℝ²)" => SimpleGraph.chromaticNumber (UnitDistancePlaneGraph Set.univ)

/-- Two points of bricks whose column indices differ by a multiple of 7 are not at distance 1.
Bricks have width 4/5, height 11/20, and row `j` is shifted by `48/25 * j`. -/
lemma core (X Y : ℝ) (a b : ℤ)
    (hX1 : ((a : ℝ) - 1) * (4/5) + (48/25) * b < X) (hX2 : X < ((a : ℝ) + 1) * (4/5) + (48/25) * b)
    (hY1 : ((b : ℝ) - 1) * (11/20) < Y) (hY2 : Y < ((b : ℝ) + 1) * (11/20))
    (h7 : (7 : ℤ) ∣ a) (h : X ^ 2 + Y ^ 2 = 1) : False := by
  have hXl : -1 ≤ X := by nlinarith [sq_nonneg (X + 1), sq_nonneg Y]
  have hXu : X ≤ 1 := by nlinarith [sq_nonneg (X - 1), sq_nonneg Y]
  have hYl : -1 ≤ Y := by nlinarith [sq_nonneg (Y + 1), sq_nonneg X]
  have hYu : Y ≤ 1 := by nlinarith [sq_nonneg (Y - 1), sq_nonneg X]
  have hb1 : b ≤ 2 := by
    by_contra hc
    have : (3 : ℝ) ≤ b := by exact_mod_cast (show (3 : ℤ) ≤ b by omega)
    linarith
  have hb2 : -2 ≤ b := by
    by_contra hc
    have : (b : ℝ) ≤ -3 := by exact_mod_cast (show b ≤ -3 by omega)
    linarith
  have hbr1 : (b : ℝ) ≤ 2 := by exact_mod_cast hb1
  have hbr2 : (-2 : ℝ) ≤ b := by exact_mod_cast hb2
  obtain ⟨m, rfl⟩ := h7
  have hm1 : m ≤ 1 := by
    by_contra hc
    have : (2 : ℝ) ≤ m := by exact_mod_cast (show (2 : ℤ) ≤ m by omega)
    push_cast at hX1
    linarith
  have hm2 : -1 ≤ m := by
    by_contra hc
    have : (m : ℝ) ≤ -2 := by exact_mod_cast (show m ≤ -2 by omega)
    push_cast at hX2
    linarith
  interval_cases m <;> interval_cases b <;> norm_num at hX1 hX2 hY1 hY2 <;> nlinarith

/-- Row index of a point. -/
noncomputable def row (p : EuclideanSpace ℝ (Fin 2)) : ℤ := ⌊p 1 * (20/11)⌋

/-- Column index of a point. -/
noncomputable def column (p : EuclideanSpace ℝ (Fin 2)) : ℤ :=
  ⌊(p 0 - (48/25) * (row p : ℝ)) * (5/4)⌋

lemma pair (p q : EuclideanSpace ℝ (Fin 2)) (h7 : (7 : ℤ) ∣ column q - column p)
    (h : (q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 = 1) : False := by
  have j1 := Int.floor_le (p 1 * (20/11))
  have j2 := Int.lt_floor_add_one (p 1 * (20/11))
  have j3 := Int.floor_le (q 1 * (20/11))
  have j4 := Int.lt_floor_add_one (q 1 * (20/11))
  have i1 := Int.floor_le ((p 0 - (48/25) * (row p : ℝ)) * (5/4))
  have i2 := Int.lt_floor_add_one ((p 0 - (48/25) * (row p : ℝ)) * (5/4))
  have i3 := Int.floor_le ((q 0 - (48/25) * (row q : ℝ)) * (5/4))
  have i4 := Int.lt_floor_add_one ((q 0 - (48/25) * (row q : ℝ)) * (5/4))
  rw [← row] at j1 j2 j3 j4
  rw [← column] at i1 i2 i3 i4
  refine core (q 0 - p 0) (q 1 - p 1) (column q - column p) (row q - row p) ?_ ?_ ?_ ?_ h7 h
  · push_cast; linarith
  · push_cast; linarith
  · push_cast; linarith
  · push_cast; linarith

theorem HadwigerNelsonAtMostSeven :
    χ(ℝ²) ≤ 7 := by
  let C : (UnitDistancePlaneGraph (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))).Coloring (ZMod 7) :=
    Coloring.mk (fun p => ((column p.1 : ℤ) : ZMod 7)) (by
      intro p q hpq heq
      have hd : dist p.1 q.1 = 1 := hpq
      rw [EuclideanSpace.dist_eq, Real.sqrt_eq_one] at hd
      simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hd
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at heq
      exact pair p.1 q.1 (by exact_mod_cast heq) (by rw [← hd]; ring))
  have hc := C.colorable
  simp only [ZMod.card] at hc
  exact_mod_cast hc.chromaticNumber_le

end Erdos508

#print axioms Erdos508.HadwigerNelsonAtMostSeven
