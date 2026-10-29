import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Positivity

namespace OeisA87719

open Nat

/-- Count of numbers k in {1, ..., m} where k > (minFac k)^n. -/
def countExceeding (n m : ℕ) : ℕ :=
  (Finset.Icc 1 m).filter (fun k => k > k.minFac ^ n) |>.card

/-- Count of numbers k in {1, ..., m} where k ≤ (minFac k)^n. -/
def countNotExceeding (n m : ℕ) : ℕ :=
  (Finset.Icc 1 m).filter (fun k => k ≤ k.minFac ^ n) |>.card

/-- The map enumerating the numbers `6(B + j) + c` with `c ∈ {2,3,4,6}`. -/
def g (B x : ℕ) : ℕ :=
  6 * B + 6 * (x / 4) +
    (if x % 4 = 0 then 2 else if x % 4 = 1 then 3 else if x % 4 = 2 then 4 else 6)

lemma g_inj (B : ℕ) : Function.Injective (g B) := by
  intro x y h
  unfold g at h
  have hx := Nat.mod_lt x (show 4 > 0 by norm_num)
  have hy := Nat.mod_lt y (show 4 > 0 by norm_num)
  split_ifs at h <;> omega

lemma g_dvd (B x : ℕ) : 2 ∣ g B x ∨ 3 ∣ g B x := by
  unfold g
  have hx := Nat.mod_lt x (show 4 > 0 by norm_num)
  split_ifs <;> omega

lemma g_bounds (B x : ℕ) (hx : x < 16 * B) : 6 * B < g B x ∧ g B x ≤ 30 * B := by
  unfold g
  have := Nat.mod_lt x (show 4 > 0 by norm_num)
  split_ifs <;> omega

lemma exceeds_of_dvd (n k : ℕ) (hk : 3 ^ n < k) (h : 2 ∣ k ∨ 3 ∣ k) :
    k.minFac ^ n < k := by
  have hm : k.minFac ≤ 3 := by
    rcases h with h | h
    · exact (Nat.minFac_le_of_dvd (by omega) h).trans (by omega)
    · exact Nat.minFac_le_of_dvd (by omega) h
  exact lt_of_le_of_lt (Nat.pow_le_pow_left hm n) hk

theorem a_exists (n : ℕ) : ∃ m, countExceeding n m > countNotExceeding n m := by
  set B := 3 ^ n with hB
  have hBpos : 0 < B := by positivity
  refine ⟨30 * B, ?_⟩
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 (30 * B)) (fun k => k > k.minFac ^ n)
  simp only [not_lt, Nat.card_Icc] at hsum
  have hE : 16 * B ≤ countExceeding n (30 * B) := by
    have := Finset.card_le_card_of_injOn (s := Finset.range (16 * B))
      (t := (Finset.Icc 1 (30 * B)).filter (fun k => k > k.minFac ^ n)) (g B)
      (by
        intro x hx
        have hx' : x < 16 * B := Finset.mem_range.mp hx
        obtain ⟨h1, h2⟩ := g_bounds B x hx'
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc]
        refine ⟨⟨by omega, h2⟩, ?_⟩
        exact exceeds_of_dvd n _ (by omega) (g_dvd B x))
      ((g_inj B).injOn)
    simpa [countExceeding] using this
  unfold countExceeding countNotExceeding at *
  omega

end OeisA87719

#print axioms OeisA87719.a_exists
