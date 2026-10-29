import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Instances.Rat
import Mathlib.SetTheory.Cardinal.Basic

open scoped Cardinal

namespace Erdos261

def Erdos261InfiniteRepresentation (x : ℚ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (1 ≤ a) ∧ Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)

/-- `∑_{k ≥ 0} k / 2^k = 2` in `ℝ`. -/
lemma hasSum_base : HasSum (fun k : ℕ => (k : ℝ) / 2 ^ k) 2 := by
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 1 / 2)
    (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)
  have e : (fun k : ℕ => (k : ℝ) / 2 ^ k) = fun n : ℕ => (n : ℝ) * (1 / 2) ^ n := by
    funext k
    rw [one_div, inv_pow, div_eq_mul_inv]
  have v : (1 / 2 : ℝ) / (1 - 1 / 2) ^ 2 = 2 := by norm_num
  rw [v] at h
  rw [e]
  exact h

/-- A rational series whose real cast has a rational sum has that sum in `ℚ`. -/
lemma hasSum_rat {g : ℕ → ℚ} {q : ℚ} (h : HasSum (fun k => (g k : ℝ)) (q : ℝ)) :
    HasSum g q := by
  have hi : Topology.IsInducing (Rat.castHom ℝ) :=
    Rat.isUniformEmbedding_coe_real.isUniformInducing.isInducing
  exact (hi.hasSum_iff g q).1 h

/-- Enumeration of `ℕ_{>0} \ {4}`. -/
def seqA (k : ℕ) : ℕ := if k < 3 then k + 1 else k + 2

/-- Enumeration of `ℕ_{>0} \ {5, 6}`. -/
def seqB (k : ℕ) : ℕ := if k < 4 then k + 1 else k + 3

noncomputable def FA (k : ℕ) : ℝ := (k : ℝ) / 2 ^ k - (if k = 4 then (4 : ℝ) / 2 ^ 4 else 0)

noncomputable def FB (k : ℕ) : ℝ := (k : ℝ) / 2 ^ k - (if k = 5 then (5 : ℝ) / 2 ^ 5 else 0)
  - (if k = 6 then (6 : ℝ) / 2 ^ 6 else 0)

lemma seqA_mono : StrictMono seqA := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold seqA
  split_ifs <;> omega

lemma seqB_mono : StrictMono seqB := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold seqB
  split_ifs <;> omega

lemma hasSum_FA : HasSum FA (2 - (4 : ℝ) / 2 ^ 4) := by
  exact hasSum_base.sub (hasSum_ite_eq (4 : ℕ) ((4 : ℝ) / 2 ^ 4))

lemma hasSum_FB : HasSum FB (2 - (5 : ℝ) / 2 ^ 5 - (6 : ℝ) / 2 ^ 6) := by
  exact (hasSum_base.sub (hasSum_ite_eq (5 : ℕ) ((5 : ℝ) / 2 ^ 5))).sub
    (hasSum_ite_eq (6 : ℕ) ((6 : ℝ) / 2 ^ 6))

lemma repA : Erdos261InfiniteRepresentation (7 / 4) seqA := by
  have hrange : ∀ x, x ∉ Set.range seqA → FA x = 0 := by
    intro x hx
    by_cases h0 : x = 0
    · subst h0; simp [FA]
    by_cases h4 : x = 4
    · subst h4; simp [FA]
    exfalso
    apply hx
    by_cases h3 : x ≤ 3
    · exact ⟨x - 1, by unfold seqA; split_ifs <;> omega⟩
    · exact ⟨x - 2, by unfold seqA; split_ifs <;> omega⟩
  have hA : HasSum (FA ∘ seqA) (2 - (4 : ℝ) / 2 ^ 4) :=
    (seqA_mono.injective.hasSum_iff hrange).2 hasSum_FA
  have hQ : HasSum (fun k => (seqA k : ℚ) / (2 ^ (seqA k) : ℚ)) (7 / 4) := by
    apply hasSum_rat
    show HasSum (fun k => (((seqA k : ℚ) / 2 ^ (seqA k) : ℚ) : ℝ)) ((7 / 4 : ℚ) : ℝ)
    have e : (fun k => (((seqA k : ℚ) / 2 ^ (seqA k) : ℚ) : ℝ)) = FA ∘ seqA := by
      funext k
      have h4 : seqA k ≠ 4 := by unfold seqA; split_ifs <;> omega
      simp only [Function.comp, FA, if_neg h4]
      push_cast
      ring
    have v : ((7 / 4 : ℚ) : ℝ) = 2 - (4 : ℝ) / 2 ^ 4 := by norm_num
    rw [e, v]
    exact hA
  refine ⟨seqA_mono, ?_, hQ.summable, hQ.tsum_eq.symm⟩
  intro k
  show 1 ≤ seqA k
  unfold seqA; split_ifs <;> omega

lemma repB : Erdos261InfiniteRepresentation (7 / 4) seqB := by
  have hrange : ∀ x, x ∉ Set.range seqB → FB x = 0 := by
    intro x hx
    by_cases h0 : x = 0
    · subst h0; simp [FB]
    by_cases h5 : x = 5
    · subst h5; simp [FB]
    by_cases h6 : x = 6
    · subst h6; simp [FB]
    exfalso
    apply hx
    by_cases h3 : x ≤ 4
    · exact ⟨x - 1, by unfold seqB; split_ifs <;> omega⟩
    · exact ⟨x - 3, by unfold seqB; split_ifs <;> omega⟩
  have hB : HasSum (FB ∘ seqB) (2 - (5 : ℝ) / 2 ^ 5 - (6 : ℝ) / 2 ^ 6) :=
    (seqB_mono.injective.hasSum_iff hrange).2 hasSum_FB
  have hQ : HasSum (fun k => (seqB k : ℚ) / (2 ^ (seqB k) : ℚ)) (7 / 4) := by
    apply hasSum_rat
    show HasSum (fun k => (((seqB k : ℚ) / 2 ^ (seqB k) : ℚ) : ℝ)) ((7 / 4 : ℚ) : ℝ)
    have e : (fun k => (((seqB k : ℚ) / 2 ^ (seqB k) : ℚ) : ℝ)) = FB ∘ seqB := by
      funext k
      have h5 : seqB k ≠ 5 := by unfold seqB; split_ifs <;> omega
      have h6 : seqB k ≠ 6 := by unfold seqB; split_ifs <;> omega
      simp only [Function.comp, FB, if_neg h5, if_neg h6]
      push_cast
      ring
    have v : ((7 / 4 : ℚ) : ℝ) = 2 - (5 : ℝ) / 2 ^ 5 - (6 : ℝ) / 2 ^ 6 := by norm_num
    rw [e, v]
    exact hB
  refine ⟨seqB_mono, ?_, hQ.summable, hQ.tsum_eq.symm⟩
  intro k
  show 1 ≤ seqB k
  unfold seqB; split_ifs <;> omega

theorem erdos_261.variants.two_representations : ∃ x : ℚ,
    2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  refine ⟨7 / 4, ?_⟩
  rw [Cardinal.two_le_iff]
  refine ⟨⟨seqA, repA⟩, ⟨seqB, repB⟩, fun h => ?_⟩
  have h3 := congrFun (congrArg Subtype.val h) 3
  simp [seqA, seqB] at h3

end Erdos261

#print axioms Erdos261.erdos_261.variants.two_representations
