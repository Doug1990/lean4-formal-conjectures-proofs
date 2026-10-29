import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
import Mathlib.Tactic.NormNum

open SimpleGraph

namespace Erdos640

/-- An odd cycle whose vertices induce a graph of chromatic number at least `k`. -/
def HasHighChromaticOddCycle {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ Odd p.length ∧
    (k : ℕ∞) ≤ (G.induce {x | x ∈ p.support}).chromaticNumber

/-- Every odd closed walk contains an odd cycle. -/
lemma exists_odd_cycle {V : Type*} (G : SimpleGraph V) :
    ∀ (n : ℕ) {u : V} (w : G.Walk u u), w.length = n → Odd n →
      ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ Odd c.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u w hw hodd
  cases w with
  | nil =>
    simp at hw
    subst hw
    exact absurd hodd (by decide)
  | @cons _ x _ h p =>
    simp only [Walk.length_cons] at hw
    by_cases hp : p.IsPath
    · by_cases he : s(u, x) ∈ p.edges
      · exfalso
        have h1 := hp.length_eq_one_of_mem_edges (by rwa [Sym2.eq_swap] at he)
        rw [h1] at hw
        subst hw
        exact absurd hodd (by decide)
      · refine ⟨u, _, (Walk.cons_isCycle_iff p h).mpr ⟨hp, he⟩, ?_⟩
        simp only [Walk.length_cons, hw]
        exact hodd
    · rw [Walk.isPath_iff_isSubwalk_imp_nil] at hp
      push Not at hp
      obtain ⟨y, c, ⟨r1, r2, hpe⟩, hcn⟩ := hp
      have hcl : 0 < c.length := Walk.not_nil_iff_lt_length.mp hcn
      have hlen : p.length = r1.length + c.length + r2.length := by
        rw [hpe]
        simp only [Walk.length_append]
      rw [Nat.odd_iff] at hodd
      rcases Nat.even_or_odd c.length with hce | hco
      · rw [Nat.even_iff] at hce
        have hlt : (Walk.cons h (r1.append r2)).length < n := by
          simp only [Walk.length_cons, Walk.length_append]
          omega
        refine ih _ hlt (Walk.cons h (r1.append r2)) rfl ?_
        rw [Nat.odd_iff]
        simp only [Walk.length_cons, Walk.length_append]
        omega
      · exact ih _ (by omega) c rfl hco

/-- A walk inside `S` lifts to the induced subgraph with the same length. -/
lemma lift {V : Type*} (G : SimpleGraph V) (S : Set V) :
    ∀ {a b : V} (p : G.Walk a b), (∀ x ∈ p.support, x ∈ S) → ∀ (ha : a ∈ S) (hb : b ∈ S),
      ∃ q : (G.induce S).Walk ⟨a, ha⟩ ⟨b, hb⟩, q.length = p.length := by
  intro a b p
  induction p with
  | nil =>
    intro _ ha hb
    exact ⟨Walk.nil, rfl⟩
  | @cons a c b h p ih =>
    intro hp ha hb
    have hc : c ∈ S := hp c (by simp)
    obtain ⟨q, hq⟩ := ih (fun x hx => hp x (by simp [hx])) hc hb
    refine ⟨Walk.cons (show (G.induce S).Adj ⟨a, ha⟩ ⟨c, hc⟩ from h) q, ?_⟩
    simp [hq]

theorem erdos_640.variants.three (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : (3 : ℕ∞) ≤ G.chromaticNumber) : HasHighChromaticOddCycle G 3 := by
  have h2 : ¬ G.Colorable 2 := by
    intro hc
    have := hG.trans hc.chromaticNumber_le
    norm_num at this
  rw [two_colorable_iff_forall_loop_even] at h2
  push Not at h2
  obtain ⟨u, w, hw⟩ := h2
  rw [Nat.not_even_iff_odd] at hw
  obtain ⟨v, c, hc, hodd⟩ := exists_odd_cycle G _ w rfl hw
  refine ⟨v, c, hc, hodd, ?_⟩
  obtain ⟨q, hq⟩ := lift G {x | x ∈ c.support} c (fun x hx => hx)
    c.start_mem_support c.start_mem_support
  exact q.three_le_chromaticNumber_of_odd_loop (hq ▸ hodd)

end Erdos640

#print axioms Erdos640.erdos_640.variants.three
