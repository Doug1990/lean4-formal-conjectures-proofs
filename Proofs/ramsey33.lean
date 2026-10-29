import Mathlib

open SimpleGraph
open scoped Classical

namespace R33

/-- classical Ramsey number definition (copied from the checkout, same shape) -/
noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }

noncomputable def classicalRamsey (k l : ℕ) : ℕ :=
  graphRamsey (completeGraph (Fin k)) (completeGraph (Fin l))

def mono (x y z : Bool) : Bool := (x == y) && (y == z)

set_option maxRecDepth 100000 in
theorem key : ∀ b01 b02 b03 b04 b05 b12 b13 b14 b15 b23 b24 b25 b34 b35 b45 : Bool,
    (mono b01 b02 b12 || mono b01 b03 b13 || mono b01 b04 b14 || mono b01 b05 b15 ||
    mono b02 b03 b23 || mono b02 b04 b24 || mono b02 b05 b25 || mono b03 b04 b34 ||
    mono b03 b05 b35 || mono b04 b05 b45 ||
    mono b12 b13 b23 || mono b12 b14 b24 || mono b12 b15 b25 || mono b13 b14 b34 ||
    mono b13 b15 b35 || mono b14 b15 b45 ||
    mono b23 b24 b34 || mono b23 b25 b35 || mono b24 b25 b45 || mono b34 b35 b45) = true := by
  decide +kernel

theorem M {C : SimpleGraph (Fin 6)} (h1 : C.CliqueFree 3) (h2 : Cᶜ.CliqueFree 3)
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    mono (decide (C.Adj i j)) (decide (C.Adj i k)) (decide (C.Adj j k)) = false := by
  by_contra hne
  have hm : mono (decide (C.Adj i j)) (decide (C.Adj i k)) (decide (C.Adj j k)) = true := by
    simpa using hne
  simp only [mono, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨e1, e2⟩ := hm
  by_cases a : C.Adj i j
  · have b : C.Adj i k := by simpa [a] using e1.symm
    have c : C.Adj j k := by simpa [b] using e2.symm
    exact h1 _ (SimpleGraph.is3Clique_triple_iff.2 ⟨a, b, c⟩)
  · have b : ¬ C.Adj i k := by simpa [a] using e1.symm
    have c : ¬ C.Adj j k := by simpa [b] using e2.symm
    exact h2 _ (SimpleGraph.is3Clique_triple_iff.2
      ⟨(SimpleGraph.compl_adj _ _ _).2 ⟨hij, a⟩, (SimpleGraph.compl_adj _ _ _).2 ⟨hik, b⟩,
        (SimpleGraph.compl_adj _ _ _).2 ⟨hjk, c⟩⟩)

theorem six_mem : ∀ C : SimpleGraph (Fin 6),
    (completeGraph (Fin 3)).IsContained C ∨ (completeGraph (Fin 3)).IsContained Cᶜ := by
  intro C
  by_contra hcon
  rw [not_or] at hcon
  have h1 : C.CliqueFree 3 := by
    by_contra h; exact hcon.1 ((SimpleGraph.not_cliqueFree_iff_top_isContained 3).1 h)
  have h2 : Cᶜ.CliqueFree 3 := by
    by_contra h; exact hcon.2 ((SimpleGraph.not_cliqueFree_iff_top_isContained 3).1 h)
  have := key (decide (C.Adj 0 1)) (decide (C.Adj 0 2)) (decide (C.Adj 0 3))
    (decide (C.Adj 0 4)) (decide (C.Adj 0 5)) (decide (C.Adj 1 2)) (decide (C.Adj 1 3))
    (decide (C.Adj 1 4)) (decide (C.Adj 1 5)) (decide (C.Adj 2 3)) (decide (C.Adj 2 4))
    (decide (C.Adj 2 5)) (decide (C.Adj 3 4)) (decide (C.Adj 3 5)) (decide (C.Adj 4 5))
  have m012 := M h1 h2 0 1 2 (by decide) (by decide) (by decide)
  have m013 := M h1 h2 0 1 3 (by decide) (by decide) (by decide)
  have m014 := M h1 h2 0 1 4 (by decide) (by decide) (by decide)
  have m015 := M h1 h2 0 1 5 (by decide) (by decide) (by decide)
  have m023 := M h1 h2 0 2 3 (by decide) (by decide) (by decide)
  have m024 := M h1 h2 0 2 4 (by decide) (by decide) (by decide)
  have m025 := M h1 h2 0 2 5 (by decide) (by decide) (by decide)
  have m034 := M h1 h2 0 3 4 (by decide) (by decide) (by decide)
  have m035 := M h1 h2 0 3 5 (by decide) (by decide) (by decide)
  have m045 := M h1 h2 0 4 5 (by decide) (by decide) (by decide)
  have m123 := M h1 h2 1 2 3 (by decide) (by decide) (by decide)
  have m124 := M h1 h2 1 2 4 (by decide) (by decide) (by decide)
  have m125 := M h1 h2 1 2 5 (by decide) (by decide) (by decide)
  have m134 := M h1 h2 1 3 4 (by decide) (by decide) (by decide)
  have m135 := M h1 h2 1 3 5 (by decide) (by decide) (by decide)
  have m145 := M h1 h2 1 4 5 (by decide) (by decide) (by decide)
  have m234 := M h1 h2 2 3 4 (by decide) (by decide) (by decide)
  have m235 := M h1 h2 2 3 5 (by decide) (by decide) (by decide)
  have m245 := M h1 h2 2 4 5 (by decide) (by decide) (by decide)
  have m345 := M h1 h2 3 4 5 (by decide) (by decide) (by decide)
  rw [m012, m013, m014, m015, m023, m024, m025, m034, m035, m045, m123, m124, m125, m134,
    m135, m145, m234, m235, m245, m345] at this
  simp at this

def PAdj (a b : ℕ) : Prop := (a + 1) % 5 = b ∨ (b + 1) % 5 = a

instance (a b : ℕ) : Decidable (PAdj a b) := by unfold PAdj; infer_instance

set_option synthInstance.maxSize 4096 in
theorem pent : ∀ a < 5, ∀ b < 5, ∀ c < 5,
    ¬ (PAdj a b ∧ PAdj a c ∧ PAdj b c) ∧
    ¬ (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬ PAdj a b ∧ ¬ PAdj a c ∧ ¬ PAdj b c) := by
  decide

def pentagon (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := PAdj i.val j.val
  symm := ⟨fun _ _ h => by unfold PAdj at h ⊢; exact h.symm⟩
  loopless := ⟨fun i h => by unfold PAdj at h; omega⟩

theorem pentagon_adj {n : ℕ} (a b : Fin n) : (pentagon n).Adj a b ↔ PAdj a.val b.val := Iff.rfl

theorem not_mem_of_lt (n : ℕ) (hn : n < 6) : n ∉
    { n : ℕ | ∀ (C : SimpleGraph (Fin n)),
      (completeGraph (Fin 3)).IsContained C ∨ (completeGraph (Fin 3)).IsContained Cᶜ } := by
  intro h
  have h1 : (pentagon n).CliqueFree 3 := by
    intro s hs
    rw [SimpleGraph.is3Clique_iff] at hs
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := hs
    rw [pentagon_adj] at hab hac hbc
    exact (pent a.val (by omega) b.val (by omega) c.val (by omega)).1 ⟨hab, hac, hbc⟩
  have h2 : (pentagon n)ᶜ.CliqueFree 3 := by
    intro s hs
    rw [SimpleGraph.is3Clique_iff] at hs
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := hs
    simp only [SimpleGraph.compl_adj, pentagon_adj] at hab hac hbc
    exact (pent a.val (by omega) b.val (by omega) c.val (by omega)).2
      ⟨fun e => hab.1 (Fin.ext e), fun e => hac.1 (Fin.ext e), fun e => hbc.1 (Fin.ext e),
        hab.2, hac.2, hbc.2⟩
  rcases h (pentagon n) with h | h
  · exact ((SimpleGraph.not_cliqueFree_iff_top_isContained 3).2 h) h1
  · exact ((SimpleGraph.not_cliqueFree_iff_top_isContained 3).2 h) h2

theorem ramsey_number_three_three : classicalRamsey 3 3 = 6 := by
  unfold classicalRamsey graphRamsey
  have h6 : 6 ∈ { n : ℕ | ∀ (C : SimpleGraph (Fin n)),
      (completeGraph (Fin 3)).IsContained C ∨ (completeGraph (Fin 3)).IsContained Cᶜ } :=
    six_mem
  apply le_antisymm
  · exact Nat.sInf_le h6
  · apply le_csInf ⟨6, h6⟩
    intro n hn
    by_contra hlt
    exact not_mem_of_lt n (by omega) hn

end R33

#print axioms R33.ramsey_number_three_three
