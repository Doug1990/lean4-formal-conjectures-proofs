import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Jacobson.Ideal

open Ring

universe u

namespace Jacobson

/-- Restated from FormalConjectures/Wikipedia/Jacobson.lean -/
def JacobsonConjectureFor (R : Type u) [Ring R] : Prop :=
  ⨅ n : ℕ, jacobson R ^ n = 0

theorem jacobson_conjecture_of_comm_ring (R : Type u) [CommRing R] [IsNoetherianRing R] :
    JacobsonConjectureFor R := by
  have h := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (R := R) (M := R) (I := Ring.jacobson R)
    Ideal.jacobson_bot.ge
  simp only [smul_eq_mul, Ideal.mul_top] at h
  rw [JacobsonConjectureFor, Submodule.zero_eq_bot]
  exact h

end Jacobson

#print axioms Jacobson.jacobson_conjecture_of_comm_ring
