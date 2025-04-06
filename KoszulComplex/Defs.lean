import Mathlib

variable {R : Type*} [CommRing R] (M : ModuleCat R) (f : M →ₗ[R] R)

open ExteriorAlgebra

def koszulComplex : ChainComplex (ModuleCat R) ℕ := by
  refine ChainComplex.of M.exteriorPower (fun n ↦ ?_) (fun n ↦ ?_)
  · sorry
  · sorry
