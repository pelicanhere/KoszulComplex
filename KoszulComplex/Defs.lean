import Mathlib

variable {R : Type*} [CommRing R] (M : ModuleCat R) (f : M →ₗ[R] R) (n : ℕ)

open ExteriorAlgebra

noncomputable def ModuleCat.exteriorPower.contraction_aux :
    M.AlternatingMap (M.exteriorPower n) (n + 1) where
  toFun x := ∑ᶠ i : Fin (n + 1),
    ((- 1 : R) ^ i.1 * (f (x i))) • exteriorPower.ιMulti R n (x.comp (Fin.succAbove i))
  map_update_add' := sorry
  map_update_smul' := sorry
  map_eq_zero_of_eq' := sorry

noncomputable def ModuleCat.exteriorPower.contraction : M.exteriorPower (n + 1) ⟶ M.exteriorPower n :=
  desc (contraction_aux M f n)

noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ := by
  refine ChainComplex.of M.exteriorPower (fun n ↦ ?_) (fun n ↦ ?_)
  · apply ModuleCat.exteriorPower.desc
    sorry
  · sorry
