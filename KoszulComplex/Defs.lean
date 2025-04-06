import Mathlib

variable {R : Type*} [CommRing R] (L : ModuleCat R) (f : L →ₗ[R] R) (n : ℕ)

open ExteriorAlgebra

noncomputable def ModuleCat.exteriorPower.contraction_aux :
    L.AlternatingMap (L.exteriorPower n) (n + 1) where
  toFun x := ∑ᶠ i : Fin (n + 1),
    ((- 1 : R) ^ i.1 * (f (x i))) • exteriorPower.ιMulti R n (x.comp (Fin.succAbove i))
  map_update_add' := sorry
  map_update_smul' := sorry
  map_eq_zero_of_eq' := sorry

noncomputable def ModuleCat.exteriorPower.contraction : L.exteriorPower (n + 1) ⟶ L.exteriorPower n :=
  desc (contraction_aux L f n)

noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ := by
  refine ChainComplex.of L.exteriorPower (ModuleCat.exteriorPower.contraction L f) (fun n ↦ ?_)
  sorry
