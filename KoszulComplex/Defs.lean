import Mathlib

variable {R : Type*} [CommRing R] (L : ModuleCat R) (f : L →ₗ[R] R) (M : ModuleCat R) (n : ℕ)

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

#check AlgebraicTopology.AlternatingFaceMapComplex.d_squared
#check map_sum

noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ := by
  refine ChainComplex.of L.exteriorPower (ModuleCat.exteriorPower.contraction L f) (fun n ↦ ?_)
  ext x
  simp only [ModuleCat.AlternatingMap.postcomp_apply, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  unfold ModuleCat.exteriorPower.contraction-- ModuleCat.exteriorPower.contraction_aux
  simp only [ModuleCat.exteriorPower.desc_mk]
  rw [iaob]
  -- need map_finsum
  have : (ModuleCat.Hom.hom (ModuleCat.exteriorPower.desc (ModuleCat.exteriorPower.contraction_aux L f n)))
    (∑ᶠ (i : Fin (n + 1 + 1)), ((-1 : R) ^ i.1 * f (x i)) • (exteriorPower.ιMulti R (n + 1)) (x ∘ i.succAbove)) =
    ∑ᶠ (i : Fin (n + 1 + 1)), (ModuleCat.Hom.hom (ModuleCat.exteriorPower.desc (ModuleCat.exteriorPower.contraction_aux L f n))) (((-1 : R) ^ i.1 * f (x i)) • (exteriorPower.ιMulti R (n + 1)) (x ∘ i.succAbove))
    --∑ᶠ (i : Fin (n + 1 + 1)), ((-1 : R) ^ i.1 * f (x i)) • ((ModuleCat.Hom.hom (ModuleCat.exteriorPower.desc (ModuleCat.exteriorPower.contraction_aux L f n))) ((exteriorPower.ιMulti R (n + 1)) (x ∘ i.succAbove)))
     := by
    sorry
  sorry

/-- The Koszul homology $H_n(f)$. -/
noncomputable def koszulHomology : ModuleCat R := (koszulComplex L f).homology n

/-- The Koszul complex with coefficients in $M$ is defined as $K_{\bullet}(f) := K_{\bullet}(f)⊗M$. -/
noncomputable def twistedKoszulComplex : ChainComplex (ModuleCat R) ℕ :=
  ((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (koszulComplex L f)

/-- The Koszul homology with coefficients in $M$ is defined as $H_n(f, M)$. -/
noncomputable def twistedKoszulHomology : ModuleCat R := (twistedKoszulComplex L f M).homology n
