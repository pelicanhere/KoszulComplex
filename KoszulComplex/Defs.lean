import Mathlib
import KoszulComplex.cycleIcc

universe u v w

variable {R : Type u} [CommRing R] (L : Type v) [AddCommGroup L] [Module R L] (f : L →ₗ[R] R) (n : ℕ)

open ExteriorAlgebra ModuleCat CategoryTheory

noncomputable def exteriorPower.contraction_aux : AlternatingMap R L (⋀[R]^n L) (Fin (n + 1)) where
  toFun x := ∑ᶠ i : Fin (n + 1),
    ((- 1 : R) ^ i.1 * (f (x i))) • exteriorPower.ιMulti R n (x.comp (Fin.succAbove i))
  map_update_add' m i x y := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← Finset.sum_add_distrib]
    congr
    funext w
    rw [mul_smul, mul_smul, mul_smul, ← smul_add]
    congr
    by_cases hw : w = i
    · rw [hw, Function.update_self, Function.update_self,
        Function.update_self, map_add, add_smul]
      congr <;> (funext k ; rw [Function.comp_apply, Function.comp_apply,
        Function.update_of_ne (Fin.succAbove_ne i k),
        Function.update_of_ne (Fin.succAbove_ne i k)])
    · rw [Function.update_of_ne hw, Function.update_of_ne hw,
        Function.update_of_ne hw, ← smul_add]
      congr
      obtain ⟨j, hj⟩ : ∃ j : Fin n, w.succAbove j = i :=
        Fin.exists_succAbove_eq (show w ≠ i by exact hw).symm
      have := hj ▸ (Function.update_comp_eq_of_injective m
        (Fin.succAbove_right_injective (p := w)) j)
      rw [this _, this _, this _, AlternatingMap.map_update_add]
  map_update_smul' m i r x := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.smul_sum]
    congr
    funext j
    by_cases jeqi : j = i
    · rw [jeqi, Function.update_self, Function.update_self, map_smul,
        smul_eq_mul, ← smul_assoc, smul_eq_mul, ← mul_assoc, ← mul_assoc,
        mul_comm _ r]
      congr
      funext k
      simp only [Function.comp_apply, ne_eq, Fin.succAbove_ne i k, not_false_eq_true, Function.update_of_ne]
    · simp only [ne_eq, jeqi, not_false_eq_true, Function.update_of_ne, SetLike.val_smul, exteriorPower.ιMulti_apply_coe]
      rw [smul_comm]
      congr
      obtain ⟨l, hl⟩ : ∃ l : Fin n, j.succAbove l = i :=
        Fin.exists_succAbove_eq (show j ≠ i by exact jeqi).symm
      have := hl ▸ (Function.update_comp_eq_of_injective m
        (Fin.succAbove_right_injective (p := j)) l)
      rw [this _, this _, AlternatingMap.map_update_smul]
  map_eq_zero_of_eq' x i j eq neq := by sorry

lemma step (x : Fin (n + 1) → L) (i j : Fin (n + 1)) (eq : x i = x j) (neq : i ≠ j) :
    ∑ᶠ (i : Fin (n + 1)), ((-1) ^ i.1 * f (x i)) • (ιMulti R n) (x ∘ i.succAbove) = 0 := by
  wlog le : i ≤ j
  · simp [neq] at le
    exact this L f n x j i eq.symm neq.symm (Fin.le_of_lt le)

  #check cycleIcc
  #check AlternatingMap.map_perm

  have : i.succAbove = j.succAbove ∘ sorry := by
    sorry
  have : ((-1) ^ i.1 * f (x i)) • (ιMulti R n) (x ∘ i.succAbove)
       + ((-1) ^ j.1 * f (x j)) • (ιMulti R n) (x ∘ j.succAbove) = 0 := by

    sorry
  sorry


noncomputable def ModuleCat.exteriorPower.contraction :
    (of R L).exteriorPower (n + 1) ⟶ (of R L).exteriorPower n :=
  desc (exteriorPower.contraction_aux L f n)

#check AlgebraicTopology.AlternatingFaceMapComplex.d_squared
#check map_sum

noncomputable def koszulComplex :
    HomologicalComplex (ModuleCat.{max u v} R) (ComplexShape.down ℕ) := by
  refine ChainComplex.of (of R L).exteriorPower (ModuleCat.exteriorPower.contraction L f) (fun n ↦ ?_)
  ext x
  simp only [ModuleCat.AlternatingMap.postcomp_apply, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  unfold ModuleCat.exteriorPower.contraction-- ModuleCat.exteriorPower.contraction_aux
  simp only [ModuleCat.exteriorPower.desc_mk]
  /- rw [iaob]
  -- need map_finsum
  have : (ModuleCat.Hom.hom (ModuleCat.exteriorPower.desc (ModuleCat.exteriorPower.contraction_aux L f n)))
    (∑ᶠ (i : Fin (n + 1 + 1)), ((-1 : R) ^ i.1 * f (x i)) • (exteriorPower.ιMulti R (n + 1)) (x ∘ i.succAbove)) =
    ∑ᶠ (i : Fin (n + 1 + 1)), (ModuleCat.Hom.hom (ModuleCat.exteriorPower.desc (ModuleCat.exteriorPower.contraction_aux L f n))) (((-1 : R) ^ i.1 * f (x i)) • (exteriorPower.ιMulti R (n + 1)) (x ∘ i.succAbove))
    --∑ᶠ (i : Fin (n + 1 + 1)), ((-1 : R) ^ i.1 * f (x i)) • ((ModuleCat.Hom.hom (ModuleCat.exteriorPower.desc (ModuleCat.exteriorPower.contraction_aux L f n))) ((exteriorPower.ιMulti R (n + 1)) (x ∘ i.succAbove)))
     := by
    sorry -/
  sorry

/-- The Koszul homology $H_n(f)$. -/
noncomputable def koszulHomology : ModuleCat R := (koszulComplex L f).homology n

namespace RingTheory.Sequence

variable (rs : List R)

/-- Let $\mathbf{x} = (x_1, \dots, x_n)$ be a sequence in $R$, consider
  $f_{\mathbf{x}} : R^n \to R, e_i \mapsto x_i$. The Koszul complex $K_{\bullet}(\mathbf{x})$
  is defined as $K_{\bullet}(\mathbf{x}) := K_{\bullet}(f_{\mathbf{x}})$. -/
noncomputable def koszulComplex : HomologicalComplex (ModuleCat R) (ComplexShape.down ℕ) :=
  _root_.koszulComplex (Fin rs.length →₀ R) <|
    Finsupp.linearCombination R (fun (i : Fin rs.length) ↦ rs.get i)

end RingTheory.Sequence

section twisted

--set_option pp.universes true
variable {R : Type u} [CommRing R] (M : ModuleCat.{w} R)

noncomputable def ModuleCat.tensorRight : (ModuleCat.{v} R) ⥤ (ModuleCat.{max v w} R) where
  obj N := ModuleCat.MonoidalCategory.tensorObj N M
  map N := ModuleCat.MonoidalCategory.whiskerRight N M
  map_id _ := ModuleCat.hom_ext (TensorProduct.ext rfl)
  map_comp _ _ := ModuleCat.hom_ext (TensorProduct.ext rfl)

instance : (ModuleCat.tensorRight M).Additive where
  map_add := by
    refine ModuleCat.hom_ext (TensorProduct.ext ?_)
    simp only [tensorRight, ModuleCat.MonoidalCategory.whiskerRight, hom_add, LinearMap.rTensor_add]
    rfl

variable {R : Type u} [CommRing R] (L : Type v) [AddCommGroup L] [Module R L] (f : L →ₗ[R] R)
  (M : ModuleCat.{w} R) (n : ℕ)

/-- The Koszul complex with coefficients in $M$ is defined as
  $K_{\bullet}(f, M) := K_{\bullet}(f)⊗M$. -/
noncomputable def twistedKoszulComplex :
    HomologicalComplex (ModuleCat.{max u v w} R) (ComplexShape.down ℕ) :=
  ((ModuleCat.tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj (koszulComplex L f)

/-- The Koszul homology with coefficients in $M$ is defined as
  $H_n(f, M) := H_n(K_{\bullet}(f, M))$. -/
noncomputable def twistedKoszulHomology : ModuleCat.{max u v w} R :=
  (twistedKoszulComplex L f M).homology n

end twisted
