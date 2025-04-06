import Mathlib

variable {R : Type*} [CommRing R] (L : Type*) [AddCommGroup L] [Module R L] (f : L →ₗ[R] R) (n : ℕ)

open ExteriorAlgebra ModuleCat

noncomputable def exteriorPower.contraction_aux : AlternatingMap R L (⋀[R]^n L) (Fin (n + 1)) where
  toFun x := ∑ᶠ i : Fin (n + 1),
    ((- 1 : R) ^ i.1 * (f (x i))) • exteriorPower.ιMulti R n (x.comp (Fin.succAbove i))
  map_update_add' := by
    intro _ m i x y
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
      rw [this _, this _, this _]
      exact AlternatingMap.map_update_add (ιMulti R n) (m ∘ w.succAbove) j x y
  map_update_smul' := by
    intro _ m i r x
    have finsupp : (Function.support fun j ↦ ((-1 : R) ^ j.1 * f (Function.update m i x j)) • (exteriorPower.ιMulti R n) (Function.update m i x ∘ j.succAbove)).Finite := sorry
    rw [smul_finsum' r finsupp]
    congr
    ext j
    by_cases jeqi : j = i
    · rw [jeqi]
      simp only [Function.update_self, map_smul, smul_eq_mul]
      rw [← smul_assoc, smul_eq_mul, ← mul_assoc, ← mul_assoc, mul_comm _ r]
      congr
      ext k
      simp only [Function.comp_apply, ne_eq, Fin.succAbove_ne i k, not_false_eq_true, Function.update_of_ne]
    · simp only [ne_eq, jeqi, not_false_eq_true, Function.update_of_ne, SetLike.val_smul, exteriorPower.ιMulti_apply_coe]
      rw [smul_comm]
      congr
      by_cases jlast : j = Fin.last n
      · simp only [jlast, Fin.succAbove_last] at jeqi ⊢
        have ilast : i ≠ Fin.last n := fun a ↦ jeqi (id (Eq.symm a))
        have (l : L) : Function.update m i l ∘ Fin.castSucc = Function.update (m ∘ Fin.castSucc) (i.castPred ilast) l := sorry
        simp only [this (r • x), AlternatingMap.map_update_smul, this x]
      · have (l : L) : Function.update m i l ∘ j.succAbove = Function.update (m ∘ j.succAbove) (Fin.predAbove (j.castPred jlast) i) l := sorry
        simp only [this (r • x), AlternatingMap.map_update_smul, this x]
  map_eq_zero_of_eq' := sorry

noncomputable def ModuleCat.exteriorPower.contraction :
    (of R L).exteriorPower (n + 1) ⟶ (of R L).exteriorPower n :=
  desc (exteriorPower.contraction_aux L f n)

#check AlgebraicTopology.AlternatingFaceMapComplex.d_squared
#check map_sum

noncomputable def koszulComplex : HomologicalComplex (ModuleCat R) (ComplexShape.down ℕ) := by
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
  $f_{\mathbf{x}} : R^n, e_i \mapsto x_i$. The Koszul complex $K_{\bullet}(\mathbf{x})$
  is defined as $K_{\bullet}(\mathbf{x}) := K_{\bullet}(f_{\mathbf{x}})$. -/
noncomputable def koszulComplex : HomologicalComplex (ModuleCat R) (ComplexShape.down ℕ) :=
  _root_.koszulComplex (Fin rs.length →₀ R) <|
    Finsupp.linearCombination R (fun (i : Fin rs.length) ↦ rs.get i)

end RingTheory.Sequence

section twisted

universe u

variable {R : Type u} [CommRing R] (L : Type u) [AddCommGroup L] [Module R L] (f : L →ₗ[R] R)
  (M : ModuleCat.{u} R) (n : ℕ)

/-- The Koszul complex with coefficients in $M$ is defined as $K_{\bullet}(f) := K_{\bullet}(f)⊗M$. -/
noncomputable def twistedKoszulComplex : HomologicalComplex (ModuleCat R) (ComplexShape.down ℕ) :=
  ((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (koszulComplex L f)

/-- $H_n(f, M)$ is the Koszul homology with coefficients in $M$ is defined as . -/
noncomputable def twistedKoszulHomology : ModuleCat R := (twistedKoszulComplex L f M).homology n

end twisted
