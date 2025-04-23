import Mathlib
import KoszulComplex.cycleIcc

universe u v w

lemma Z_simp (R : Type u) [Ring R] {L : Type v} [AddCommGroup L] [Module R L]
  (k : ℕ) (x : L): (-1 : ℤˣ) ^ k • x = ((-1 : R) ^ k) • x := by
  rcases Nat.even_or_odd k with ch | ch
  · simp [ch]
  · simp [ch]

variable {R : Type u} [CommRing R] (L : Type v) [AddCommGroup L] [Module R L] (f : L →ₗ[R] R) (n : ℕ)

open ExteriorAlgebra ModuleCat CategoryTheory Fin Function

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
    · rw [hw, update_self, update_self, update_self, map_add, add_smul]
      congr <;> (funext k ; rw [comp_apply, comp_apply, update_of_ne (Fin.succAbove_ne i k),
        update_of_ne (Fin.succAbove_ne i k)])
    · rw [update_of_ne hw, update_of_ne hw, update_of_ne hw, ← smul_add]
      congr
      obtain ⟨j, hj⟩ : ∃ j : Fin n, w.succAbove j = i :=
        exists_succAbove_eq (show w ≠ i by exact hw).symm
      have := hj ▸ (update_comp_eq_of_injective m (succAbove_right_injective (p := w)) j)
      rw [this _, this _, this _, AlternatingMap.map_update_add]
  map_update_smul' m i r x := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.smul_sum]
    congr
    funext j
    by_cases jeqi : j = i
    · rw [jeqi, update_self, update_self, map_smul, smul_eq_mul, ← smul_assoc, smul_eq_mul,
        ← mul_assoc, ← mul_assoc, mul_comm _ r]
      congr
      funext k
      simp only [comp_apply, ne_eq, succAbove_ne i k, not_false_eq_true, update_of_ne]
    · simp only [ne_eq, jeqi, not_false_eq_true, update_of_ne, SetLike.val_smul, exteriorPower.ιMulti_apply_coe]
      rw [smul_comm]
      congr
      obtain ⟨l, hl⟩ : ∃ l : Fin n, j.succAbove l = i :=
        exists_succAbove_eq (show j ≠ i by exact jeqi).symm
      have := hl ▸ (update_comp_eq_of_injective m (succAbove_right_injective (p := j)) l)
      rw [this _, this _, AlternatingMap.map_update_smul]
  map_eq_zero_of_eq' x i j eq neq := by sorry


lemma step [NeZero n] (x : Fin (n + 1) → L) (i j : Fin (n + 1)) (eq : x i = x j) (neq : i ≠ j) :
    ∑ᶠ (i : Fin (n + 1)), ((-1) ^ i.1 * f (x i)) • (ιMulti R n) (x ∘ i.succAbove) = 0 := by
  wlog le : i ≤ j
  · simp [neq] at le
    exact this L f n x j i eq.symm neq.symm (Fin.le_of_lt le)
  have lt : i < j := by omega
  have ilt : i.1 < n := by omega
  have jlt : (j - 1).1 < n := by rw [Fin.val_sub_one_of_ne_zero (Fin.ne_zero_of_lt lt)]; omega
  have hij : Fin.castLT i ilt ≤ Fin.castLT (j - 1) jlt := by
    refine Fin.le_def.mpr ?_
    simp only [coe_castLT, val_fin_le]
    rw [le_def, val_sub_one_of_ne_zero (ne_zero_of_lt lt)]
    omega
  have succAbove_comp_cycleIcc : x ∘ i.succAbove = x ∘ j.succAbove ∘ (cycleIcc hij) := by
    ext k
    simp [succAbove]
    by_cases ch : k.castSucc < i
    · simp [cycleIcc_of_gt hij ch, ch, lt_trans ch lt]
    simp [ch]
    by_cases ch1 : (j - 1).castLT jlt < k
    · have : ¬ k.castSucc < j := by
        rw [not_lt, Fin.le_def]
        simp [Fin.lt_def, Fin.val_sub_one_of_ne_zero (Fin.ne_zero_of_lt lt)] at ch1 ⊢
        omega
      simp [cycleIcc_of_le hij ch1, this]
    simp at ch ch1
    have hik: i.castLT ilt ≤ k := le_def.mpr (by simpa)
    by_cases ch2 : k < (j - 1).castLT jlt
    · have : (k + 1).castSucc < j := by
        rw [lt_def, coe_castSucc, val_add_one_of_lt' ch2]
        simp [Fin.lt_def, Fin.val_sub_one_of_ne_zero (Fin.ne_zero_of_lt lt)] at ch2
        omega
      simp [cycleIcc_of_lt hij ch ch2, this]
      congr
      refine Fin.eq_of_val_eq ?_
      simp [Fin.val_add_one_of_lt' ch2]
    simp at ch2
    have : (cycleIcc hij) k = i.castLT ilt := by rw [← Fin.le_antisymm ch2 ch1, cycleIcc_of_eq hij]
    simp [this, lt, eq]
    congr
    have : (j - 1).castLT jlt = k := Fin.le_antisymm ch2 ch1
    simp [Fin.ext_iff] at this ⊢
    rw [← this, Fin.val_sub_one_of_ne_zero (Fin.ne_zero_of_lt lt)]
    omega
  have : ((-1) ^ i.1 * f (x i)) • (ιMulti R n) (x ∘ i.succAbove)
       + ((-1) ^ j.1 * f (x j)) • (ιMulti R n) (x ∘ j.succAbove) = 0 := by
    rw [succAbove_comp_cycleIcc]
    show ((-1) ^ i.1 * f (x i)) • ((ιMulti R n) ((x ∘ j.succAbove) ∘ ⇑(cycleIcc hij)))
        + ((-1) ^ j.1 * f (x j)) • (ιMulti R n) (x ∘ j.succAbove) = 0
    simp only [eq, AlternatingMap.map_perm (ιMulti R n) (x ∘ j.succAbove) (cycleIcc hij),
      sign_cycleIcc, coe_castLT, Z_simp R ((j - 1).1 - i.1) ((ιMulti R n) (x ∘ j.succAbove))]
    have : (-1 : R) ^ i.1 * (-1 : R) ^ ((j - 1).1 - i.1) + (-1) ^ j.1 = 0 := by
      have : i.1 + (j.1 - 1 - i.1) = j.1 - 1 := by omega
      have part: (-1 : R) ^ (j.1 - 1) * (-1) ^ 1 = (-1 : R) ^ (j.1) := by
        rw [← (pow_add (-1) (↑j - 1) 1)]
        congr
        omega
      simp at part
      rw [Fin.val_sub_one_of_ne_zero (Fin.ne_zero_of_lt lt), ← npow_add, this, ← part, add_neg_cancel]
    rw [← mul_smul, ← add_smul, mul_assoc]
    nth_rw 2 [mul_comm]
    rw [← mul_assoc, ← add_mul, this, zero_mul, zero_smul]
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
