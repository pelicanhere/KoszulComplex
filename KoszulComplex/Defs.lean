import Mathlib
import KoszulComplex.cycleIcc

universe u v w

lemma Z_simp (R : Type u) [Ring R] {L : Type v} [AddCommGroup L] [Module R L]
  (k : ℕ) (x : L): (-1 : ℤˣ) ^ k • x = ((-1 : R) ^ k) • x := by
  rcases Nat.even_or_odd k with ch | ch
  · simp [ch]
  · simp [ch]

lemma lt_ne {n : ℕ}{i j : Fin (n + 1)} (hij : i < j) : NeZero n := by
  by_contra ne
  have : n = 0 := not_neZero.mp ne
  omega

variable {R : Type u} [CommRing R] (L : Type v) [AddCommGroup L] [Module R L] (f : L →ₗ[R] R)
  (n : ℕ)

open ExteriorAlgebra ModuleCat CategoryTheory Fin Function

omit [AddCommGroup L] in
theorem succAbove_comp_cycleIcc [NeZero n] (x : Fin (n + 1) → L) (i j : Fin (n + 1))
    (eq : x i = x j) (ilt : i.1 < n) (jlt : (j - 1).1 < n) (lt : i < j) (hij : castLT i ilt ≤
    castLT (j - 1) jlt) : x ∘ i.succAbove = x ∘ j.succAbove ∘ (cycleIcc hij) := by
  ext k
  simp [succAbove]
  by_cases ch : k.castSucc < i
  · simp [cycleIcc_of_gt hij ch, ch, lt_trans ch lt]
  simp [ch]
  by_cases ch1 : (j - 1).castLT jlt < k
  · have : ¬ k.castSucc < j := by
      simp [not_lt, lt_def, val_sub_one_of_ne_zero (ne_zero_of_lt lt)] at ch1 ⊢; omega
    simp [cycleIcc_of_le hij ch1, this]
  simp at ch ch1
  by_cases ch2 : k < (j - 1).castLT jlt
  · have : (k + 1).castSucc < j := by
      rw [lt_def, coe_castSucc, val_add_one_of_lt' ch2]
      simp [lt_def, val_sub_one_of_ne_zero (ne_zero_of_lt lt)] at ch2
      omega
    simp [cycleIcc_of_lt hij ch ch2, this]; congr
    exact eq_of_val_eq (by simp [val_add_one_of_lt' ch2])
  simp at ch2
  have : (cycleIcc hij) k = i.castLT ilt := by rw [← le_antisymm ch2 ch1, cycleIcc_of_eq hij]
  simp [this, lt, eq]; congr; exact eq_of_val_eq
    (by simp [← le_antisymm ch2 ch1, val_sub_one_of_ne_zero (ne_zero_of_lt lt)]; omega)

lemma step1 [NeZero n] {x : Fin (n + 1) → L} {i j : Fin (n + 1)} (eq : x i = x j) (lt : i < j) :
    ((-1) ^ i.1 * f (x i)) • (exteriorPower.ιMulti R n) (x ∘ i.succAbove)
    + ((-1) ^ j.1 * f (x j)) • (exteriorPower.ιMulti R n) (x ∘ j.succAbove) = 0 := by
  have ilt : i.1 < n := by omega
  have jlt : (j - 1).1 < n := by rw [val_sub_one_of_ne_zero (ne_zero_of_lt lt)]; omega
  have hij : castLT i ilt ≤ castLT (j - 1) jlt := by
    simp [le_def, val_sub_one_of_ne_zero (ne_zero_of_lt lt)]; omega
  rw [succAbove_comp_cycleIcc L n x i j eq ilt jlt lt hij]
  show ((-1) ^ i.1 * f (x i)) • ((exteriorPower.ιMulti R n) ((x ∘ j.succAbove) ∘ ⇑(cycleIcc hij)))
      + ((-1) ^ j.1 * f (x j)) • (exteriorPower.ιMulti R n) (x ∘ j.succAbove) = 0
  simp only [eq,
    AlternatingMap.map_perm (exteriorPower.ιMulti R n) (x ∘ j.succAbove) (cycleIcc hij),
    sign_cycleIcc, coe_castLT,
    Z_simp R ((j - 1).1 - i.1) ((exteriorPower.ιMulti R n) (x ∘ j.succAbove))]
  have : (-1 : R) ^ i.1 * (-1 : R) ^ ((j - 1).1 - i.1) + (-1) ^ j.1 = 0 := by
    have : i.1 + (j.1 - 1 - i.1) = j.1 - 1 := by omega
    have part: (-1 : R) ^ (j.1 - 1) * (-1) ^ 1 = (-1 : R) ^ (j.1) := by
      rw [← (pow_add (-1) (↑j - 1) 1)]; congr; omega
    simp at part
    rw [val_sub_one_of_ne_zero (ne_zero_of_lt lt), ← npow_add, this, ← part, add_neg_cancel]
  rw [← mul_smul, ← add_smul, mul_assoc]; nth_rw 2 [mul_comm]
  rw [← mul_assoc, ← add_mul, this, zero_mul, zero_smul]

lemma step2 {x : Fin (n + 1) → L} {i j k : Fin (n + 1)} (eq : x i = x j) (neq : i ≠ j) (hk : k ≠ i ∧
    k ≠ j): ((-1) ^ k.1 * f (x k)) • (exteriorPower.ιMulti R n) (x ∘ k.succAbove) = 0 := by
  have i_in : i ∈ Set.range k.succAbove := by
    simp [Fin.range_succAbove k, Set.mem_compl_singleton_iff, hk.1.symm]
  have j_in : j ∈ Set.range k.succAbove := by
    simp [Fin.range_succAbove k, Set.mem_compl_singleton_iff, hk.2.symm]
  have neq : (Set.rangeSplitting k.succAbove ⟨i, i_in⟩) ≠
             (Set.rangeSplitting k.succAbove ⟨j, j_in⟩) := fun eq ↦ by
    have eq: k.succAbove (Set.rangeSplitting k.succAbove ⟨i, i_in⟩)
           = k.succAbove (Set.rangeSplitting k.succAbove ⟨j, j_in⟩) := by rw [eq]
    simp [Set.apply_rangeSplitting k.succAbove] at eq
    exact neq eq
  rw [AlternatingMap.map_eq_zero_of_eq (exteriorPower.ιMulti R n) (x ∘ k.succAbove) ?_ neq]
  simp
  simp [Set.apply_rangeSplitting k.succAbove, eq]

lemma sum_of_two {s : Fin n → L}{i j : Fin n} (neq : i ≠ j)(eq0 : ∀ k, k ≠ i ∧ k ≠ j → s k = 0)
    (sum0 : s i + s j = 0) : finsum s = 0 := by
  by_cases ch : s i = 0
  · refine finsum_eq_zero_of_forall_eq_zero fun k ↦ ?_
    by_cases ch2 : k ≠ i ∧ k ≠ j
    · exact eq0 k ch2
    · rcases Decidable.or_iff_not_not_and_not.mpr ch2 with ch3 | ch3
      · rw [ch3, ch]
      · simpa [ch3, ch] using sum0
  · have : s.support = {i, j} := by
      refine support_eq_iff.mpr ?_
      constructor
      · intro x hx
        rcases hx with ch3 | ch3
        · simp [ch3, ch]
        · rwa [ch3, ← neg_eq_of_add_eq_zero_right sum0, ne_eq, neg_eq_zero]
      · exact fun x hx ↦ eq0 x (not_or.mp hx)
    rw [← finsum_mem_support s, this, finsum_mem_pair neq, sum0]

noncomputable def exteriorPower.contraction_aux : AlternatingMap R L (⋀[R]^n L) (Fin (n + 1)) where
  toFun x := ∑ᶠ i : Fin (n + 1),
    ((- 1 : R) ^ i.1 * (f (x i))) • exteriorPower.ιMulti R n (x.comp i.succAbove)
  map_update_add' m i x y := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← Finset.sum_add_distrib]
    congr
    funext w
    rw [mul_smul, mul_smul, mul_smul, ← smul_add]
    congr
    by_cases hw : w = i
    · rw [hw, update_self, update_self, update_self, map_add, add_smul]
      congr <;> (funext k ; rw [comp_apply, comp_apply, update_of_ne (i.succAbove_ne k),
        update_of_ne (i.succAbove_ne k)])
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
    · simp only [ne_eq, jeqi, not_false_eq_true, update_of_ne]
      rw [smul_comm]
      congr
      obtain ⟨l, hl⟩ : ∃ l : Fin n, j.succAbove l = i :=
        exists_succAbove_eq (show j ≠ i by exact jeqi).symm
      have := hl ▸ (update_comp_eq_of_injective m (succAbove_right_injective (p := j)) l)
      rw [this _, this _, AlternatingMap.map_update_smul]
  map_eq_zero_of_eq' x i j eq neq := by
    wlog le : i ≤ j
    · simp [neq] at le
      exact this L f n x j i eq.symm neq.symm (le_of_lt le)
    have hij : i < j := lt_of_le_of_ne le neq
    have : NeZero n := lt_ne hij
    exact sum_of_two (↥(⋀[R]^n L)) (n + 1) neq (fun k ↦ step2 L f n eq neq) (step1 L f n eq hij)

noncomputable def ModuleCat.exteriorPower.contraction :
    (of R L).exteriorPower (n + 1) ⟶ (of R L).exteriorPower n :=
  desc (exteriorPower.contraction_aux L f n)

#check AlgebraicTopology.AlternatingFaceMapComplex.d_squared
#check map_sum

noncomputable def koszulComplex :
    HomologicalComplex (ModuleCat.{max u v} R) (ComplexShape.down ℕ) := by
  refine ChainComplex.of (of R L).exteriorPower (ModuleCat.exteriorPower.contraction L f) (fun n ↦ ?_)
  ext x
  dsimp at x
  simp only [ModuleCat.AlternatingMap.postcomp_apply, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  unfold ModuleCat.exteriorPower.contraction-- ModuleCat.exteriorPower.contraction_aux
  simp only [ModuleCat.exteriorPower.desc_mk]
  simp only [exteriorPower.desc, hom_ofHom]
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
