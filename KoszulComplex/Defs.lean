import Mathlib
import KoszulComplex.cycleIcc

universe w v u

lemma Z_simp (R : Type u) [Ring R] {L : Type v} [AddCommGroup L] [Module R L]
  (k : ℕ) (x : L): (-1 : ℤˣ) ^ k • x = ((-1 : R) ^ k) • x := by
  rcases Nat.even_or_odd k with ch | ch <;>
    simp only [ch, Even.neg_pow, one_pow, one_smul, ch, Odd.neg_one_pow, Units.neg_smul,
    neg_smul]

lemma lt_ne {n : ℕ}{i j : Fin (n + 1)} (hij : i < j) : NeZero n := by
  by_contra ne
  have : n = 0 := not_neZero.mp ne
  omega

variable {R : Type u} [CommRing R] {L : Type v} [AddCommGroup L] [Module R L] (f : L →ₗ[R] R)
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
  rw [succAbove_comp_cycleIcc n x i j eq ilt jlt lt hij]
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

lemma step2 {x : Fin (n + 1) → L} {i j : Fin (n + 1)} (eq : x i = x j) (neq : i ≠ j) :
    ∀ (k : Fin (n + 1)), k ≠ i ∧ k ≠ j → ((-1) ^ k.1 * f (x k)) • (exteriorPower.ιMulti R n)
    (x ∘ k.succAbove) = 0 := fun k hk ↦ by
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
      exact this f n x j i eq.symm neq.symm (le_of_lt le)
    have hij : i < j := lt_of_le_of_ne le neq
    have : NeZero n := lt_ne hij
    rw [finsum_eq_sum_of_fintype, Fintype.sum_eq_add i j neq (step2 f n eq neq), step1 f n eq hij]

noncomputable def ModuleCat.exteriorPower.contraction :
    (of R L).exteriorPower (n + 1) ⟶ (of R L).exteriorPower n :=
  desc (exteriorPower.contraction_aux f n)

lemma aux1 {m} {j : Fin (m + 1 + 1)} {i : Fin (m + 1)} (hij : j.1 ≤ i.1) :
  i.succ.succAbove ∘ (⟨j, Nat.lt_of_le_of_lt hij i.isLt⟩ : Fin (m + 1)).succAbove =
    j.succAbove ∘ i.succAbove := by
  ext k
  simp only [Function.comp_apply, succAbove, castSucc_lt_succ_iff]
  split_ifs <;> try omega
  all_goals (expose_names; try simp[h, h_1, h_2, h_3, hij]; try contradiction)
  · have : k.1 + 1 < j.1 := h_3
    have : i.1 ≤ k.1 := not_lt.1 h_2; omega
  · have : k.1 < i.1 := Nat.lt_of_lt_of_le h hij
    have : i.1 ≤ k.1 := not_lt.1 h_2; omega
  · have : k.1 < i.1 := Nat.lt_of_lt_of_le h hij
    have : i.1 ≤ k.1 := not_lt.1 h_2; omega
  · have : j.1 ≤ k.1 := not_lt.1 h
    have : k.1 + 1 < j.1 := h_3; omega

lemma aux2 {m} {j : Fin (m + 1 + 1)} {i : Fin (m + 1)} (hij : j.1 ≤ i.1) :
  j.succAbove i = i.succ := by
    simp only [succAbove, ite_eq_right_iff]
    exact fun (h : i.1 < j.1) ↦ False.elim <| (Nat.not_lt.2 hij) h

noncomputable def koszulComplex :
    HomologicalComplex (ModuleCat.{max u v} R) (ComplexShape.down ℕ) := by
  refine ChainComplex.of (of R L).exteriorPower
    (ModuleCat.exteriorPower.contraction f) (fun m ↦ ?_)
  ext g
  simp only [ModuleCat.AlternatingMap.postcomp_apply, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
    ModuleCat.exteriorPower.contraction]
  simp_rw [ModuleCat.exteriorPower.desc_mk, exteriorPower.desc, hom_ofHom]
  convert_to
    (exteriorPower.alternatingMapLinearEquiv (exteriorPower.contraction_aux f m))
    (∑ᶠ (i : Fin (m + 1 + 1)), ((-1) ^ ↑i * f (g i)) • (exteriorPower.ιMulti R (m + 1))
      (g ∘ i.succAbove)) = 0
  simp only [finsum_eq_sum_of_fintype, map_sum, map_smul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  show ∑ j, ((-1) ^ ↑j * f (g j)) • (∑ᶠ i : Fin (m + 1),
    ((- 1 : R) ^ i.1 * (f ((g ∘ j.succAbove) i))) • exteriorPower.ιMulti R m
      ((g ∘ j.succAbove).comp i.succAbove)) = 0
  simp only [Function.comp_apply, finsum_eq_sum_of_fintype]
  conv => enter [1, 2, j, 2, 2, i, 2, 2]; rw [comp_assoc]
  conv => enter [1, 2, j]; rw [Finset.smul_sum]
  conv =>
    enter [1, 2, j, 2, i]
    rw [← smul_assoc, smul_eq_mul, ← mul_assoc, mul_comm _ ((- 1) ^ i.1),
      ← mul_assoc, ← pow_add, mul_assoc]
  set h₀ : Fin (m + 1 + 1) × Fin (m + 1) → ↥(⋀[R]^m L) := fun α ↦
    ((-1) ^ (α.2.1 + α.1.1) * (f (g α.1) * f (g (α.1.succAbove α.2)))) •
        (exteriorPower.ιMulti R m) (g ∘ α.1.succAbove ∘ α.2.succAbove)
  show ∑ j : Fin (m + 1 + 1), ∑ i : Fin (m + 1), h₀ (j, i) = 0
  have eq_ij {j : Fin (m + 1 + 1)} {i : Fin (m + 1)} (hij : j.1 ≤ i.1) :
      h₀ (j, i) = - h₀ (i.succ, (⟨j, Nat.lt_of_le_of_lt hij i.isLt⟩ : Fin (m + 1))) := by
    simp only [h₀, val_succ]
    have : i.succ.succAbove ⟨j, Nat.lt_of_le_of_lt hij i.isLt⟩ = j := by
      simp only [succAbove, castSucc_mk, Fin.eta, succ_mk, ite_eq_left_iff, not_lt]
      exact fun (h : i.1 + 1 ≤ j.1) ↦ False.elim <| (Nat.not_le_of_lt h) hij
    rw [aux1 hij, aux2 hij, this, mul_comm (f (g j)), ← add_assoc,
      pow_add _ (j.1 + i.1), pow_one, mul_comm _ (- 1), mul_assoc,
      mul_smul (- 1), neg_smul, neg_neg, one_smul, add_comm]
  set left_down := {(j, i) : Fin (m + 1 + 1) × Fin (m + 1) | j.1 ≤ i.1}
  set t : left_down → Set (Fin (m + 1 + 1) × Fin (m + 1)) :=
    fun α ↦ {α.1, (α.1.2.succ, ⟨α.1.1, Nat.lt_of_le_of_lt α.2 α.1.2.isLt⟩)}
  have pair : Pairwise (Disjoint on t) := by
    intro x y hxy
    simp only [Set.disjoint_insert_right, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
      Set.disjoint_singleton_right, Prod.mk.injEq, succ_inj, mk.injEq, not_and, t]
    split_ands
    · exact Subtype.coe_ne_coe.2 hxy.symm
    · intro h
      have y_prop := y.2
      dsimp only [Set.mem_setOf_eq, left_down] at y_prop
      rw [(Prod.ext_iff.1 h).1, (Prod.ext_iff.1 h).2] at y_prop
      exact False.elim <| (Nat.not_succ_le_self ↑(x.1).2) <| y_prop.trans x.2
    · intro h
      have x_prop := x.2
      dsimp only [Set.mem_setOf_eq, left_down] at x_prop
      rw [(Prod.ext_iff.1 h).1.symm, (Prod.ext_iff.1 h).2.symm] at x_prop
      exact False.elim <| (Nat.not_succ_le_self ↑(y.1).2) <| x_prop.trans y.2
    · intro h₁ h₂
      absurd hxy
      ext
      · exact h₂.symm
      · exact congrArg val h₁.symm
  have union : ⋃ i, t i = Set.univ := by
    ext x
    constructor
    · exact fun _ ↦ trivial
    · simp only [Set.mem_univ, Set.iUnion_coe_set, Set.mem_iUnion, Prod.exists,
        forall_const, left_down, t]
      by_cases hx' : x.1 ≤ x.2
      · use x.1, x.2,
          (by simpa only [Prod.mk.eta, Set.mem_setOf_eq, coe_eq_castSucc] using hx')
        simp only [Prod.mk.eta, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
      · simp only [coe_eq_castSucc, not_le] at hx'
        use x.2, x.1.pred (ne_of_val_ne <| Nat.ne_zero_of_lt hx')
        simp only [coe_eq_castSucc, succ_pred, coe_castSucc, Fin.eta, Prod.mk.eta,
          Set.mem_insert_iff, Set.mem_singleton_iff, or_true, Set.mem_setOf_eq, coe_pred,
          exists_prop, and_true]
        exact Nat.le_sub_one_of_lt hx'
  have := finsum_mem_iUnion pair
    (fun i ↦ by simp only [Set.finite_singleton, Set.Finite.insert, t]) (f := h₀)
  simp only [union, Set.mem_univ, finsum_true, finsum_eq_sum_of_fintype] at this
  have eq_zero : (0 : ↥(⋀[R]^m L)) = ∑ i : left_down, 0 :=
    (congrArg _ Finset.sum_const_zero).mpr rfl
  rw [(Fintype.sum_prod_type _).symm, this, eq_zero]
  apply Finset.sum_congr rfl (fun x _ ↦ ?_)
  calc
    _ = ∑ᶠ (i : Fin (m + 1 + 1) × Fin (m + 1))
      (_ : i ∈ ({↑x, ((x.1).2.succ,
        ⟨↑(x.1).1, Nat.lt_of_le_of_lt x.2 (x.1).2.isLt⟩)} :
          Set (Fin (m + 1 + 1) × Fin (m + 1))).toFinset), h₀ i := by
      simp only [← finsum_eq_sum_of_fintype, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.toFinset_insert, Set.toFinset_singleton, Finset.mem_insert,
        Finset.mem_singleton, t]
    _ = h₀ x.1 + h₀ ((x.1).2.succ, ⟨↑(x.1).1, Nat.lt_of_le_of_lt x.2 (x.1).2.isLt⟩) := by
      rw [Set.toFinset_insert, Set.toFinset_singleton, finsum_mem_finset_eq_sum h₀ _,
        Finset.sum_pair]
      intro h
      simp only [Prod.ext_iff, Set.mem_setOf_eq] at h
      have := h.2
      simp_rw [h.1, ← Fin.val_inj] at this
      simp only [val_succ, Nat.left_eq_add, one_ne_zero] at this
    _ = _ := by
      rw [eq_ij x.2, neg_add_cancel]

/-- The Koszul homology $H_n(f)$. -/
noncomputable def koszulHomology : ModuleCat R := (koszulComplex f).homology n

namespace RingTheory.Sequence

variable (rs : List R)

/-- Let $\mathbf{x} = (x_1, \dots, x_n)$ be a sequence in $R$, consider
  $f_{\mathbf{x}} : R^n \to R, e_i \mapsto x_i$. The Koszul complex $K_{\bullet}(\mathbf{x})$
  is defined as $K_{\bullet}(\mathbf{x}) := K_{\bullet}(f_{\mathbf{x}})$. -/
noncomputable def koszulComplex : HomologicalComplex (ModuleCat R) (ComplexShape.down ℕ) :=
  _root_.koszulComplex (Finsupp.linearCombination R (fun (i : Fin rs.length) ↦ rs.get i))

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
  (M : ModuleCat.{w} R) (n : ℕ) (rs : List R)

/-- The Koszul complex with coefficients in $M$ is defined as
  $K_{\bullet}(f, M) := K_{\bullet}(f)⊗M$. -/
noncomputable def twistedKoszulComplex :
    HomologicalComplex (ModuleCat.{max u v w} R) (ComplexShape.down ℕ) :=
  ((ModuleCat.tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).obj (koszulComplex f)

/-- The Koszul homology with coefficients in $M$ is defined as
  $H_n(f, M) := H_n(K_{\bullet}(f, M))$. -/
noncomputable def twistedKoszulHomology : ModuleCat.{max u v w} R :=
  (twistedKoszulComplex L f M).homology n

noncomputable def RingTheory.Sequence.twistedKoszulComplex :
    HomologicalComplex (ModuleCat R) (ComplexShape.down ℕ) :=
  _root_.twistedKoszulComplex (Fin rs.length →₀ R)
    (Finsupp.linearCombination R (fun (i : Fin rs.length) ↦ rs.get i)) M

end twisted

namespace RingTheory.Sequence

section ind

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (a : R) (rs : List R)
--(hr : IsWeaklyRegular M rs)

instance : (MonoidalCategory.curriedTensor (ModuleCat R)).Additive where
  map_add := by
    intros
    simp only [MonoidalCategory.curriedTensor, MonoidalPreadditive.add_whiskerRight]
    rfl

noncomputable def twistedKoszulComplex_iso_cons :
  (koszulComplex [a]).tensorObj (twistedKoszulComplex M rs) ≅ twistedKoszulComplex M (a :: rs) := sorry

end ind

end RingTheory.Sequence
