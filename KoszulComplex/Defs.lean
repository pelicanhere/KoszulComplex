import Mathlib

variable {R : Type*} [CommRing R] (M : ModuleCat R) (f : M →ₗ[R] R) (n : ℕ)

open ExteriorAlgebra

noncomputable def ModuleCat.exteriorPower.contraction_aux :
    M.AlternatingMap (M.exteriorPower n) (n + 1) where
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
      rw [← Subtype.val_inj, AddMemClass.coe_add, exteriorPower.ιMulti_apply_coe]
      obtain ⟨j, hj⟩ : ∃ j : Fin n, w.succAbove j = i :=
        Fin.exists_succAbove_eq (show w ≠ i by exact hw).symm
      have := hj ▸ (Function.update_comp_eq_of_injective m
        (Fin.succAbove_right_injective (p := w)) j)
      rw [this _, this _, this _]
      exact AlternatingMap.map_update_add (ιMulti R n) (m ∘ w.succAbove) j x y
  map_update_smul' := sorry
  map_eq_zero_of_eq' := sorry

noncomputable def ModuleCat.exteriorPower.contraction : M.exteriorPower (n + 1) ⟶ M.exteriorPower n :=
  desc (contraction_aux M f n)

noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ := by
  refine ChainComplex.of M.exteriorPower (fun n ↦ ?_) (fun n ↦ ?_)
  · apply ModuleCat.exteriorPower.desc
    sorry
  · sorry
