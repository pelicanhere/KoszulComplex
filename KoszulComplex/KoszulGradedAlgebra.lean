import Mathlib
import KoszulComplex.DGA


section koszulDF

open DirectSum ExteriorAlgebra

variable {R : Type u} [CommRing R] {L : Type v} [AddCommGroup L] [Module R L]

variable (R) (L) in
def exteriorIntGrading : ℤ → Submodule R (ExteriorAlgebra R L) := fun i =>
  match i with
  | Int.ofNat i => ⋀[R]^i L
  | Int.negSucc _ => 0

instance : GradedAlgebra (fun i : ℕ ↦ ⋀[R]^i L) := ExteriorAlgebra.gradedAlgebra R L

instance : SetLike.GradedMonoid (exteriorIntGrading R L) where
  one_mem := by simp [exteriorIntGrading]
  mul_mem := by
    unfold exteriorIntGrading
    intro i j gi gj hgi hgj
    cases i with
    | ofNat i =>
      cases j with
      | ofNat j =>
        simp only at hgi hgj
        exact SetLike.mul_mem_graded hgi hgj
      | negSucc j => simp_all
    | negSucc i => simp_all

instance : GradedAlgebra (exteriorIntGrading R L) := by
  apply GradedAlgebra.ofAlgHom _ ?_ ?_ ?_
  . apply AlgHom.comp ?_ (GradedAlgebra.liftι R L)
    refine DirectSum.toAlgebra _ _ (fun i => ?_) ?_ ?_
    . exact (DirectSum.lof R ℤ (fun i => (exteriorIntGrading R L i)) i).comp <|
        Submodule.inclusion (by rfl)
    . simp only [Int.ofNat_eq_coe, Int.cast_ofNat_Int, LinearMap.coe_comp, Function.comp_apply]
      rfl
    . intro i j ai aj



      sorry

  . ext t
    simp
    sorry
  .
    sorry





end koszulDF
