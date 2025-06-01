import Mathlib

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (𝓐 : ℤ → Submodule R A)

section DGA

class DifferentialGradedAlgebra [GradedAlgebra 𝓐] where
  deriv : Derivation R A A
  derivIsHomogeneous (n : ℤ) (m : 𝓐 n) : deriv m ∈ 𝓐 (n - 1)

end DGA

section DGM

variable [GradedAlgebra 𝓐] [DifferentialGradedAlgebra 𝓐]
  {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  (𝓜 : ℤ → Submodule R M)

class GradedModule extends SetLike.GradedSMul 𝓐 𝓜, DirectSum.Decomposition 𝓜
open DirectSum
example [GradedModule 𝓐 𝓜] : @LinearEquiv A A _ _ (RingHom.id A) (RingHom.id A) _ _ M (⨁ (i : ℤ), 𝓜 i) _
    _ _ (by letI := GradedModule.isModule 𝓐 𝓜; infer_instance) := by
  have := GradedModule.linearEquiv 𝓐 𝓜
  apply this

-- class DifferentialGradedModule where
--   deriv :


end DGM
