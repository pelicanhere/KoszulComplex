import Mathlib

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (𝒜 : ℤ → Submodule R A)

class DifferentialGradedAlgebra [GradedAlgebra 𝒜] where
  deriv : Derivation R A A
  derivIsHomogeneous (n : ℤ) (m : 𝒜 n) : deriv m ∈ 𝒜 (n - 1)
