/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Contractions against an orthonormal basis

Two sums over an orthonormal basis `b` that appear whenever a tensor is traced in an orthonormal
frame, for instance when the Ricci tensor is contracted to the scalar curvature:

* `OrthonormalBasis.sum_apply_mul_inner`: a linear functional `ℓ` satisfies
  `∑ i, ℓ (b i) * ⟪b i, a⟫ = ℓ a`, the expansion of `a` in `b` pushed through `ℓ`.
* `OrthonormalBasis.sum_inner_self`: `∑ i, ⟪b i, b i⟫ = card ι`, the trace of the identity.
-/

public section

namespace OrthonormalBasis

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

/-- A linear functional is recovered from its values on an orthonormal basis:
`∑ i, ℓ (b i) * ⟪b i, a⟫ = ℓ a`. -/
theorem sum_apply_mul_inner {F : Type*} [FunLike F E 𝕜] [LinearMapClass F 𝕜 E 𝕜]
    (b : OrthonormalBasis ι 𝕜 E) (ℓ : F) (a : E) : ∑ i, ℓ (b i) * ⟪b i, a⟫_𝕜 = ℓ a := by
  conv_rhs => rw [← b.sum_repr' a]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

/-- The vectors of an orthonormal basis have unit length, so `∑ i, ⟪b i, b i⟫ = card ι`. -/
theorem sum_inner_self (b : OrthonormalBasis ι 𝕜 E) : ∑ i, ⟪b i, b i⟫_𝕜 = Fintype.card ι := by
  simp [inner_self_eq_norm_sq_to_K, b.orthonormal.1]

end OrthonormalBasis
