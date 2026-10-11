/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Zero extension of a rectangular map to the square `L²` product

A linear map `A : E →ₗ[𝕜] F` between inner product spaces extends by zero to an endomorphism
`(x, y) ↦ (0, A x)` of the `L²` product `E × F`. For finite-dimensional `E` and `F` this
endomorphism has the same zero-padded singular values as `A`, so statements about square
operators transfer to rectangular maps.

## Main declarations

* `LinearMap.zeroExtension`: the zero extension `(x, y) ↦ (0, A x)`.
* `LinearMap.singularValues_zeroExtension`: the zero extension has the singular values of `A`.

## Source

Adapted from the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(`ForTauCeti/Analysis/InnerProductSpace/ZeroExtension.lean`).
Original copyright (c) 2026 Kitware, Inc.; Apache-2.0.
-/

public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace LinearMap

/-- The **zero extension** of `A : E →ₗ[𝕜] F` to an endomorphism of the `L²` product `E × F`:
the map `(x, y) ↦ (0, A x)`. -/
noncomputable def zeroExtension (A : E →ₗ[𝕜] F) : WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ inr 𝕜 E F ∘ₗ A ∘ₗ WithLp.fstₗ 2 𝕜 E F

@[simp]
theorem zeroExtension_apply (A : E →ₗ[𝕜] F) (z : WithLp 2 (E × F)) :
    A.zeroExtension z = WithLp.toLp 2 (0, A z.fst) :=
  (rfl)

/-- **Singular values of the zero extension**: extending `A : E →ₗ[𝕜] F` by zero to an
endomorphism of the `L²` product `E × F` leaves its zero-padded singular-value sequence
unchanged. -/
@[simp]
theorem singularValues_zeroExtension [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (A : E →ₗ[𝕜] F) : A.zeroExtension.singularValues = A.singularValues := by
  -- `A.zeroExtension = B ∘ fst` for `B = (0, A ·)`, and the adjoint of `fst` is the inclusion
  -- of the first factor; both `B` and that inclusion preserve norms.
  set B : E →ₗ[𝕜] WithLp 2 (E × F) :=
    (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ inr 𝕜 E F ∘ₗ A
  have hB : B.singularValues = A.singularValues :=
    singularValues_eq_of_norm_apply_eq fun x ↦ by simp [B, WithLp.norm_toLp_snd]
  have hA : A.zeroExtension = B ∘ₗ WithLp.fstₗ 2 𝕜 E F := rfl
  rw [hA, ← singularValues_adjoint, adjoint_comp, WithLp.adjoint_fstₗ, ← hB,
    ← singularValues_adjoint B]
  exact singularValues_eq_of_norm_apply_eq fun x ↦ by simp [WithLp.norm_toLp_fst]

end LinearMap
