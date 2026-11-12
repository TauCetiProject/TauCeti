/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Hermitian dilation of a rectangular linear map

A linear map `A : E →ₗ[𝕜] F` between finite-dimensional inner product spaces determines
an endomorphism of the Hilbert direct sum `WithLp 2 (E × F)` with block matrix
`[[0, A†], [A, 0]]`. The dilation is self-adjoint, even when `E` and `F` differ.

The construction uses Mathlib's product linear maps and `LinearMap.withLpMap`. It respects
addition and subtraction, and its square is the block diagonal sum of the two Gram operators
`A† A` and `A A†`. These identities allow spectral arguments for self-adjoint operators to
be applied to rectangular operators and their singular subspaces.

## Source

Adapted from the AIQ-Kitware DKPS formalization (Kitware, Inc.; Apache-2.0):
https://github.com/AIQ-Kitware/aiq-dkps-formalization/blob/main/YuWangSamworth2015/YuWangSamworth2015/Core/SingularSubspace.lean
-/

public section

open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The Hermitian dilation of `A` on the Hilbert `L²` product of its domain and codomain. -/
noncomputable def hermitianDilation (A : E →ₗ[𝕜] F) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  ((A.adjoint ∘ₗ LinearMap.snd 𝕜 E F).prod
    (A ∘ₗ LinearMap.fst 𝕜 E F)).withLpMap 2

/-- The dilation interchanges the two summands, applying `A` and its adjoint. -/
@[simp]
theorem hermitianDilation_apply (A : E →ₗ[𝕜] F) (x : WithLp 2 (E × F)) :
    A.hermitianDilation x =
      WithLp.toLp 2 (A.adjoint (WithLp.ofLp x).2, A (WithLp.ofLp x).1) := by
  rfl

/-- The dilation of the zero map is zero. -/
@[simp]
theorem hermitianDilation_zero :
    hermitianDilation (0 : E →ₗ[𝕜] F) = 0 := by
  ext x
  apply WithLp.ofLp_injective 2
  ext <;> simp [hermitianDilation_apply]

/-- Hermitian dilation commutes with negation. -/
@[simp]
theorem hermitianDilation_neg (A : E →ₗ[𝕜] F) :
    hermitianDilation (-A) = -A.hermitianDilation := by
  ext x
  apply WithLp.ofLp_injective 2
  ext <;> simp [hermitianDilation_apply]

/-- Hermitian dilation is additive. -/
@[simp]
theorem hermitianDilation_add (A B : E →ₗ[𝕜] F) :
    hermitianDilation (A + B) = A.hermitianDilation + B.hermitianDilation := by
  ext x
  apply WithLp.ofLp_injective 2
  ext <;> simp [hermitianDilation_apply]

/-- Hermitian dilation commutes with subtraction, as used in perturbation bounds. -/
@[simp]
theorem hermitianDilation_sub (A B : E →ₗ[𝕜] F) :
    hermitianDilation (A - B) = A.hermitianDilation - B.hermitianDilation := by
  ext x
  apply WithLp.ofLp_injective 2
  ext <;> simp [hermitianDilation_apply]

/-- The Hermitian dilation of a rectangular linear map is symmetric. -/
theorem isSymmetric_hermitianDilation (A : E →ₗ[𝕜] F) :
    A.hermitianDilation.IsSymmetric := fun x y => by
  simp only [hermitianDilation_apply, WithLp.prod_inner_apply]
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right, add_comm]

/-- The Hermitian dilation is self-adjoint in finite dimensions. -/
theorem isSelfAdjoint_hermitianDilation (A : E →ₗ[𝕜] F) :
    IsSelfAdjoint A.hermitianDilation :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp A.isSymmetric_hermitianDilation

/-- The adjoint of a Hermitian dilation is itself. -/
@[simp]
theorem adjoint_hermitianDilation (A : E →ₗ[𝕜] F) :
    adjoint A.hermitianDilation = A.hermitianDilation :=
  LinearMap.isSelfAdjoint_iff'.mp A.isSelfAdjoint_hermitianDilation

/-- Squaring the dilation yields the two Gram operators on the diagonal. -/
theorem hermitianDilation_comp_self (A : E →ₗ[𝕜] F) :
    A.hermitianDilation ∘ₗ A.hermitianDilation =
      ((A.adjoint ∘ₗ A).prodMap (A ∘ₗ A.adjoint)).withLpMap 2 := by
  ext x
  apply WithLp.ofLp_injective 2
  ext <;> simp [hermitianDilation_apply, WithLp.map, prodMap_apply]

end LinearMap
