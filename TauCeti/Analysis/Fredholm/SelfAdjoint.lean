/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Self-adjoint Fredholm operators

This file proves that a self-adjoint Fredholm operator on a Hilbert space has index zero. More
generally, the same conclusion holds whenever an operator and its adjoint have the same kernel.
The closed range of a Fredholm operator has orthogonal complement equal to the kernel of its
adjoint. Orthogonal decomposition therefore identifies the cokernel with that kernel; under the
kernel-equality hypothesis, it identifies the cokernel with the original kernel.

## Main declarations

* `ContinuousLinearMap.IsFredholm.cokerEquivKerOfKerAdjointEq`: identify the cokernel with the
  kernel when the operator and its adjoint have equal kernels.
* `ContinuousLinearMap.index_eq_zero_of_ker_adjoint_eq`: the corresponding index-zero
  criterion.
* `ContinuousLinearMap.index_eq_zero_of_isSelfAdjoint`: a self-adjoint Fredholm operator
  has index zero.
* `ContinuousLinearMap.index_eq_zero_of_isSymmetric`: the same result in terms of
  symmetry of the underlying linear map.
* `ContinuousLinearMap.IsFredholm.isInvertible_of_injective_of_isSelfAdjoint`: an injective
  self-adjoint Fredholm operator is invertible.
* `ContinuousLinearMap.IsFredholm.isUnit_of_injective_of_isSelfAdjoint`: the same result in terms
  of units of the ring of continuous endomorphisms.
* `ContinuousLinearMap.IsFredholm.zero_notMem_spectrum_of_injective_of_isSelfAdjoint`: an
  injective self-adjoint Fredholm operator does not have `0` in its spectrum.

This is the elementary self-adjoint index computation for Fredholm operators. The convention and
argument follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace ContinuousLinearMap

open Module

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The cokernel of a Fredholm operator is linearly equivalent to its kernel if the operator and
its adjoint have the same kernel. -/
noncomputable def IsFredholm.cokerEquivKerOfKerAdjointEq {T : E →L[𝕜] E}
    (hT : IsFredholm T) (hker : (ContinuousLinearMap.adjoint T).ker = T.ker) :
    (E ⧸ LinearMap.range (T : E →ₗ[𝕜] E)) ≃ₗ[𝕜]
      LinearMap.ker (T : E →ₗ[𝕜] E) :=
  (cokerEquivKerAdjoint T hT.isClosed_range).toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ hker)

/-- The cokernel of a self-adjoint Fredholm operator is linearly equivalent to its kernel. -/
noncomputable def IsFredholm.cokerEquivKer {T : E →L[𝕜] E}
    (hT : IsFredholm T) (hself : IsSelfAdjoint T) :
    (E ⧸ LinearMap.range (T : E →ₗ[𝕜] E)) ≃ₗ[𝕜]
      LinearMap.ker (T : E →ₗ[𝕜] E) :=
  hT.cokerEquivKerOfKerAdjointEq <| by rw [hself.adjoint_eq]


/-- A Fredholm operator has index zero if it and its adjoint have the same kernel. -/
theorem index_eq_zero_of_ker_adjoint_eq {T : E →L[𝕜] E}
    (hT : IsFredholm T)
    (hker : (adjoint T).ker = T.ker) :
    index T = 0 := by
  rw [index_eq_finrank_sub,
    ← LinearEquiv.finrank_eq (hT.cokerEquivKerOfKerAdjointEq hker)]
  omega

/-- A self-adjoint Fredholm operator on a Hilbert space has Fredholm index zero. -/
@[simp]
theorem index_eq_zero_of_isSelfAdjoint {T : E →L[𝕜] E}
    (hT : IsFredholm T)
    (hself : IsSelfAdjoint T) : index T = 0 :=
  index_eq_zero_of_ker_adjoint_eq hT <| by rw [hself.adjoint_eq]

/-- A symmetric Fredholm operator on a Hilbert space has Fredholm index zero. -/
@[simp]
theorem index_eq_zero_of_isSymmetric {T : E →L[𝕜] E}
    (hT : IsFredholm T)
    (hsymm : T.IsSymmetric) : index T = 0 :=
  index_eq_zero_of_isSelfAdjoint hT
    (isSelfAdjoint_iff_isSymmetric.mpr hsymm)

/-- An injective self-adjoint Fredholm operator on a Hilbert space is invertible, since its index
vanishes. -/
theorem IsFredholm.isInvertible_of_injective_of_isSelfAdjoint {T : E →L[𝕜] E}
    (hT : IsFredholm T) (hself : IsSelfAdjoint T) (hinj : Function.Injective T) :
    T.IsInvertible :=
  hT.isInvertible_of_injective_of_index_eq_zero hinj (index_eq_zero_of_isSelfAdjoint hT hself)

/-- An injective self-adjoint Fredholm operator on a Hilbert space is a unit of the ring of
continuous endomorphisms. -/
theorem IsFredholm.isUnit_of_injective_of_isSelfAdjoint {T : E →L[𝕜] E}
    (hT : IsFredholm T) (hself : IsSelfAdjoint T) (hinj : Function.Injective T) : IsUnit T :=
  isInvertible_iff_isUnit.1 (hT.isInvertible_of_injective_of_isSelfAdjoint hself hinj)

/-- An injective self-adjoint Fredholm operator on a Hilbert space does not have `0` in its
spectrum. -/
theorem IsFredholm.zero_notMem_spectrum_of_injective_of_isSelfAdjoint {T : E →L[𝕜] E}
    (hT : IsFredholm T) (hself : IsSelfAdjoint T) (hinj : Function.Injective T) :
    (0 : 𝕜) ∉ spectrum 𝕜 T :=
  (spectrum.zero_notMem_iff 𝕜).2 (hT.isUnit_of_injective_of_isSelfAdjoint hself hinj)

end ContinuousLinearMap
