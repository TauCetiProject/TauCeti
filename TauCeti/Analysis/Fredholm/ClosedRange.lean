/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Topology.Algebra.OpenMapping.FiniteCokernel
import TauCeti.Analysis.Fredholm.Parametric

/-!
# Closed range from a finite-dimensional cokernel

This file applies `ContinuousLinearMap.isClosed_range_of_finite_coker` (proved in
`TauCeti.Topology.Algebra.OpenMapping.FiniteCokernel`) to show that the closed-range hypothesis in
the definition of a Fredholm operator is *automatic* between Banach spaces once the cokernel is
finite dimensional.

This upgrades the Fredholm predicate of `TauCeti.Analysis.Fredholm.Basic`: over Banach spaces over
an `IsRCLikeNormedField` (in particular, real or complex Banach spaces), a Fredholm operator is
*exactly* a continuous linear map with finite-dimensional kernel and cokernel, the closed-range
condition following for free. Downstream this lets Sard–Smale and transversality arguments certify
Fredholmness of a linearization from the two defect spaces alone, without a separate closed-range
check.

## Main declarations

* `ContinuousLinearMap.IsFredholm.of_finite_ker_coker`: over Banach spaces over an
  `IsRCLikeNormedField`, finite-dimensional kernel and cokernel suffice for Fredholmness.
* `TauCeti.isFredholm_iff_finite_ker_coker`: over Banach spaces over an
  `IsRCLikeNormedField`, the Fredholm predicate is equivalent to finite dimensionality of the
  kernel and cokernel.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix
A.1, where a Fredholm operator has finite-dimensional kernel and cokernel; the closed-range
condition is noted there to be automatic between Banach spaces.
-/

public section

namespace TauCeti

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]


/-- Over Banach spaces over an `IsRCLikeNormedField`, a continuous linear map with
finite-dimensional kernel and cokernel is Fredholm: the closed-range condition is automatic.

This is the Banach-space form of the Fredholm criterion, complementing the direct constructor of
`ContinuousLinearMap.IsFredholm` by removing the closed-range obligation. -/
theorem _root_.ContinuousLinearMap.IsFredholm.of_finite_ker_coker (T : E →L[𝕜] F)
    (hker : FiniteDimensional 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)))
    (hcoker : FiniteDimensional 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F))) :
    ContinuousLinearMap.IsFredholm T where
  isStrictMap := by
    have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
    have hclosed := by
      have := hcoker
      exact ContinuousLinearMap.isClosed_range_of_finite_coker T
    let : CompleteSpace T.range := hclosed.completeSpace_coe
    rw [Topology.isStrictMap_iff_isQuotientMap_rangeFactorization]
    exact T.rangeRestrict.isQuotientMap Set.rangeFactorization_surjective
  isClosed_range := by
    have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
    have := hcoker
    exact ContinuousLinearMap.isClosed_range_of_finite_coker T
  finite_ker := hker
  finite_coker := hcoker
  closedComplemented_ker := by
    have := hker
    exact Submodule.ClosedComplemented.of_finiteDimensional T.ker

/-- Over Banach spaces over an `IsRCLikeNormedField`, the Fredholm predicate is equivalent to finite
dimensionality of the kernel and cokernel; closedness of the range is not an independent
condition. -/
theorem isFredholm_iff_finite_ker_coker (T : E →L[𝕜] F) :
    ContinuousLinearMap.IsFredholm T ↔
      FiniteDimensional 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) ∧
        FiniteDimensional 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) :=
  ⟨fun h => ⟨h.finite_ker, h.finite_coker⟩,
    fun h => .of_finite_ker_coker T h.1 h.2⟩

/-- **Fredholm operators from surjective stabilizations.** If adjoining finitely many domain
directions `B : S → F` makes `T` surjective with a finite-dimensional kernel, then `T` is Fredholm:
its kernel embeds into that of `T.coprod B`, and its cokernel is the image of `S`. -/
theorem _root_.ContinuousLinearMap.IsFredholm.of_surjective_coprod {S : Type*}
    [NormedAddCommGroup S] [NormedSpace 𝕜 S] [FiniteDimensional 𝕜 S] (T : E →L[𝕜] F)
    (B : S →L[𝕜] F) (h : Function.Surjective (T.coprod B))
    (hker : FiniteDimensional 𝕜 (T.coprod B).ker) : ContinuousLinearMap.IsFredholm T := by
  refine ContinuousLinearMap.IsFredholm.of_finite_ker_coker T ?_ ?_
  · exact ContinuousLinearMap.finiteDimensional_ker_of_finiteDimensional_ker_coprod T B
  · exact Module.Finite.of_surjective _
      ((ContinuousLinearMap.parameterToCoker_surjective_iff_coprod_surjective T B).2 h)

end TauCeti
