/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import TauCeti.Analysis.Fredholm.Parametric

/-!
# Universal level sets of Fredholm families

Let `f : E × Λ → F` be a parametrized equation. At a zero `(x, l)`, write its derivative as
`D₁.coprod D₂`, where `D₁` differentiates in the `E` direction and `D₂` in the parameter
direction. The implicit function theorem locally parametrizes the universal zero set near `(x, l)`
once the total derivative is surjective and its kernel is topologically complemented.

The main result of this file obtains that complemented-kernel hypothesis from the condition used
in Fredholm transversality: `D₁` is Fredholm and `D₁.coprod D₂` is surjective. The proof splits the
finite-dimensional cokernel of `D₁` using parameter directions, and then solves the remaining
range component using a Fredholm decomposition. Thus it does not assume that the universal zero
set already has a manifold chart.

The linear splitting results hold over a complete nontrivially normed field, for topological
additive modules with continuous scalar multiplication in `Λ` and `F`. The three spaces need not
be normable, complete, or Hausdorff.

This is the splitting step in the parametric transversality package of McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.3. The resulting complement
feeds Mathlib's complemented-kernel implicit function theorem, while
`ContinuousLinearMap.parameterProj` describes the derivative of the projection from the universal
zero set to the parameter space.

## Main results

* `ContinuousLinearMap.IsFredholm.hasRightInverse_coprod`: a surjective total linearization whose
  fixed-parameter part is Fredholm admits a continuous linear right inverse.
* `ContinuousLinearMap.IsFredholm.closedComplemented_ker_coprod`: consequently, the kernel of the
  total linearization is topologically complemented.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
-/

public section

namespace ContinuousLinearMap.IsFredholm

variable {𝕜 E Λ F : Type*}
variable [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ]
variable [IsTopologicalAddGroup Λ] [ContinuousSMul 𝕜 Λ]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
variable {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F}

/-- **A surjective total linearization splits continuously when its fixed-parameter part is
Fredholm.**

If `D₁ : E →L[𝕜] F` is Fredholm and `D₁.coprod D₂ : E × Λ →L[𝕜] F` is surjective, then the latter
has a continuous linear right inverse. Parameter directions first solve the finite-dimensional
cokernel component of `D₁`; a Fredholm quasi-inverse then solves the remaining range component. -/
theorem hasRightInverse_coprod (hD₁ : ContinuousLinearMap.IsFredholm D₁)
    (hD : Function.Surjective (D₁.coprod D₂)) :
    (D₁.coprod D₂).HasRightInverse := by
  let pkg := hD₁.nonempty_fredholmPackage.some
  -- The cokernel is Hausdorff because the Fredholm range is closed.
  let : IsClosed (D₁.range : Set F) := hD₁.isClosed_range
  let : FiniteDimensional 𝕜 (F ⧸ D₁.range) := hD₁.finite_coker
  let q : Λ →L[𝕜] F ⧸ D₁.range := D₁.range.mkQL.comp D₂
  have hq : Function.Surjective q := by
    simpa only [Function.Surjective, ContinuousLinearMap.parameterToCoker_apply, q,
      ContinuousLinearMap.comp_apply, Submodule.mkQL_apply] using
      (ContinuousLinearMap.parameterToCoker_surjective_iff_coprod_surjective D₁ D₂).mpr hD
  obtain ⟨qinv, hqinv⟩ :=
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hq
  let L : F →L[𝕜] Λ := qinv.comp D₁.range.mkQL
  let R : F →L[𝕜] E :=
    pkg.quasiInverse.comp ((ContinuousLinearMap.id 𝕜 F) - D₂.comp L)
  refine ⟨R.prod L, fun y => ?_⟩
  have hsub_mem : y - D₂ (L y) ∈ pkg.decCodom.X₁ := by
    rw [← pkg.range_eq, ← Submodule.Quotient.mk_eq_zero]
    have h := hqinv (D₁.range.mkQ y)
    simpa [q, L, map_sub, sub_eq_zero] using h.symm
  have hproj : pkg.decCodom.proj (y - D₂ (L y)) = ⟨y - D₂ (L y), hsub_mem⟩ := by
    simpa only [FredholmDecomposition.proj] using
      Submodule.projectionOntoL_apply_left pkg.decCodom.isTopCompl
        (⟨y - D₂ (L y), hsub_mem⟩ : pkg.decCodom.X₁)
  have hright : D₁ (pkg.quasiInverse (y - D₂ (L y))) = y - D₂ (L y) := by
    simp [ContinuousLinearMap.FredholmPackage.quasiInverse, pkg.eq_equiv, hproj,
      FredholmDecomposition.proj]
  have hR : R y = pkg.quasiInverse (y - D₂ (L y)) := by
    simp [R]
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply]
  rw [hR, hright, sub_add_cancel]

/-- The kernel of a surjective total linearization is topologically complemented when its
fixed-parameter part is Fredholm. This is the complemented-kernel hypothesis required by the
Banach-space implicit function theorem for the universal zero set. -/
theorem closedComplemented_ker_coprod (hD₁ : ContinuousLinearMap.IsFredholm D₁)
    (hD : Function.Surjective (D₁.coprod D₂)) :
    (D₁.coprod D₂).ker.ClosedComplemented :=
  let hright := hD₁.hasRightInverse_coprod hD
  ContinuousLinearMap.closedComplemented_ker_of_rightInverse _ hright.rightInverse
    hright.rightInverse_rightInverse

end ContinuousLinearMap.IsFredholm
