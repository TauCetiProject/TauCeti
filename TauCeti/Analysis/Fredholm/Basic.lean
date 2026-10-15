/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic

import TauCeti.Topology.Algebra.Module.Complement

/-!
# Fredholm operators

This file extends Mathlib's notion of a **Fredholm operator** with finite-dimensional examples
and invariance under scalar multiplication and continuous linear changes of coordinates.
All Fredholm hypotheses use `ContinuousLinearMap.IsFredholm` directly. That predicate asks for a
strict map with closed range, finite-dimensional kernel and cokernel, and a topologically
complemented kernel. Between Banach spaces over an `IsRCLikeNormedField`, finite-dimensional
kernel and cokernel imply the strictness, closed-range and complemented-kernel conditions.
Thus the predicate is *equivalent* there to finite dimensionality of the kernel and cokernel alone;
that equivalence is proved in `TauCeti.Analysis.Fredholm.ClosedRange` as
`TauCeti.isFredholm_iff_finite_ker_coker`.
Outside that setting `ContinuousLinearMap.IsFredholm` is genuinely stronger, and it is the notion
intended throughout.

## Main declarations

* `ContinuousLinearMap.isFredholm_of_finiteDimensional`: every operator between finite-dimensional
  topological vector spaces over a complete scalar field, with Hausdorff target, is Fredholm.
* `ContinuousLinearMap.IsFredholm.neg`, `ContinuousLinearMap.IsFredholm.smul`: Fredholmness is
  preserved by negation and by nonzero scalar multiples.
* `ContinuousLinearMap.IsFredholm.comp_equiv` and
  `ContinuousLinearMap.IsFredholm.equiv_comp`: composing with a continuous linear equivalence on
  either side preserves Fredholmness. These implications hold between topological modules over any
  `NontriviallyNormedField`, without completeness or separation assumptions.

The Fredholm index and its elementary API live in
`TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index`.
-/

public section

namespace ContinuousLinearMap

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
variable [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

section FiniteDimensional

variable [CompleteSpace 𝕜]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F] [FiniteDimensional 𝕜 F]

/-- Every continuous linear map between finite-dimensional topological vector spaces over a
complete scalar field is Fredholm, provided the target is Hausdorff. -/
lemma isFredholm_of_finiteDimensional (T : E →L[𝕜] F) : IsFredholm T where
  isStrictMap := T.isStrictMap_of_finiteDimensional
  isClosed_range := (LinearMap.range (T : E →ₗ[𝕜] F)).closed_of_finiteDimensional
  finite_ker := inferInstance
  finite_coker := inferInstance
  closedComplemented_ker :=
    Submodule.ClosedComplemented.of_finiteDimensional_quotient T.isClosed_ker

end FiniteDimensional

section CompEquiv

variable {T : E →L[𝕜] F}

/-- Postcomposing a Fredholm operator with a continuous linear equivalence yields a Fredholm
operator.

Unlike `ContinuousLinearMap.isFredholm_equiv_comp`, this implication does not require a complete
scalar field, continuous module operations, or Hausdorff spaces. -/
lemma IsFredholm.equiv_comp (hT : IsFredholm T) (e : F ≃L[𝕜] G) :
    IsFredholm ((e : F →L[𝕜] G).comp T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Expose function composition so the homeomorphism strictness lemma applies.
    change Topology.IsStrictMap (fun x ↦ e (T x))
    exact e.toHomeomorph.comp_isStrictMap_iff.mpr hT.isStrictMap
  · rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
    simpa [Submodule.map_coe] using e.isClosed_image.2 hT.isClosed_range
  · rw [ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearEquiv.ker_comp]
    exact hT.finite_ker
  · rw [ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearMap.range_comp]
    have := hT.finite_coker
    exact (Submodule.Quotient.equiv _ _ e.toLinearEquiv rfl).finiteDimensional
  · rw [ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearEquiv.ker_comp]
    exact hT.closedComplemented_ker

/-- Precomposing a Fredholm operator with a continuous linear equivalence yields a Fredholm
operator.

Unlike `ContinuousLinearMap.isFredholm_comp_equiv`, this implication does not require a complete
scalar field, continuous module operations, or Hausdorff spaces. -/
lemma IsFredholm.comp_equiv (hT : IsFredholm T) (e : G ≃L[𝕜] E) :
    IsFredholm (T.comp (e : G →L[𝕜] E)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Expose function composition so the homeomorphism strictness lemma applies.
    change Topology.IsStrictMap (fun x ↦ T (e x))
    exact e.toHomeomorph.isStrictMap_comp_iff.mpr hT.isStrictMap
  · simpa using hT.isClosed_range
  · rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.ker_comp,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
      Submodule.comap_equiv_eq_map_symm]
    have := hT.finite_ker
    exact (e.symm.submoduleMap _).finiteDimensional
  · simpa using hT.finite_coker
  · rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.ker_comp,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
      Submodule.comap_equiv_eq_map_symm]
    exact hT.closedComplemented_ker.map e.symm

end CompEquiv

variable [ContinuousConstSMul 𝕜 F] in
/-- A nonzero scalar multiple of a Fredholm operator is Fredholm. -/
lemma IsFredholm.smul {T : E →L[𝕜] F} (hT : IsFredholm T) {c : 𝕜} (hc : c ≠ 0) :
    IsFredholm (c • T) := by
  convert hT.equiv_comp (ContinuousLinearEquiv.smulLeft (R₁ := 𝕜) (M₁ := F)
    (Units.mk0 c hc)) using 1
  ext x
  simp

variable [IsTopologicalAddGroup F] in
/-- The negation of a Fredholm operator is Fredholm. -/
lemma IsFredholm.neg {T : E →L[𝕜] F} (hT : IsFredholm T) : IsFredholm (-T) := by
  convert hT.equiv_comp (ContinuousLinearEquiv.neg 𝕜) using 1
  ext x
  simp

end ContinuousLinearMap
