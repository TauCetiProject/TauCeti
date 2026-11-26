/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

import TauCeti.LinearAlgebra.Trace.Basic

/-!
# The trace of a continuous endomorphism as a continuous linear functional

On a finite-dimensional Hausdorff topological vector space `V` over a complete nontrivially
normed field `𝕜`, the trace `T ↦ trace T` of a continuous endomorphism is itself a continuous
linear functional `TauCeti.traceCLM 𝕜 V : (V →L[𝕜] V) →L[𝕜] 𝕜`, where `V →L[𝕜] V` carries its
usual topology of uniform convergence on bounded sets (the operator-norm topology when `V` is
normed). Continuity is not something the algebraic `LinearMap.trace` can see: it holds because
`V →L[𝕜] V` is again a finite-dimensional Hausdorff topological vector space over the complete
field `𝕜`, and every linear map out of such a space is continuous. The unbundled trace
`T ↦ LinearMap.trace 𝕜 V T` is continuous with no finite-dimensionality assumption
(`TauCeti.continuous_trace`), being zero in infinite dimension.

This bundled form is what lets the trace commute with limits, continuity and integrals: it is
used, for instance, for the continuity of the character of a continuous representation, to move
the trace through a Bochner integral of operators, and to define the divergence of a vector field
as the trace of its derivative.

Conjugation by a continuous linear equivalence `e`, `T ↦ e ∘ T ∘ e⁻¹`, preserves the unbundled
trace (`ContinuousLinearEquiv.trace_conjContinuousAlgEquiv`).
-/

public section

namespace TauCeti

variable (𝕜 V : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]

/-- The trace of a continuous endomorphism of a finite-dimensional Hausdorff topological vector
space, as a continuous linear functional. Continuity is automatic: `V →L[𝕜] V` is a
finite-dimensional Hausdorff topological vector space over the complete field `𝕜`, and every
linear map out of such a space is continuous. -/
noncomputable def traceCLM : (V →L[𝕜] V) →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace 𝕜 V).comp (ContinuousLinearMap.coeLM 𝕜))

variable {𝕜 V}

/-- `TauCeti.traceCLM` evaluates to the trace of the underlying linear map. -/
@[simp]
theorem traceCLM_apply (T : V →L[𝕜] V) :
    traceCLM 𝕜 V T = LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V) :=
  (rfl)

omit [FiniteDimensional 𝕜 V] in
/-- The trace `T ↦ trace T` of continuous endomorphisms of a Hausdorff topological vector space
is continuous. When `V` is infinite-dimensional, `LinearMap.trace` is the zero map. -/
theorem continuous_trace :
    Continuous fun T : V →L[𝕜] V ↦ LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V) := by
  by_cases hV : FiniteDimensional 𝕜 V
  · exact (traceCLM 𝕜 V).continuous
  · simpa only [TauCeti.LinearMap.trace_eq_zero_of_not_finite hV, LinearMap.zero_apply] using
      continuous_const

/-- The trace of a composition does not depend on the order of the factors:
`tr (S ∘ T) = tr (T ∘ S)`. -/
theorem _root_.ContinuousLinearMap.traceCLM_comp_comm (S T : V →L[𝕜] V) :
    traceCLM 𝕜 V (S ∘L T) = traceCLM 𝕜 V (T ∘L S) := by
  rw [traceCLM_apply, traceCLM_apply, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp]
  exact LinearMap.trace_comp_comm' (T : V →ₗ[𝕜] V) (S : V →ₗ[𝕜] V)

/-- The trace is invariant under conjugation by a one-sided inverse pair: if `M ∘ N = 1`, then
`tr (N ∘ T ∘ M) = tr T`. -/
theorem _root_.ContinuousLinearMap.traceCLM_comp_comp_of_comp_eq_id {W : Type*} [AddCommGroup W]
    [Module 𝕜 W] [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕜 W] [T2Space W]
    [FiniteDimensional 𝕜 W] {M : W →L[𝕜] V} {N : V →L[𝕜] W}
    (h : M ∘L N = ContinuousLinearMap.id 𝕜 V) (T : V →L[𝕜] V) :
    traceCLM 𝕜 W (N ∘L T ∘L M) = traceCLM 𝕜 V T := by
  rw [traceCLM_apply, traceCLM_apply, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.trace_comp_comm']
  simp [← ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.comp_assoc, h]

/-- The trace is invariant under conjugation by a continuous linear equivalence:
`tr (e ∘ T ∘ e⁻¹) = tr T`. -/
theorem _root_.ContinuousLinearEquiv.traceCLM_comp_comp_symm {W : Type*} [AddCommGroup W]
    [Module 𝕜 W] [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕜 W] [T2Space W]
    [FiniteDimensional 𝕜 W]
    (e : V ≃L[𝕜] W) (T : V →L[𝕜] V) :
    traceCLM 𝕜 W ((e : V →L[𝕜] W) ∘L T ∘L (e.symm : W →L[𝕜] V)) = traceCLM 𝕜 V T :=
  ContinuousLinearMap.traceCLM_comp_comp_of_comp_eq_id (by ext; simp) T

end TauCeti

namespace ContinuousLinearEquiv

variable {𝕜 G H : Type*} [NormedField 𝕜] [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G] [AddCommGroup H] [Module 𝕜 H]
  [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousConstSMul 𝕜 H]

/-- The trace is invariant under the conjugation `T ↦ e ∘ T ∘ e⁻¹` by a continuous linear
equivalence, with no finite-dimensionality assumption. -/
@[simp]
theorem trace_conjContinuousAlgEquiv (e : G ≃L[𝕜] H) (T : G →L[𝕜] G) :
    LinearMap.trace 𝕜 H (e.conjContinuousAlgEquiv T) = LinearMap.trace 𝕜 G T :=
  -- On underlying linear maps, `conjContinuousAlgEquiv` is `LinearEquiv.conj`.
  LinearMap.trace_conj' (T : G →ₗ[𝕜] G) e.toLinearEquiv

end ContinuousLinearEquiv
