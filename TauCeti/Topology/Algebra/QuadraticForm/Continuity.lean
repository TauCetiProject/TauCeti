/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
-- Supplies the real topology used by the public `IsModuleTopology ℝ V` hypothesis.
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Analysis.Real.Sqrt

/-!
# Continuity of quadratic maps

A quadratic map on a finite module is continuous for the module topologies when two is
invertible. This follows from Mathlib's continuity theorem for bilinear maps by evaluating
the associated bilinear map on the diagonal.
For any continuous quadratic map, its preserving endomorphisms form a closed set when the
codomain is Hausdorff.

Over the reals, near a vector with nonzero quadratic value, the ratio to that value is a
nonzero square. This is the neighborhood condition that allows weak approximation of vectors
to preserve the square classes of their quadratic values.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §66.
-/

public section

namespace TauCeti

open scoped Topology

/-- A quadratic map on a finite module is continuous for the module topologies if two is
invertible on its codomain. -/
@[continuity, fun_prop]
theorem _root_.QuadraticMap.continuous
    {R M N : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [TopologicalSpace M] [IsModuleTopology R M]
    [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]
    [Invertible (2 : Module.End R N)] (Q : QuadraticMap R M N) : Continuous Q := by
  simpa only [Function.comp_def, id_eq, QuadraticMap.associated_eq_self_apply] using
    (IsModuleTopology.continuous_bilinear_of_finite_left (Q.associatedHom R)).comp
      (continuous_id.prodMk continuous_id)

/-- Endomorphisms preserving a continuous quadratic map form a closed subset of the
endomorphism space when the codomain is Hausdorff. -/
theorem _root_.QuadraticMap.isClosed_setOfPred_forall_map_app
    {R M N : Type*} [CommRing R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
    [TopologicalSpace (Module.End R M)] [IsModuleTopology R (Module.End R M)]
    [AddCommGroup N] [Module R N] [TopologicalSpace N] [T2Space N]
    (Q : QuadraticMap R M N) (hQ : Continuous Q) :
    IsClosed {f : Module.End R M | ∀ x : M, Q (f x) = Q x} := by
  let : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  have h (x : M) : IsClosed {f : Module.End R M | Q (f x) = Q x} := by
    have hev : Continuous (fun f : Module.End R M => f x) :=
      IsModuleTopology.continuous_of_linearMap ((LinearMap.applyₗ :
        M →ₗ[R] Module.End R M →ₗ[R] M) x)
    exact isClosed_eq (hQ.comp hev) continuous_const
  simpa only [Set.ofPred_forall] using isClosed_iInter h

/-- Near a vector where a real quadratic form is nonzero, its value remains nonzero and in
the same square class. No nondegeneracy assumption on the form is needed. -/
theorem _root_.QuadraticForm.eventually_isSquare_div
    {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    [TopologicalSpace V] [IsModuleTopology ℝ V]
    (Q : QuadraticForm ℝ V) {x : V} (hx : Q x ≠ 0) :
    ∀ᶠ z in 𝓝 x, Q z ≠ 0 ∧ IsSquare (Q z / Q x) := by
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have hpos : ∀ᶠ z in 𝓝 x, 0 < Q z / Q x :=
    (Q.continuous.div_const (Q x)).continuousAt.eventually
      (isOpen_Ioi.mem_nhds (by simp [hx]))
  filter_upwards [hpos] with z hz
  exact ⟨fun hzero ↦ by simp [hzero] at hz, Real.isSquare_iff.mpr hz.le⟩

end TauCeti
