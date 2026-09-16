/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Analysis.Real.Sqrt

/-!
# Continuity of quadratic maps

A quadratic map on a finite module is continuous for the module topologies when two is
invertible. This follows from Mathlib's continuity theorem for bilinear maps by evaluating
the associated bilinear map on the diagonal.

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
