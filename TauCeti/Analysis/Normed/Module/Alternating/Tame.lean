/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Taming a fixed endomorphism is an open condition

Let `E` be a finite-dimensional real normed space and `J` a continuous linear endomorphism of `E`.
A continuous alternating two-form `f` tames `J` when `f(u, J u) > 0` for every `u ≠ 0`. The set of
forms taming `J` is open (`ContinuousAlternatingMap.isOpen_setOf_forall_ne_zero_pos`): the map
sending `f` to the bilinear form `(u, v) ↦ f ![u, v]` is continuous, and the pairs `(B, A)` of a
continuous bilinear form and an endomorphism with `B(u, A u) > 0` for every `u ≠ 0` form an open
set (`TauCeti.isOpen_setOf_forall_bilinear_apply_endomorphism_pos`).

For a symplectic form and an almost complex structure `J`, this is the openness of taming
(`TauCeti.SymplecticForm.Tames`) in the form, which makes symplectic orientations locally constant
in continuous families of symplectic forms.
-/

public section

namespace ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The continuous alternating two-forms `f` taming a continuous linear endomorphism `J`, that is
with `f(u, J u) > 0` for every `u ≠ 0`, form an open set. -/
theorem isOpen_setOf_forall_ne_zero_pos (J : E →L[ℝ] E) :
    IsOpen {f : E [⋀^Fin 2]→L[ℝ] ℝ | ∀ u ≠ 0, 0 < f ![u, J u]} := by
  -- `f ↦ ((u, v) ↦ f ![u, v])` is continuous, so this is a preimage of the joint open set.
  have hc : Continuous fun f : E [⋀^Fin 2]→L[ℝ] ℝ ↦
      ((continuousMultilinearCurryFin1 ℝ E ℝ : _ →L[ℝ] E →L[ℝ] ℝ).comp
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 ↦ E) ℝ
          f.toContinuousMultilinearMap), J) := by
    fun_prop
  simpa [continuousMultilinearCurryFin1_apply] using
    TauCeti.isOpen_setOf_forall_bilinear_apply_endomorphism_pos.preimage hc

end ContinuousAlternatingMap
