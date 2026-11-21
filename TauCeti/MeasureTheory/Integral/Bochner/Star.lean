/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.Star

/-!
# The Bochner integral commutes with `star`

In a real normed space with a continuous real-linear `star`, the Bochner integral commutes with
`star`. This is the vector-valued analogue of Mathlib's `integral_conj` for `RCLike` scalars; it
applies for instance to complex normed spaces with a continuous conjugate-linear `star`, such as
`Fin n → ℂ` with coordinatewise conjugation. No integrability is needed, since `star` is a
continuous linear equivalence.
-/

public section

namespace MeasureTheory

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [StarAddMonoid F] [StarModule ℝ F] [ContinuousStar F]

/-- The Bochner integral commutes with a continuous real-linear `star`. -/
theorem integral_star (f : X → F) : ∫ x, star (f x) ∂μ = star (∫ x, f x ∂μ) :=
  (starL' ℝ : F ≃L[ℝ] F).integral_comp_comm f

end MeasureTheory
