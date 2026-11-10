/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Real finrank of a compatible complex module

This file records the tower-law dimension formula for a complex module whose real scalar
structure is the ambient one. It is the linear-algebra input for almost-complex even-dimensionality
results, but has no symplectic hypotheses. Consequently a real-linear isomorphism between two such
modules preserves the complex dimension (`LinearEquiv.finrank_complex_eq`).
-/

public section

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A compatible complex module structure forces the real dimension to be twice the complex
dimension. This is the ambient-real-structure form of Mathlib's `finrank_real_of_complex`: that
lemma fixes the real structure to be the one induced by restricting scalars
(`Module.complexToReal`), whereas here `V` already carries an ambient `Module ℝ V` made compatible
via `IsScalarTower ℝ ℂ V` (the situation produced by an almost complex structure). -/
theorem finrank_real_eq_two_mul_finrank_complex [Module ℂ V] [IsScalarTower ℝ ℂ V] :
    Module.finrank ℝ V = 2 * Module.finrank ℂ V := by
  rw [← Module.finrank_mul_finrank ℝ ℂ V, Complex.finrank_real_complex]

end TauCeti

/-- Real-linearly isomorphic complex modules have the same complex dimension, since the real
dimension is twice the complex one (`TauCeti.finrank_real_eq_two_mul_finrank_complex`). -/
theorem LinearEquiv.finrank_complex_eq {V W : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V]
    [IsScalarTower ℝ ℂ V] [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]
    (g : V ≃ₗ[ℝ] W) : Module.finrank ℂ V = Module.finrank ℂ W := by
  have := g.finrank_eq
  rw [TauCeti.finrank_real_eq_two_mul_finrank_complex,
    TauCeti.finrank_real_eq_two_mul_finrank_complex] at this
  omega
