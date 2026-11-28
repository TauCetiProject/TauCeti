/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Basic

/-!
# Isometric ring endomorphisms of `ℂ`

An isometric ring endomorphism `σ : ℂ →+* ℂ` is continuous, so it is the identity or complex
conjugation (Mathlib's `Complex.ringHom_eq_id_or_conj_of_continuous`). Hence `σ` is an involution
(`Complex.map_map_of_isometric`), commutes with complex conjugation
(`Complex.map_conj_of_isometric`) and commutes with Bochner integrals
(`Complex.map_integral_of_isometric`). These are the scalar facts needed for `σ`-semilinear maps
such as the transport of reproducing models.
-/

public section

open MeasureTheory
open scoped ComplexConjugate

namespace Complex

/-- An isometric ring endomorphism of `ℂ` (the identity or complex conjugation) is an
involution. -/
@[simp]
theorem map_map_of_isometric (σ : ℂ →+* ℂ) [RingHomIsometric σ] (z : ℂ) :
    σ (σ z) = z := by
  rcases ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl <;> simp

/-- An isometric ring endomorphism of `ℂ` (the identity or complex conjugation) commutes with
complex conjugation. -/
theorem map_conj_of_isometric (σ : ℂ →+* ℂ) [RingHomIsometric σ] (z : ℂ) :
    σ (conj z) = conj (σ z) := by
  rcases ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl <;> simp

/-- An isometric ring endomorphism of `ℂ` (the identity or complex conjugation) commutes with
Bochner integrals. -/
theorem map_integral_of_isometric {X : Type*} [MeasurableSpace X] (σ : ℂ →+* ℂ)
    [RingHomIsometric σ] (μ : Measure X) (f : X → ℂ) :
    σ (∫ x, f x ∂μ) = ∫ x, σ (f x) ∂μ := by
  rcases ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
  · simp
  · exact integral_conj.symm

end Complex
