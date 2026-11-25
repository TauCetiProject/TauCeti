/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.ODE.Propagator.Liouville

/-!
# Liouville's formula for a diagonal coefficient

For a diagonal coefficient `P = diag(p₁, p₂)` on `Fin 2 → ℝ` with `p₁, p₂` integrable,
`TauCeti.det_toMatrix'_propagator` gives `det N_P(t, s) = e^{∫_s^t (p₁ + p₂)}`
(`TauCeti.Examples.Propagator.det_propagator_diagonal`).
-/

public section

open MeasureTheory Set

namespace TauCeti.Examples.Propagator

/-- **Liouville's formula for a diagonal coefficient.** For `p₁, p₂` integrable on `[a, b]` and
`s, t ∈ [a, b]`, the propagator of `diag(p₁, p₂)` on `Fin 2 → ℝ` has determinant
`exp (∫ s..t, (p₁ + p₂))`. -/
theorem det_propagator_diagonal {p₁ p₂ : ℝ → ℝ} {a b s t : ℝ}
    (h₁ : IntegrableOn p₁ (Icc a b)) (h₂ : IntegrableOn p₂ (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    (LinearMap.toMatrix' (propagator (fun r ↦ LinearMap.toContinuousLinearMap
      (Matrix.toLin' !![p₁ r, 0; 0, p₂ r])) t s : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ)).det =
      Real.exp (∫ r in s..t, (p₁ r + p₂ r)) := by
  have hP : IntegrableOn (fun r ↦ LinearMap.toContinuousLinearMap
      (Matrix.toLin' !![p₁ r, 0; 0, p₂ r])) (Icc a b) := by
    have : (fun r ↦ LinearMap.toContinuousLinearMap (Matrix.toLin' !![p₁ r, 0; 0, p₂ r])) =
        fun r ↦ p₁ r • LinearMap.toContinuousLinearMap (Matrix.toLin' !![(1 : ℝ), 0; 0, 0]) +
          p₂ r • LinearMap.toContinuousLinearMap (Matrix.toLin' !![(0 : ℝ), 0; 0, 1]) := by
      funext r
      ext v i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [this]
    exact (h₁.smul_const _).add (h₂.smul_const _)
  rw [det_toMatrix'_propagator hP hs ht, ← Real.exp_eq_exp_ℝ]
  simp [LinearMap.toMatrix'_toLin', Matrix.trace_fin_two]

end TauCeti.Examples.Propagator
