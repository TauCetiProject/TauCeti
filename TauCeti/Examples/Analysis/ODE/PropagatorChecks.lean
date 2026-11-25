/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.ODE.Propagator.Liouville

/-!
# Checks for continuous dependence on the coefficient and Liouville's formula

**Continuous dependence (§1.5).** For the scalar constant coefficients `p = 0` and `p′ = 1` on
`[0, 1]`, the propagators from `0` to `1` are `1` and `e`, and the bound
`‖N_{p′}(1, 0) − N_p(1, 0)‖ ≤ ‖p′ − p‖_{L¹} exp(‖p′‖_{L¹} + ‖p‖_{L¹})` reads `e − 1 ≤ e`
(`TauCeti.Examples.PropagatorChecks.norm_propagator_one_sub_propagator_zero`). For `P′ = P` the
bound is `0` (`TauCeti.Examples.PropagatorChecks.norm_propagator_sub_self_le`), and the propagator
only depends on the coefficient almost everywhere (`TauCeti.propagator_congr_ae`).

**Liouville's formula (§1.4).** For a diagonal coefficient `P = diag(p₁, p₂)` on `Fin 2 → ℝ` with
`p₁, p₂` integrable, `det N_P(t, s) = e^{∫_s^t (p₁ + p₂)}`
(`TauCeti.Examples.PropagatorChecks.det_propagator_diagonal`).

These are Checks of §§1.4 and 1.5 of the DiracScatteringAndNonlinearFourierTransform roadmap.
-/

public section

open MeasureTheory Set

namespace TauCeti.Examples.PropagatorChecks

/-- For the scalar coefficients `0` and `1` on `ℝ`, the propagators from `0` to `1` differ by
`e − 1`, and the continuity bound of §1.5 is `e`. -/
theorem norm_propagator_one_sub_propagator_zero :
    ‖propagator (fun _ ↦ (1 : ℝ →L[ℝ] ℝ)) 1 0 - propagator (fun _ ↦ (0 : ℝ →L[ℝ] ℝ)) 1 0‖ =
        Real.exp 1 - 1 ∧
      Real.exp 1 - 1 ≤ |∫ _ in (0 : ℝ)..1, ‖(1 : ℝ →L[ℝ] ℝ) - 0‖| *
        Real.exp (|∫ _ in (0 : ℝ)..1, ‖(1 : ℝ →L[ℝ] ℝ)‖| +
          |∫ _ in (0 : ℝ)..1, ‖(0 : ℝ →L[ℝ] ℝ)‖|) := by
  have h1 : propagator (fun _ ↦ (1 : ℝ →L[ℝ] ℝ)) 1 0 = Real.exp 1 • (1 : ℝ →L[ℝ] ℝ) := by
    rw [propagator_const, sub_zero, RCLike.ofReal_one, one_smul, Real.exp_eq_exp_ℝ,
      ← Algebra.algebraMap_eq_smul_one, NormedSpace.algebraMap_exp_comm, map_one]
  have h0 : propagator (fun _ ↦ (0 : ℝ →L[ℝ] ℝ)) 1 0 = 1 := by
    rw [propagator_const, smul_zero, NormedSpace.exp_zero]
  constructor
  · rw [h1, h0, show Real.exp 1 • (1 : ℝ →L[ℝ] ℝ) - 1 = (Real.exp 1 - 1) • 1 by
      rw [sub_smul (Real.exp 1) 1 (1 : ℝ →L[ℝ] ℝ), one_smul], norm_smul, norm_one, mul_one,
      Real.norm_of_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])]
  · simp only [sub_zero, norm_one, norm_zero, intervalIntegral.integral_const, smul_eq_mul,
      mul_one, mul_zero, abs_one, abs_zero, add_zero, one_mul]
    linarith

/-- For `P′ = P` the continuity bound of §1.5 is `0`. -/
theorem norm_propagator_sub_self_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ → E →L[ℝ] E) (t s : ℝ) :
    ‖propagator P t s - propagator P t s‖ ≤ |∫ u in s..t, ‖P u - P u‖| := by
  simp

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

end TauCeti.Examples.PropagatorChecks
