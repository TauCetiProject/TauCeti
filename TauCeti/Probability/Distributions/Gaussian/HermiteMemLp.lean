module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.MeasureTheory.Function.PolynomialMemLp

/-!
# `L²` membership of polynomials and Hermite polynomials against a Gaussian measure

This file proves that a real polynomial, evaluated pointwise, is square-integrable against a real
Gaussian measure `gaussianReal μ v`, and specializes this to the probabilists' Hermite polynomials
`Polynomial.hermite n`.  The Hermite statement `memLp_hermite_gaussianReal` is target **A3′** of the
`OrthogonalL2Bases` roadmap: the variance-general `L²` membership of the normalized Hermite
polynomials `Hₙ / √(n!)` under `gaussianReal 0 v`, the membership the Gaussian Hermite Hilbert-basis
construction consumes for its `MemLp` obligations.

The argument factors through the family-agnostic `memLp_two_eval_of_forall_integrable_pow`
(`TauCeti.MeasureTheory.Function.PolynomialMemLp`), which holds for **any** reference measure on `ℝ`
all of whose polynomial moments are finite.  The Gaussian instance supplies that moment hypothesis
`∀ k, Integrable (x ↦ xᵏ)` from Mathlib's `memLp_id_gaussianReal'` (all moments of a real Gaussian
are finite).  The
scalar-generic cast to `[RCLike 𝕜]` (needed because the roadmap's bases are stated over `Lp 𝕜 2 μ`
uniformly for `𝕜 = ℝ` and `𝕜 = ℂ`) reuses Mathlib's `MemLp.ofReal`, rewriting the `algebraMap ℝ 𝕜`
cast to `RCLike.ofReal`.

Mathlib's `memLp_id_gaussianReal'` (Fernique), `memLp_two_iff_integrable_sq`, and the `Polynomial`
evaluation API are consumed, not re-derived.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Polynomial

open scoped NNReal ENNReal

/-! ## The Gaussian instance -/

/-- Every polynomial moment of a real Gaussian measure is finite: `x ↦ xⁿ` is integrable against
`gaussianReal μ v`.  This is `memLp_id_gaussianReal'` (all moments finite) unwound to plain
integrability of the power. -/
theorem integrable_pow_gaussianReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal μ v) := by
  have h : Integrable (fun x : ℝ => ‖x‖ ^ n) (gaussianReal μ v) := by
    simpa using
      (memLp_id_gaussianReal' (μ := μ) (v := v) (n : ℝ≥0∞) (by simp)).integrable_norm_pow'
  rw [← integrable_norm_iff (continuous_pow n).aestronglyMeasurable]
  simpa only [norm_pow] using h

/-- A real polynomial is square-integrable against every real Gaussian measure. -/
theorem memLp_two_eval_gaussianReal (μ : ℝ) (v : ℝ≥0) (q : ℝ[X]) :
    MemLp (fun x : ℝ => q.eval x) 2 (gaussianReal μ v) :=
  memLp_two_eval_of_forall_integrable_pow (fun k => integrable_pow_gaussianReal μ v k) q

/-! ## Scalar-generic cast and the Hermite instance -/

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Target A3′ (variance-general `L²` membership).** The normalized probabilists' Hermite
polynomial `Hₙ / √(n!)`, cast into `𝕜`, is square-integrable against every centred real Gaussian
`gaussianReal 0 v`.  Immediate from `memLp_two_eval_gaussianReal` (Hermite is a polynomial) and the
scalar cast `MemLp.ofReal`. -/
theorem memLp_hermite_gaussianReal (n : ℕ) (v : ℝ≥0) :
    MemLp (fun x => (algebraMap ℝ 𝕜) (aeval x (hermite n) / Real.sqrt (n.factorial))) 2
      (gaussianReal 0 v) := by
  have key : ∀ x : ℝ, aeval x (hermite n) / Real.sqrt (n.factorial)
      = ((hermite n).map (Int.castRingHom ℝ)).eval x * (Real.sqrt (n.factorial))⁻¹ := by
    intro x
    rw [div_eq_mul_inv, Polynomial.aeval_def, algebraMap_int_eq, Polynomial.eval_map]
  simp only [key]
  simpa only [← RCLike.algebraMap_eq_ofReal] using
    ((memLp_two_eval_gaussianReal 0 v _).mul_const _).ofReal (K := 𝕜)

end TauCeti
