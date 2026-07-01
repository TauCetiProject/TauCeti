module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# `L²` membership of polynomials and Hermite polynomials against a Gaussian measure

This file proves that a real polynomial, evaluated pointwise, is square-integrable against a real
Gaussian measure `gaussianReal μ v`, and specializes this to the probabilists' Hermite polynomials
`Polynomial.hermite n`.  The Hermite statement `memLp_hermite_gaussianReal` is target **A3′** of the
`OrthogonalL2Bases` roadmap: the variance-general `L²` membership of the normalized Hermite
polynomials `Hₙ / √(n!)` under `gaussianReal 0 v`, the membership the Gaussian Hermite Hilbert-basis
construction consumes for its `MemLp` obligations.

The argument factors through two family-agnostic lemmas that hold for **any** reference measure on
`ℝ` all of whose polynomial moments are finite:

* `integrable_eval_of_forall_integrable_pow` — a polynomial is integrable, being a finite linear
  combination of monomials;
* `memLp_two_eval_of_forall_integrable_pow` — a polynomial is in `L²`, since the square of a
  polynomial is again a polynomial (hence integrable), and `memLp_two_iff_integrable_sq`.

These consume only the moment hypothesis `∀ k, Integrable (x ↦ xᵏ)`, so they apply verbatim to the
Chebyshev measure (compact support) as well as to the Gaussian.  The Gaussian instance supplies that
hypothesis from Mathlib's `memLp_id_gaussianReal'` (all moments of a real Gaussian are finite).  The
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

/-! ## Polynomials against a measure with finite moments (family-agnostic) -/

variable {μ : Measure ℝ}

/-- A real polynomial is integrable against any measure all of whose polynomial moments are finite.
The polynomial is a finite linear combination of the monomials `x ↦ xᵏ`, each integrable by
hypothesis. -/
theorem integrable_eval_of_forall_integrable_pow
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    Integrable (fun x : ℝ => q.eval x) μ := by
  simp_rw [Polynomial.eval_eq_sum_range]
  exact integrable_finsetSum _ fun i _ => (hmom i).const_mul _

/-- A real polynomial is in `L²` against any measure all of whose polynomial moments are finite.
The square of a polynomial is again a polynomial, hence integrable by
`integrable_eval_of_forall_integrable_pow`, and `L²` membership is integrability of the square. -/
theorem memLp_two_eval_of_forall_integrable_pow
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    MemLp (fun x : ℝ => q.eval x) 2 μ := by
  rw [memLp_two_iff_integrable_sq (Polynomial.continuous q).aestronglyMeasurable]
  have hsq : (fun x : ℝ => q.eval x ^ 2) = fun x : ℝ => (q ^ 2).eval x := by
    ext x; rw [Polynomial.eval_pow]
  rw [hsq]
  exact integrable_eval_of_forall_integrable_pow hmom (q ^ 2)

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
