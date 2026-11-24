/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.ReducedGeometry.Euclidean.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Euclidean reduced volume

The variational Euclidean reduced length determines the actual reduced-volume integral.
In every finite-dimensional real inner-product space its unnormalized value is
`(4 π t)^(dim / 2)` and its normalized value is one at each positive backward time.
This includes dimension zero and arbitrary basepoints. Gaussian integration is reused from
Mathlib; the reduced-length formula comes from minimization of the backward action.

The normalization follows J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*
(2007), Chapters 6–7, with the additional factor `(4 π)^(-dim / 2)`. Related formalizations:
https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open MeasureTheory Real

namespace TauCeti.ReducedGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The normalized reduced-volume integral of the static Euclidean metric. -/
def euclideanReducedVolume (p : E) (t : ℝ) : ℝ :=
  (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
    ∫ q : E, exp (-euclideanReducedLength p q t)

/-- The integral formula for normalized Euclidean reduced volume. -/
theorem euclideanReducedVolume_eq_integral (p : E) (t : ℝ) :
    euclideanReducedVolume p t =
      (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        ∫ q : E, exp (-euclideanReducedLength p q t) := by rfl

/-- The integral determined by the variational reduced length is exactly the Gaussian mass. -/
theorem integral_exp_neg_euclideanReducedLength (p : E) {t : ℝ} (ht : 0 ≤ t) :
    (∫ q : E, exp (-euclideanReducedLength p q t)) =
      (4 * π * t) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  rcases ht.eq_or_lt with rfl | ht
  · by_cases hE : Module.finrank ℝ E = 0
    · have : Subsingleton E := Module.finrank_zero_iff.mp hE
      have hnorm : ∀ q : E, ‖q‖ = 0 := fun q ↦ by rw [Subsingleton.elim q 0, norm_zero]
      simpa [hE, hnorm] using
        (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := 1) zero_lt_one)
    · have : Nontrivial E := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hE)
      simp [measure_univ_of_isAddLeftInvariant, measureReal_def,
        Real.zero_rpow (by positivity : (Module.finrank ℝ E : ℝ) / 2 ≠ 0)]
  have hfun : (fun q : E ↦ exp (-euclideanReducedLength p q t)) =
      fun q ↦ exp (-(4 * t)⁻¹ * ‖q - p‖ ^ 2) := by
    funext q
    rw [euclideanReducedLength_eq p q ht.le]
    congr 1
    ring
  rw [hfun]
  rw [integral_sub_right_eq_self (fun v : E ↦ exp (-(4 * t)⁻¹ * ‖v‖ ^ 2)) p]
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E)
    (b := (4 * t)⁻¹) (by positivity)
  convert h using 1
  congr 1
  field_simp

/-- The Euclidean reduced-volume kernel is integrable at every positive backward time. -/
theorem integrable_exp_neg_euclideanReducedLength (p : E) {t : ℝ} (ht : 0 < t) :
    Integrable (fun q : E ↦ exp (-euclideanReducedLength p q t)) := by
  by_contra h
  have hi := integral_exp_neg_euclideanReducedLength p ht.le
  rw [integral_undef h] at hi
  exact (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)) hi.symm

/-- Static Euclidean space has normalized reduced volume one at every positive backward time. -/
@[simp] theorem euclideanReducedVolume_eq_one (p : E) {t : ℝ} (ht : 0 < t) :
    euclideanReducedVolume p t = 1 := by
  rw [euclideanReducedVolume_eq_integral, integral_exp_neg_euclideanReducedLength p ht.le,
    neg_div, Real.rpow_neg (by positivity)]
  exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))

/-- Removing the dimensional factor gives Morgan–Tian's unnormalized Euclidean reduced volume. -/
theorem rpow_mul_integral_exp_neg_euclideanReducedLength (p : E) {t : ℝ} (ht : 0 < t) :
    t ^ (-(Module.finrank ℝ E : ℝ) / 2) *
      (∫ q : E, exp (-euclideanReducedLength p q t)) =
        (4 * π) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  rw [integral_exp_neg_euclideanReducedLength p ht.le,
    Real.mul_rpow (by positivity : 0 ≤ 4 * π) ht.le,
    neg_div, Real.rpow_neg ht.le]
  have hpow : t ^ ((Module.finrank ℝ E : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ht _)
  field_simp

end TauCeti.ReducedGeometry
