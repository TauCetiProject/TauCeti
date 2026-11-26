/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.Positivity
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Complex Japanese-bracket integral

Specializes `TauCeti.integral_rpow_neg_one_add_norm_sq` to the complex vector space `κ → ℂ`
(real dimension `2 * Fintype.card κ`) at exponent `-(card κ + 1)`.

## Main results

* `TauCeti.lintegral_one_add_sum_norm_sq_inv_pow`: the lower Lebesgue integral of
  `(1 + ∑ j, ‖y j‖²) ^ (-(k + 1))` over `y : κ → ℂ` (`k = Fintype.card κ`) equals `π ^ k / k!`.
-/

public section

open Fintype MeasureTheory Real

namespace TauCeti

/-- The integral of `(1 + ∑ j, ‖y j‖²) ^ (-(k + 1))` over `y : κ → ℂ` (`k = card κ`) is
`π ^ k / k!`. -/
theorem lintegral_one_add_sum_norm_sq_inv_pow {κ : Type*} [Fintype κ] :
    ∫⁻ y : κ → ℂ, ENNReal.ofReal ((1 + ∑ j : κ, ‖y j‖ ^ 2)⁻¹ ^ (card κ + 1)) =
      ENNReal.ofReal (π ^ card κ / (card κ).factorial) := by
  let e : (κ → ℂ) ≃ᵐ EuclideanSpace ℝ (κ ⊕ κ) :=
    (complexToRealEuclidean κ).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e := volume_preserving_complexToRealEuclidean
  have h_norm (y : κ → ℂ) : ‖e y‖ ^ 2 = ∑ j : κ, ‖y j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [e, complexToRealEuclidean_apply, sq]
  have h_pow (x : EuclideanSpace ℝ (κ ⊕ κ)) :
      (1 + ‖x‖ ^ 2) ^ (-(2 * ((card κ : ℝ) + 1)) / 2) = (1 + ‖x‖ ^ 2)⁻¹ ^ (card κ + 1) := by
    rw [neg_div, mul_div_cancel_left₀ _ two_ne_zero, rpow_neg (by positivity),
      ← Nat.cast_one, ← Nat.cast_add, rpow_natCast, inv_pow]
  have h_dim : Module.finrank ℝ (EuclideanSpace ℝ (κ ⊕ κ)) = 2 * card κ := by
    rw [finrank_euclideanSpace, Fintype.card_sum, two_mul]
  have h_int : ∫ x : EuclideanSpace ℝ (κ ⊕ κ), (1 + ‖x‖ ^ 2)⁻¹ ^ (card κ + 1) =
      π ^ card κ / (card κ).factorial := by
    have h := integral_rpow_neg_one_add_norm_sq (V := EuclideanSpace ℝ (κ ⊕ κ))
      (r := 2 * ((card κ : ℝ) + 1)) (by rw [h_dim]; push_cast; linarith)
    simp_rw [h_pow] at h
    rw [h, h_dim]
    have h_sub : (2 * ((card κ : ℝ) + 1) - (2 * card κ : ℕ)) / 2 = 1 := by push_cast; ring
    have h_half : (2 * ((card κ : ℝ) + 1)) / 2 = (card κ : ℝ) + 1 := by ring
    have h_dim_half : ((2 * card κ : ℕ) : ℝ) / 2 = card κ := by push_cast; ring
    rw [h_sub, h_half, h_dim_half, Gamma_one, mul_one, rpow_natCast, Gamma_nat_eq_factorial]
  have h_int_y : ∫ y : κ → ℂ, (1 + ∑ j : κ, ‖y j‖ ^ 2)⁻¹ ^ (card κ + 1) =
      π ^ card κ / (card κ).factorial := by
    have h_comp := he.integral_comp' (g := fun x : EuclideanSpace ℝ (κ ⊕ κ) ↦
      (1 + ‖x‖ ^ 2)⁻¹ ^ (card κ + 1))
    simpa only [h_norm] using h_comp.trans h_int
  have h_ne : π ^ card κ / (card κ).factorial ≠ 0 := by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (.of_integral_ne_zero (h_int_y.trans_ne h_ne))
    (.of_forall fun y ↦ by positivity), h_int_y]

end TauCeti
