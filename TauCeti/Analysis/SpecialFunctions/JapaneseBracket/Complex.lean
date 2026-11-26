/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Positivity
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.MeasureTheory.Constructions.Pi

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
  let e1 : (κ → ℂ) ≃ᵐ (κ → Fin 2 → ℝ) :=
    MeasurableEquiv.piCongrRight fun _ ↦ Complex.measurableEquivPi
  let e2 : (κ → Fin 2 → ℝ) ≃ᵐ (κ × Fin 2 → ℝ) := (MeasurableEquiv.curry κ (Fin 2) ℝ).symm
  let e3 : (κ × Fin 2 → ℝ) ≃ᵐ EuclideanSpace ℝ (κ × Fin 2) :=
    (EuclideanSpace.equiv (κ × Fin 2) ℝ).symm.toHomeomorph.toMeasurableEquiv
  let e : (κ → ℂ) ≃ᵐ EuclideanSpace ℝ (κ × Fin 2) := (e1.trans e2).trans e3
  have h1 : MeasurePreserving e1 :=
    volume_preserving_pi fun _ ↦ Complex.volume_preserving_equiv_pi
  have h2 : MeasurePreserving e2 := by
    simpa [volume_pi] using
      (TauCeti.measurePreserving_curry fun (_ : κ) (_ : Fin 2) ↦ (volume : Measure ℝ)).symm
  have h3 : MeasurePreserving e3 := PiLp.volume_preserving_toLp (κ × Fin 2)
  have he : MeasurePreserving e := (h3.comp h2).comp h1
  have h_norm (y : κ → ℂ) : ‖e y‖ ^ 2 = ∑ j : κ, ‖y j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [e, e1, e2, e3, Fin.sum_univ_two, MeasurableEquiv.piCongrRight,
      Complex.measurableEquivPi, sq]
  have h_pow (x : EuclideanSpace ℝ (κ × Fin 2)) :
      (1 + ‖x‖ ^ 2) ^ (-(2 * ((card κ : ℝ) + 1)) / 2) = (1 + ‖x‖ ^ 2)⁻¹ ^ (card κ + 1) := by
    rw [neg_div, mul_div_cancel_left₀ _ two_ne_zero, rpow_neg (by positivity),
      ← Nat.cast_one, ← Nat.cast_add, rpow_natCast, inv_pow]
  have h_dim : Module.finrank ℝ (EuclideanSpace ℝ (κ × Fin 2)) = 2 * card κ := by
    rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, mul_comm]
  have h_int : ∫ x : EuclideanSpace ℝ (κ × Fin 2), (1 + ‖x‖ ^ 2)⁻¹ ^ (card κ + 1) =
      π ^ card κ / (card κ).factorial := by
    have h := integral_rpow_neg_one_add_norm_sq (V := EuclideanSpace ℝ (κ × Fin 2))
      (r := 2 * ((card κ : ℝ) + 1)) (by rw [h_dim]; push_cast; linarith)
    simp_rw [h_pow] at h
    rw [h, h_dim]
    have h_sub : (2 * ((card κ : ℝ) + 1) - (2 * card κ : ℕ)) / 2 = 1 := by push_cast; ring
    have h_half : (2 * ((card κ : ℝ) + 1)) / 2 = (card κ : ℝ) + 1 := by ring
    have h_dim_half : ((2 * card κ : ℕ) : ℝ) / 2 = card κ := by push_cast; ring
    rw [h_sub, h_half, h_dim_half, Gamma_one, mul_one, rpow_natCast, Gamma_nat_eq_factorial]
  have h_int_y : ∫ y : κ → ℂ, (1 + ∑ j : κ, ‖y j‖ ^ 2)⁻¹ ^ (card κ + 1) =
      π ^ card κ / (card κ).factorial := by
    have h_comp := he.integral_comp' (g := fun x : EuclideanSpace ℝ (κ × Fin 2) ↦
      (1 + ‖x‖ ^ 2)⁻¹ ^ (card κ + 1))
    simpa only [h_norm] using h_comp.trans h_int
  have h_ne : π ^ card κ / (card κ).factorial ≠ 0 := by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (.of_integral_ne_zero (h_int_y.trans_ne h_ne))
    (.of_forall fun y ↦ by positivity), h_int_y]

end TauCeti
