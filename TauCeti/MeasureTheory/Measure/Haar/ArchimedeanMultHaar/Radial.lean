/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import TauCeti.MeasureTheory.Measure.Haar.ArchimedeanMultHaar

/-!
# The radial majorant `(1 + log² |z|)⁻¹` for the multiplicative Haar measure of `ℂˣ`

The multiplicative Haar measure `2 dx dy / (x² + y²)` of `ℂˣ` (`TauCeti.complexMultHaar`) has
image `4π dt / t` under `z ↦ |z|` (`TauCeti.map_norm_complexMultHaar`). The radial profile of
`(1 + log² |z|)⁻¹` is `(1 + log² t)⁻¹`; absorbing `dt / t` into the integrand gives Mathlib's
log-Cauchy density `(t (1 + log² t))⁻¹` against `dt` on `(0, ∞)`, of total mass `π`
(`integral_Ioi_zero_inv_mul_one_add_log_sq`), so
`∫ (1 + log² |z|)⁻¹ 2 dx dy / (x² + y²) = 4π²`. For a finite type `Φ`, the product
`a ↦ ∏_τ (1 + log² |a_τ|)⁻¹` is therefore integrable on `ℂ^Φ` for the product of the measures
`2 dx dy / (x² + y²)` (`TauCeti.integrable_prod_inv_one_add_log_sq`), with integral
`(4π²) ^ #Φ` (`TauCeti.integral_prod_inv_one_add_log_sq`). That product measure is carried by the
units `(ℂ^Φ)ˣ = (ℂˣ)^Φ` (`TauCeti.ae_isUnit_pi_complexMultHaar`), and on `(ℂˣ)^Φ` itself, for the
product of the Haar measures `TauCeti.complexUnitsMultHaar`, the same product is integrable
(`TauCeti.integrable_prod_inv_one_add_log_sq_units`).

## Main results

* `TauCeti.integral_inv_one_add_log_sq_complexMultHaar`: `∫ (1 + log² |z|)⁻¹ = 4π²`.
* `TauCeti.integrable_prod_inv_one_add_log_sq`: `a ↦ ∏_τ (1 + log² |a_τ|)⁻¹` is integrable on
  `ℂ^Φ` for the product of the measures `2 dx dy / (x² + y²)`.
* `TauCeti.integrable_prod_inv_one_add_log_sq_units`: the same on `(ℂˣ)^Φ` for the product of
  the Haar measures of `ℂˣ`.

## References

* The statement `TauCeti.integrable_prod_inv_one_add_log_sq` is
  `New.integrable_prod_inv_one_add_log_sq` of `Lib/SiegelWeil/Tower/PrincipalIdeles.lean` in the
  folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open MeasureTheory Measure Set
open scoped Real

namespace TauCeti

/-! ### The majorant `(1 + log² |z|)⁻¹` -/

/-- `z ↦ (1 + log² |z|)⁻¹` is integrable against `2 dx dy / (x² + y²)`: its radial profile
`(1 + log² t)⁻¹` against `dt / t` is Mathlib's log-Cauchy density `(t (1 + log² t))⁻¹` against
`dt` on `(0, ∞)`. -/
theorem integrable_inv_one_add_log_sq_complexMultHaar :
    Integrable (fun z : ℂ ↦ (1 + Real.log ‖z‖ ^ 2)⁻¹) complexMultHaar := by
  refine (integrable_complexMultHaar_comp_norm_iff (h := fun t ↦ (1 + Real.log t ^ 2)⁻¹)).2
    (integrable_multHaar_iff.2 ?_)
  simpa only [one_mul, mul_inv, smul_eq_mul] using
    integrableOn_Ioi_zero_inv_mul_one_add_log_sq one_ne_zero

/-- `∫ (1 + log² |z|)⁻¹ 2 dx dy / (x² + y²) = 4π²`: the radial profile has mass `π` against
`dt / t` (Mathlib's `integral_Ioi_zero_inv_mul_one_add_log_sq`). -/
theorem integral_inv_one_add_log_sq_complexMultHaar :
    ∫ z : ℂ, (1 + Real.log ‖z‖ ^ 2)⁻¹ ∂complexMultHaar = 4 * π ^ 2 := by
  have hπ : ∫ t in Ioi 0, t⁻¹ • (1 + Real.log t ^ 2)⁻¹ = π := by
    simpa only [one_mul, mul_inv, smul_eq_mul, abs_one, div_one] using
      integral_Ioi_zero_inv_mul_one_add_log_sq 1
  rw [integral_complexMultHaar_comp_norm fun t ↦ (1 + Real.log t ^ 2)⁻¹,
    integral_multHaar_eq_setIntegral, hπ, smul_eq_mul]
  ring

/-! ### Products over a finite set of complex places -/

variable {Φ : Type*} [Fintype Φ]

/-- **The majorant `∏_τ (1 + log² |a_τ|)⁻¹` is integrable** on `ℂ^Φ` for the product of the
measures `2 dx dy / (x² + y²)`, that is, for Haar measure on `(ℂˣ)^Φ`
(`TauCeti.ae_isUnit_pi_complexMultHaar`). -/
theorem integrable_prod_inv_one_add_log_sq :
    Integrable (fun a : Φ → ℂ ↦ ∏ τ, (1 + Real.log ‖a τ‖ ^ 2)⁻¹)
      (Measure.pi fun _ : Φ ↦ complexMultHaar) :=
  Integrable.fintype_prod fun _ ↦ integrable_inv_one_add_log_sq_complexMultHaar

/-- **The majorant `∏_τ (1 + log² |a_τ|)⁻¹` is integrable on `(ℂˣ)^Φ`** for the product of the
Haar measures `TauCeti.complexUnitsMultHaar` of the factors. -/
theorem integrable_prod_inv_one_add_log_sq_units :
    Integrable (fun a : Φ → ℂˣ ↦ ∏ τ, (1 + Real.log ‖(a τ : ℂ)‖ ^ 2)⁻¹)
      (Measure.pi fun _ : Φ ↦ complexUnitsMultHaar) := by
  have hval : Measurable fun a : Φ → ℂˣ ↦ fun τ ↦ (a τ : ℂ) :=
    measurable_pi_iff.2 fun τ ↦
      Units.measurableEmbedding_val.measurable.comp (measurable_pi_apply τ)
  -- Coordinatewise, `complexUnitsMultHaar` is carried to `complexMultHaar` by `Units.val`.
  have hmap : (Measure.pi fun _ : Φ ↦ complexUnitsMultHaar).map (fun a τ ↦ (a τ : ℂ)) =
      Measure.pi fun _ : Φ ↦ complexMultHaar := by
    rw [Measure.pi_map_pi (hμ := fun _ ↦ map_val_complexUnitsMultHaar ▸ inferInstance)
      fun _ ↦ Units.measurableEmbedding_val.measurable.aemeasurable]
    simp only [map_val_complexUnitsMultHaar]
  have h := integrable_prod_inv_one_add_log_sq (Φ := Φ)
  rw [← hmap] at h
  exact (integrable_map_measure h.1 hval.aemeasurable).1 h

/-- The integral of `∏_τ (1 + log² |a_τ|)⁻¹` on `ℂ^Φ` for the product of the measures
`2 dx dy / (x² + y²)` is `(4π²) ^ #Φ`. -/
theorem integral_prod_inv_one_add_log_sq :
    ∫ a : Φ → ℂ, ∏ τ, (1 + Real.log ‖a τ‖ ^ 2)⁻¹ ∂(Measure.pi fun _ : Φ ↦ complexMultHaar) =
      (4 * π ^ 2) ^ Fintype.card Φ := by
  rw [integral_fintype_prod_eq_pow fun z : ℂ ↦ (1 + Real.log ‖z‖ ^ 2)⁻¹,
    integral_inv_one_add_log_sq_complexMultHaar]

end TauCeti
