/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.DistribChar
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
import TauCeti.MeasureTheory.Integral.Circle.LIntegral

/-!
# The multiplicative Haar measures of `ℝˣ` and `ℂˣ`

The archimedean factors of the normalized Haar measure on the ideles are the measures `dx / |x|`
on `ℝˣ` and `2 dx dy / (x² + y²)` on `ℂˣ`: Tate's self-dual additive Haar measure (`dx` on `ℝ`,
`2 dx dy` on `ℂ`) with density the inverse of the normalized absolute value, which is `|x|` at a
real place and `|z| ^ 2` at a complex place. With respect to Lebesgue measure the densities are
`|x|⁻¹` and `2 |z|⁻²`. This file defines them as measures on `ℝ` and `ℂ` that do not charge `0`
(`TauCeti.realMultHaar`, `TauCeti.complexMultHaar`) and shows that they are invariant under
multiplication by every nonzero scalar (`TauCeti.map_realMultHaar_mul_left`,
`TauCeti.map_complexMultHaar_mul_left`). On `(0, ∞)`, `dx / |x|` is `TauCeti.multHaar`
(`TauCeti.realMultHaar_restrict_Ioi`), so it is `dt / t` plus its reflection
(`TauCeti.realMultHaar_eq_multHaar_add_map_neg`).

The invariance is an instance of `MeasureTheory.Measure.map_smul_withDensity`: if `g` scales
additive Haar measure by `distribHaarChar A g` and a density `f` satisfies
`distribHaarChar A g * f (g • x) = f x`, then the measure with density `f` is invariant under
`g • ·`.

The normalizations are fixed by masses: for `0 < a ≤ b`, `dx / |x|` gives `[a, b]` mass
`log b - log a` (`TauCeti.realMultHaar_Icc`), and, by polar coordinates, `2 dx dy / (x² + y²)` gives
the annulus `a ≤ |z| ≤ b` mass `2 · 2π · (log b - log a)`
(`TauCeti.complexMultHaar_setOf_norm_mem_Icc`). In particular `[1, e]` has mass one
(`TauCeti.realMultHaar_Icc_one_exp_one`) and the annulus `1 ≤ |z| ≤ e` has mass `4π`
(`TauCeti.complexMultHaar_setOf_norm_mem_Icc_one_exp_one`).

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §2.3.
-/

public section

open MeasureTheory Measure Set
open scoped ENNReal NNReal Real

namespace TauCeti

/-- The multiplicative Haar measure `dx / |x|` of `ℝˣ`, as a measure on `ℝ`: Lebesgue measure with
density `|x|⁻¹`. It does not charge `0`. -/
noncomputable def realMultHaar : Measure ℝ :=
  volume.withDensity fun x ↦ ENNReal.ofReal |x|⁻¹

/-- The defining formula of `dx / |x|`. -/
theorem realMultHaar_def :
    realMultHaar = volume.withDensity fun x ↦ ENNReal.ofReal |x|⁻¹ := (rfl)

instance : SigmaFinite realMultHaar := by
  rw [realMultHaar_def]
  infer_instance

instance : NullSingletonClass realMultHaar := by
  rw [realMultHaar_def]
  infer_instance

/-- The lower integral against `dx / |x|` is the Lebesgue lower integral of `|x|⁻¹ * f x`. -/
theorem lintegral_realMultHaar (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂realMultHaar = ∫⁻ x, ENNReal.ofReal |x|⁻¹ * f x := by
  rw [realMultHaar_def, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (by fun_prop) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [Pi.mul_apply]

/-- A function is integrable against `dx / |x|` exactly when `|x|⁻¹ • f x` is Lebesgue
integrable. -/
theorem integrable_realMultHaar_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} : Integrable f realMultHaar ↔ Integrable fun x ↦ |x|⁻¹ • f x := by
  rw [realMultHaar_def, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))]

/-- The integral against `dx / |x|` is the Lebesgue integral of `|x|⁻¹ • f x`. -/
theorem integral_realMultHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : ∫ x, f x ∂realMultHaar = ∫ x, |x|⁻¹ • f x := by
  rw [realMultHaar_def, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))]

/-- The multiplicative Haar measure `2 dx dy / (x² + y²)` of `ℂˣ`, as a measure on `ℂ`: Lebesgue
measure with density `2 |z|⁻²`. It does not charge `0`. -/
noncomputable def complexMultHaar : Measure ℂ :=
  volume.withDensity fun z ↦ ENNReal.ofReal (2 * (‖z‖ ^ 2)⁻¹)

/-- The defining formula of `2 dx dy / (x² + y²)`. -/
theorem complexMultHaar_def :
    complexMultHaar = volume.withDensity fun z ↦ ENNReal.ofReal (2 * (‖z‖ ^ 2)⁻¹) := (rfl)

instance : SigmaFinite complexMultHaar := by
  rw [complexMultHaar_def]
  infer_instance

instance : NullSingletonClass complexMultHaar := by
  rw [complexMultHaar_def]
  infer_instance

/-- The lower integral against `2 dx dy / (x² + y²)` is the Lebesgue lower integral of
`2 |z|⁻² * f z`. -/
theorem lintegral_complexMultHaar (f : ℂ → ℝ≥0∞) :
    ∫⁻ z, f z ∂complexMultHaar = ∫⁻ z, ENNReal.ofReal (2 * (‖z‖ ^ 2)⁻¹) * f z := by
  rw [complexMultHaar_def, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (by fun_prop) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [Pi.mul_apply]

/-- A function is integrable against `2 dx dy / (x² + y²)` exactly when `2 |z|⁻² • f z` is
Lebesgue integrable. -/
theorem integrable_complexMultHaar_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} : Integrable f complexMultHaar ↔ Integrable fun z ↦ (2 * (‖z‖ ^ 2)⁻¹) • f z := by
  rw [complexMultHaar_def, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * (‖_‖ ^ 2)⁻¹)]

/-- The integral against `2 dx dy / (x² + y²)` is the Lebesgue integral of `2 |z|⁻² • f z`. -/
theorem integral_complexMultHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) : ∫ z, f z ∂complexMultHaar = ∫ z, (2 * (‖z‖ ^ 2)⁻¹) • f z := by
  rw [complexMultHaar_def, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * (‖_‖ ^ 2)⁻¹)]

/-- On `(0, ∞)`, `dx / |x|` is `dt / t` (`TauCeti.multHaar`). -/
theorem realMultHaar_restrict_Ioi : realMultHaar.restrict (Ioi 0) = multHaar := by
  rw [realMultHaar_def, multHaar_def, restrict_withDensity measurableSet_Ioi]
  exact withDensity_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono fun x (hx : 0 < x) ↦ by
    simp only [abs_of_pos hx])

/-- The scaling identity `‖a‖ * ‖a * x‖⁻¹ = ‖x‖⁻¹` behind the invariance of `dx / |x|` and of
`2 dx dy / (x² + y²)`. -/
private theorem norm_mul_inv_norm_mul {K : Type*} [NormedField K] {a : K} (ha : a ≠ 0) (x : K) :
    ‖a‖ * ‖a * x‖⁻¹ = ‖x‖⁻¹ := by
  rw [norm_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_mul]

/-- `dx / |x|` is invariant under multiplication by a nonzero real number. -/
theorem map_realMultHaar_mul_left {a : ℝ} (ha : a ≠ 0) :
    realMultHaar.map (a * ·) = realMultHaar := by
  -- Multiplication by `a` is the scalar action of the unit `Units.mk0 a ha`.
  have hsmul : (a * ·) = (Units.mk0 a ha • · : ℝ → ℝ) := funext fun x ↦ by
    rw [Units.smul_def, Units.val_mk0, smul_eq_mul]
  rw [hsmul, realMultHaar_def]
  refine map_smul_withDensity volume (Units.mk0 a ha) fun x ↦ ?_
  rw [distribHaarChar_real_eq, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simpa [Units.smul_def, Real.norm_eq_abs] using norm_mul_inv_norm_mul ha x

/-- `dx / |x|` is `dt / t` on `(0, ∞)` plus its reflection on `(-∞, 0)`. -/
theorem realMultHaar_eq_multHaar_add_map_neg :
    realMultHaar = multHaar + multHaar.map Neg.neg := by
  have hneg : realMultHaar.map Neg.neg = realMultHaar := by
    simpa [neg_one_mul] using map_realMultHaar_mul_left (a := -1) (by norm_num)
  rw [← restrict_add_restrict_compl (μ := realMultHaar) measurableSet_Ioi, compl_Ioi,
    restrict_congr_set (Iio_ae_eq_Iic' (measure_singleton 0)).symm, realMultHaar_restrict_Ioi]
  congr 1
  conv_lhs => rw [← hneg]
  rw [restrict_map measurable_neg measurableSet_Iio, neg_preimage, neg_Iio, neg_zero,
    realMultHaar_restrict_Ioi]

/-- `2 dx dy / (x² + y²)` is invariant under multiplication by a nonzero complex number. -/
theorem map_complexMultHaar_mul_left {a : ℂ} (ha : a ≠ 0) :
    complexMultHaar.map (a * ·) = complexMultHaar := by
  -- Multiplication by `a` is the scalar action of the unit `Units.mk0 a ha`.
  have hsmul : (a * ·) = (Units.mk0 a ha • · : ℂ → ℂ) := funext fun z ↦ by
    rw [Units.smul_def, Units.val_mk0, smul_eq_mul]
  rw [hsmul, complexMultHaar_def]
  refine map_smul_withDensity volume (Units.mk0 a ha) fun z ↦ ?_
  rw [distribHaarChar_complex_eq, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h := congrArg (· ^ 2) (norm_mul_inv_norm_mul ha z)
  simp only [Units.smul_def, Units.val_mk0, smul_eq_mul, NNReal.coe_pow, coe_nnNorm,
    Complex.finrank_real_complex]
  linear_combination 2 * h

/-- `dx / |x|` gives the interval `[a, b]` mass `log b - log a` for `0 < a ≤ b`. -/
theorem realMultHaar_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    realMultHaar (Icc a b) = ENNReal.ofReal (Real.log b - Real.log a) := by
  have hsub : Icc a b ⊆ Ioi 0 := fun _ ht ↦ ha.trans_le ht.1
  rw [← restrict_eq_self _ hsub, realMultHaar_restrict_Ioi, multHaar_Icc ha hab]

/-- `dx / |x|` gives the interval `[1, e]` mass one. -/
@[simp]
theorem realMultHaar_Icc_one_exp_one : realMultHaar (Icc 1 (Real.exp 1)) = 1 := by
  rw [realMultHaar_Icc one_pos (Real.one_le_exp zero_le_one), Real.log_exp, Real.log_one,
    sub_zero, ENNReal.ofReal_one]

/-- `2 dx dy / (x² + y²)` gives the annulus `a ≤ |z| ≤ b` mass `2 · 2π · (log b - log a)` for
`0 < a ≤ b`. -/
theorem complexMultHaar_setOf_norm_mem_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    complexMultHaar {z | ‖z‖ ∈ Icc a b} = ENNReal.ofReal (4 * π * (Real.log b - Real.log a)) := by
  have hsub : Icc a b ⊆ Ioi 0 := fun _ ht ↦ ha.trans_le ht.1
  have hm : MeasurableSet {z : ℂ | ‖z‖ ∈ Icc a b} :=
    measurableSet_Icc.preimage continuous_norm.measurable
  -- The integrand is constant on each circle about `0`: there it is `2 / ρ ^ 2` for `ρ ∈ [a, b]`,
  -- so its circle integral is `2πρ · 2 / ρ ^ 2 = 4π / ρ`.
  have hcircle : ∀ ρ ∈ Ioi (0 : ℝ), circleLIntegral
      ({z : ℂ | ‖z‖ ∈ Icc a b}.indicator fun z ↦ ENNReal.ofReal (2 * (‖z‖ ^ 2)⁻¹)) 0 ρ =
        (Icc a b).indicator (fun r ↦ ENNReal.ofReal (4 * π) * ENNReal.ofReal r⁻¹) ρ := by
    intro ρ hρ
    have hρ : 0 < ρ := hρ
    rw [circleLIntegral_congr (h := fun _ ↦ (Icc a b).indicator
      (fun r ↦ ENNReal.ofReal (2 * (r ^ 2)⁻¹)) ρ) 0 ρ fun _ z hz ↦ by
        simp only [indicator_apply, mem_ofPred_eq, mem_sphere_zero_iff_norm.mp hz],
      circleLIntegral_const]
    by_cases h : ρ ∈ Icc a b
    · rw [indicator_of_mem h, indicator_of_mem h, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    · simp [h]
  calc complexMultHaar {z | ‖z‖ ∈ Icc a b}
      = ∫⁻ ρ in Ioi 0, circleLIntegral ({z : ℂ | ‖z‖ ∈ Icc a b}.indicator
          fun z ↦ ENNReal.ofReal (2 * (‖z‖ ^ 2)⁻¹)) 0 ρ := by
        rw [complexMultHaar_def, withDensity_apply _ hm, ← lintegral_indicator hm,
          ← lintegral_circleLIntegral_eq_lintegral (Measurable.indicator (by fun_prop) hm) 0]
    _ = ∫⁻ ρ in Icc a b, ENNReal.ofReal (4 * π) * ENNReal.ofReal ρ⁻¹ := by
        rw [setLIntegral_congr_fun measurableSet_Ioi hcircle, lintegral_indicator measurableSet_Icc,
          restrict_restrict measurableSet_Icc,
          inter_eq_self_of_subset_left hsub]
    _ = ENNReal.ofReal (4 * π * (Real.log b - Real.log a)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_Icc_ofReal_inv ha hab,
          ← ENNReal.ofReal_mul (by positivity)]

/-- **The annulus Check.** `2 dx dy / (x² + y²)` gives the annulus `1 ≤ |z| ≤ e` mass
`2 · 2π · log e = 4π`. -/
theorem complexMultHaar_setOf_norm_mem_Icc_one_exp_one :
    complexMultHaar {z | ‖z‖ ∈ Icc 1 (Real.exp 1)} = ENNReal.ofReal (4 * π) := by
  rw [complexMultHaar_setOf_norm_mem_Icc one_pos (Real.one_le_exp zero_le_one), Real.log_exp,
    Real.log_one, sub_zero, mul_one]

end TauCeti
