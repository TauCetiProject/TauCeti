/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.DistribChar
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
public import TauCeti.MeasureTheory.Constructions.Polish.Units
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Group.Units
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
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

Their pullbacks along `Units.val` are the Haar measures `TauCeti.realUnitsMultHaar` on `ℝˣ` and
`TauCeti.complexUnitsMultHaar` on `ℂˣ`. Since `0` is null, integrals of functions of `x : ℝ` or
`z : ℂ` over the units are the integrals over `ℝ` or `ℂ` (`TauCeti.integral_realUnitsMultHaar`,
`TauCeti.integral_complexUnitsMultHaar`). Radial integrals reduce to `dt / t` on `(0, ∞)`: by
`2` on `ℝ` (`TauCeti.integral_realMultHaar_comp_abs`) and by the annulus mass `4π` on `ℂ`
(`TauCeti.integral_complexMultHaar_comp_norm`).

For a finite type `Φ`, the product of the measures `2 dx dy / (x² + y²)` on `ℂ^Φ` is carried by
its units `(ℂ^Φ)ˣ = (ℂˣ)^Φ` (`TauCeti.ae_isUnit_pi_complexMultHaar`).

On `ℂ` there is more: in polar coordinates `2 dx dy / (x² + y²)` is `2 dr dθ / r`
(`TauCeti.complexMultHaar_eq_smul_map_circleMap`), so, integrating out the angle, its image
under `z ↦ |z|` is `4π dt / t`
(`TauCeti.lintegral_complexMultHaar_comp_norm`, `TauCeti.map_norm_complexMultHaar`). So a radial
function `z ↦ h |z|` is a.e. strongly measurable, or integrable, for it exactly when `h` is so
for `dt / t` (`TauCeti.aestronglyMeasurable_complexMultHaar_comp_norm_iff`,
`TauCeti.integrable_complexMultHaar_comp_norm_iff`).

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

/-! ### The multiplicative Haar measures on the units of `ℝ` and `ℂ` -/

/-- The multiplicative Haar measure `dx / |x|` of `ℝˣ`: the pullback of `TauCeti.realMultHaar`
along `ℝˣ → ℝ`. -/
noncomputable def realUnitsMultHaar : Measure ℝˣ :=
  realMultHaar.comap Units.val

/-- The defining formula of `dx / |x|` on `ℝˣ`. -/
theorem realUnitsMultHaar_def : realUnitsMultHaar = realMultHaar.comap Units.val := (rfl)

/-- The pushforward of `dx / |x|` on `ℝˣ` to `ℝ` is `TauCeti.realMultHaar`. -/
theorem map_val_realUnitsMultHaar : realUnitsMultHaar.map Units.val = realMultHaar :=
  Units.map_val_comap_val

/-- The multiplicative Haar measure `2 dx dy / |z|_ℂ` of `ℂˣ`: the pullback of
`TauCeti.complexMultHaar` along `ℂˣ → ℂ`. -/
noncomputable def complexUnitsMultHaar : Measure ℂˣ :=
  complexMultHaar.comap Units.val

/-- The defining formula of `2 dx dy / |z|_ℂ` on `ℂˣ`. -/
theorem complexUnitsMultHaar_def : complexUnitsMultHaar = complexMultHaar.comap Units.val := (rfl)

/-- The pushforward of `2 dx dy / |z|_ℂ` on `ℂˣ` to `ℂ` is `TauCeti.complexMultHaar`. -/
theorem map_val_complexUnitsMultHaar : complexUnitsMultHaar.map Units.val = complexMultHaar :=
  Units.map_val_comap_val

/-- The product of the measures `2 dx dy / (x² + y²)` on `ℂ^Φ` is carried by its units
`(ℂ^Φ)ˣ = (ℂˣ)^Φ`. -/
theorem ae_isUnit_pi_complexMultHaar {Φ : Type*} [Fintype Φ] :
    ∀ᵐ a ∂Measure.pi fun _ : Φ ↦ complexMultHaar, IsUnit a := by
  filter_upwards [Filter.eventually_all.2 fun τ ↦ ae_eval_ne (fun _ : Φ ↦ complexMultHaar) τ 0]
    with a ha
  exact Pi.isUnit_iff.2 fun τ ↦ (ha τ).isUnit

section UnitsIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrating a function of `x : ℝ` against `dx / |x|` over `ℝˣ` is integrating it against
`TauCeti.realMultHaar` over `ℝ`. -/
theorem integral_realUnitsMultHaar (g : ℝ → E) :
    ∫ x : ℝˣ, g x ∂realUnitsMultHaar = ∫ y, g y ∂realMultHaar :=
  Units.integral_comap_val g

omit [NormedSpace ℝ E] in
/-- A function of `x : ℝ` is integrable against `dx / |x|` over `ℝˣ` exactly when it is
integrable against `TauCeti.realMultHaar` over `ℝ`. -/
theorem integrable_realUnitsMultHaar_iff {g : ℝ → E} :
    Integrable (fun x : ℝˣ ↦ g x) realUnitsMultHaar ↔ Integrable g realMultHaar :=
  Units.integrable_comap_val_iff

/-- Integrating a function of `z : ℂ` against `2 dx dy / |z|_ℂ` over `ℂˣ` is integrating it
against `TauCeti.complexMultHaar` over `ℂ`. -/
theorem integral_complexUnitsMultHaar (g : ℂ → E) :
    ∫ z : ℂˣ, g z ∂complexUnitsMultHaar = ∫ w, g w ∂complexMultHaar :=
  Units.integral_comap_val g

omit [NormedSpace ℝ E] in
/-- A function of `z : ℂ` is integrable against `2 dx dy / |z|_ℂ` over `ℂˣ` exactly when it is
integrable against `TauCeti.complexMultHaar` over `ℂ`. -/
theorem integrable_complexUnitsMultHaar_iff {g : ℂ → E} :
    Integrable (fun z : ℂˣ ↦ g z) complexUnitsMultHaar ↔ Integrable g complexMultHaar :=
  Units.integrable_comap_val_iff

end UnitsIntegral

instance : realUnitsMultHaar.IsMulLeftInvariant :=
  Units.isMulLeftInvariant_comap_val fun b ↦ map_realMultHaar_mul_left b.ne_zero

instance : complexUnitsMultHaar.IsMulLeftInvariant :=
  Units.isMulLeftInvariant_comap_val fun b ↦ map_complexMultHaar_mul_left b.ne_zero

instance : realUnitsMultHaar.IsHaarMeasure := by
  have : IsFiniteMeasureOnCompacts realUnitsMultHaar := by
    rw [realUnitsMultHaar_def, realMultHaar_def]
    exact Units.isFiniteMeasureOnCompacts_comap_val_withDensity volume
      (continuous_abs.continuousOn.inv₀ fun x hx ↦ abs_ne_zero.2 hx)
  have : realUnitsMultHaar.IsOpenPosMeasure := by
    rw [realUnitsMultHaar_def, realMultHaar_def]
    exact Units.isOpenPosMeasure_comap_val_withDensity volume continuous_abs.measurable.inv
      fun x hx ↦ inv_pos.2 (abs_pos.2 hx)
  exact {}

instance : complexUnitsMultHaar.IsHaarMeasure := by
  have : IsFiniteMeasureOnCompacts complexUnitsMultHaar := by
    rw [complexUnitsMultHaar_def, complexMultHaar_def]
    exact Units.isFiniteMeasureOnCompacts_comap_val_withDensity volume
      (continuousOn_const.mul ((continuous_norm.pow 2).continuousOn.inv₀ fun z hz ↦
        pow_ne_zero 2 (norm_ne_zero_iff.2 hz)))
  have : complexUnitsMultHaar.IsOpenPosMeasure := by
    rw [complexUnitsMultHaar_def, complexMultHaar_def]
    exact Units.isOpenPosMeasure_comap_val_withDensity volume
      (measurable_const.mul (measurable_norm.pow_const 2).inv)
      fun z hz ↦ mul_pos two_pos (inv_pos.2 (pow_pos (norm_pos_iff.2 hz) 2))
  exact {}

/-! ### Radial integrals -/

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A radial integral against `dx / |x|` is twice the corresponding integral against `dt / t`. -/
theorem integral_realMultHaar_comp_abs (G : ℝ → E) :
    ∫ y, G |y| ∂realMultHaar = (2 : ℝ) • ∫ t, G t ∂multHaar := by
  have h := integral_fun_norm_addHaar (volume : Measure ℝ) (fun r ↦ r⁻¹ • G r)
  simp only [Real.norm_eq_abs, Module.finrank_self, one_smul, pow_zero, tsub_self] at h
  rw [integral_realMultHaar, h, integral_multHaar_eq_setIntegral]
  norm_num

/-- A radial integral against `2 dx dy / |z|_ℂ` is `4π` times the corresponding integral against
`dt / t`. -/
theorem integral_complexMultHaar_comp_norm (G : ℝ → E) :
    ∫ z, G ‖z‖ ∂complexMultHaar = (4 * π) • ∫ t, G t ∂multHaar := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r ↦ (2 * (r ^ 2)⁻¹) • G r)
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    rw [Measure.real, Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
      ENNReal.coe_toReal, NNReal.coe_real_pi]
  have hint : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (2 * (y ^ 2)⁻¹) • G y =
      (2 : ℝ) • ∫ y in Ioi (0 : ℝ), y⁻¹ • G y := by
    rw [← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    simp only [smul_smul]
    congr 1
    field_simp
    ring
  rw [integral_complexMultHaar, h, integral_multHaar_eq_setIntegral, Complex.finrank_real_complex,
    hball, hint]
  module

/-- Polar coordinates as a product: `2 dx dy / (x² + y²)` is twice the image of
`dt / t ⊗ dθ` on `(0, ∞) × (-π, π)` under `(ρ, θ) ↦ ρ e^{iθ}`. -/
private theorem lintegral_complexMultHaar_eq_lintegral_prod {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z ∂complexMultHaar = ENNReal.ofReal 2 *
      ∫⁻ p, g (circleMap 0 p.1 p.2) ∂(multHaar.prod (volume.restrict (Ioo (-π) π))) := by
  have hc : Measurable fun p : ℝ × ℝ ↦ g (circleMap 0 p.1 p.2) :=
    hg.comp (continuous_circleMap_uncurry 0).measurable
  rw [lintegral_prod _ hc.aemeasurable, lintegral_multHaar_eq_setLIntegral,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_complexMultHaar,
    ← lintegral_circleLIntegral_eq_lintegral (by fun_prop) 0]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ρ (hρ : 0 < ρ) ↦ ?_
  have hnorm : ∀ θ, ‖circleMap 0 ρ θ‖ = ρ := fun θ ↦ by rw [norm_circleMap_zero, abs_of_pos hρ]
  simp only [circleLIntegral_def, hnorm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← mul_assoc,
    ← ENNReal.ofReal_mul hρ.le, ← ENNReal.ofReal_mul zero_le_two]
  congr 2
  field_simp

/-- **Polar coordinates for `2 dx dy / (x² + y²)`.** It is twice the image of the product measure
`dt / t ⊗ dθ` on `(0, ∞) × (-π, π)` under `(ρ, θ) ↦ ρ e^{iθ}`. -/
theorem complexMultHaar_eq_smul_map_circleMap :
    complexMultHaar = ENNReal.ofReal 2 •
      (multHaar.prod (volume.restrict (Ioo (-π) π))).map fun p ↦ circleMap 0 p.1 p.2 := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  rw [lintegral_smul_measure, lintegral_map hg (continuous_circleMap_uncurry 0).measurable,
    lintegral_complexMultHaar_eq_lintegral_prod hg, smul_eq_mul]

/-- In polar coordinates the norm is the radius, almost everywhere. -/
private theorem ae_norm_circleMap_eq_fst :
    ∀ᵐ p ∂multHaar.prod (volume.restrict (Ioo (-π) π)), ‖circleMap 0 p.1 p.2‖ = p.1 := by
  filter_upwards [quasiMeasurePreserving_fst.ae ae_pos_multHaar] with p hp
  rw [norm_circleMap_zero, abs_of_pos hp]

/-- `(ρ, θ) ↦ ρ e^{iθ}` is quasi-measure-preserving from `dt / t ⊗ dθ` on `(0, ∞) × (-π, π)`
to `2 dx dy / (x² + y²)`: the preimage of a `complexMultHaar`-null set is null. -/
private theorem quasiMeasurePreserving_circleMap_prod :
    QuasiMeasurePreserving (fun p : ℝ × ℝ ↦ circleMap 0 p.1 p.2)
      (multHaar.prod (volume.restrict (Ioo (-π) π))) complexMultHaar := by
  rw [complexMultHaar_eq_smul_map_circleMap]
  exact ((continuous_circleMap_uncurry 0).measurable.quasiMeasurePreserving _).mono_right
    (absolutelyContinuous_smul (by norm_num))

/-- **The radial part of `2 dx dy / (x² + y²)`.** Its image under `z ↦ |z|` is `4π dt / t`. -/
theorem map_norm_complexMultHaar :
    complexMultHaar.map (‖·‖) = ENNReal.ofReal (4 * π) • multHaar := by
  rw [complexMultHaar_eq_smul_map_circleMap, Measure.map_smul,
    map_map continuous_norm.measurable (continuous_circleMap_uncurry 0).measurable,
    map_congr (f := (‖·‖) ∘ fun p : ℝ × ℝ ↦ circleMap 0 p.1 p.2) (g := Prod.fst)
      ae_norm_circleMap_eq_fst, map_fst_prod, smul_smul,
    Measure.restrict_apply_univ, Real.volume_Ioo, ← ENNReal.ofReal_mul zero_le_two]
  · congr 2
    ring
  · exact continuous_norm.aemeasurable

/-- **Polar coordinates for `2 dx dy / (x² + y²)`.** The lower integral of a radial function
`z ↦ f |z|` is `4π` times the lower integral of `f` against `dt / t`. No measurability of `f` is
required. -/
theorem lintegral_complexMultHaar_comp_norm (f : ℝ → ℝ≥0∞) :
    ∫⁻ z, f ‖z‖ ∂complexMultHaar = ENNReal.ofReal (4 * π) * ∫⁻ t, f t ∂multHaar := by
  refine le_antisymm ?_ ?_
  · -- Through polar coordinates, where the integrand is `f ρ`, constant in the angle.
    calc ∫⁻ z, f ‖z‖ ∂complexMultHaar
        ≤ ENNReal.ofReal 2 *
          ∫⁻ p, f ‖circleMap 0 p.1 p.2‖ ∂(multHaar.prod (volume.restrict (Ioo (-π) π))) := by
          conv_lhs => rw [complexMultHaar_eq_smul_map_circleMap]
          rw [lintegral_smul_measure, smul_eq_mul]
          gcongr
          exact lintegral_map_le _ (continuous_circleMap_uncurry 0).measurable.aemeasurable
      _ = ENNReal.ofReal 2 *
          ∫⁻ p, f p.1 ∂(multHaar.prod (volume.restrict (Ioo (-π) π))) := by
          congr 1
          exact lintegral_congr_ae (ae_norm_circleMap_eq_fst.mono fun p hp ↦ by simp only [hp])
      _ ≤ ENNReal.ofReal 2 * ∫⁻ ρ, (∫⁻ _ in Ioo (-π) π, f ρ) ∂multHaar := by
          gcongr
          exact lintegral_prod_le _
      _ = ENNReal.ofReal (4 * π) * ∫⁻ t, f t ∂multHaar := by
          simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm (∫⁻ t, f t ∂multHaar),
            ← mul_assoc, ← ENNReal.ofReal_mul zero_le_two]
          congr 2
          ring
  · rw [← smul_eq_mul, ← lintegral_smul_measure, ← map_norm_complexMultHaar]
    exact lintegral_map_le _ continuous_norm.aemeasurable

/-- A radial function `z ↦ h |z|` is a.e. strongly measurable for `2 dx dy / (x² + y²)` exactly
when `h` is a.e. strongly measurable for `dt / t`. -/
@[simp]
theorem aestronglyMeasurable_complexMultHaar_comp_norm_iff {X : Type*} [TopologicalSpace X]
    {h : ℝ → X} :
    AEStronglyMeasurable (fun z ↦ h ‖z‖) complexMultHaar ↔ AEStronglyMeasurable h multHaar := by
  refine ⟨fun hh ↦ ?_, fun hh ↦ ?_⟩
  · -- In polar coordinates `(ρ, θ)` the function is `h ρ`, constant in the angle.
    refine AEStronglyMeasurable.of_comp_fst
      ((hh.comp_quasiMeasurePreserving quasiMeasurePreserving_circleMap_prod).congr
        (ae_norm_circleMap_eq_fst.mono fun p hp ↦ by simp only [Function.comp_apply, hp]))
      (by simp [Real.pi_pos])
  · exact (map_norm_complexMultHaar ▸ hh.smul_measure _).comp_aemeasurable
      continuous_norm.aemeasurable

/-- A radial function `z ↦ h |z|` is integrable against `2 dx dy / (x² + y²)` exactly when `h` is
integrable against `dt / t`. -/
@[simp]
theorem integrable_complexMultHaar_comp_norm_iff {ε : Type*} [TopologicalSpace ε]
    [ContinuousENorm ε] {h : ℝ → ε} :
    Integrable (fun z ↦ h ‖z‖) complexMultHaar ↔ Integrable h multHaar := by
  have hc : ENNReal.ofReal (4 * π) ≠ 0 := by positivity
  rw [Integrable, Integrable, aestronglyMeasurable_complexMultHaar_comp_norm_iff,
    hasFiniteIntegral_def, hasFiniteIntegral_def,
    lintegral_complexMultHaar_comp_norm fun t ↦ ‖h t‖ₑ, ENNReal.mul_lt_top_iff]
  simp only [ENNReal.ofReal_lt_top, true_and, hc, false_or]
  -- A zero lower integral is finite.
  refine and_congr_right fun _ ↦ or_iff_left_of_imp fun h0 ↦ ?_
  rw [h0]
  exact ENNReal.zero_lt_top

end Radial

end TauCeti
