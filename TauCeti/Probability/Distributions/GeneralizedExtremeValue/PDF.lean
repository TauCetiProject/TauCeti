/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Basic
public import TauCeti.Probability.Distributions.Gumbel.PDF
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Distributions.GeneralizedPareto.Basic

/-!
# Generalized extreme-value densities

For positive scale `s` and nonzero shape `ξ`, the generalized extreme-value law has density

`t ^ (-ξ⁻¹ - 1) * exp (-(t ^ (-ξ⁻¹))) / s`,

where `t = 1 + ξ * ((x - m) / s)` is positive. At shape zero this is the Gumbel density.
The density is zero outside the open support and at nonpositive scale.

This file derives the measure identity from the standard Gumbel law through the generalized
Pareto transformation. It supplies the density, `HasPDF`, Radon–Nikodym, and exact topological
support interfaces for the generalized extreme-value family.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {m s ξ x : ℝ}

/-! ### Densities -/

/-- The real density of a generalized extreme-value law, zero outside its open support and at
nonpositive scale. Shape zero uses the Gumbel density. -/
def generalizedExtremeValuePDFReal (m s ξ x : ℝ) : ℝ :=
  if ξ = 0 then gumbelPDFReal m s x
  else if 0 < s ∧ 0 < 1 + ξ * ((x - m) / s) then
    let t := 1 + ξ * ((x - m) / s)
    t ^ (-ξ⁻¹ - 1) * Real.exp (-(t ^ (-ξ⁻¹))) / s
  else 0

/-- The extended nonnegative density of a generalized extreme-value law. -/
def generalizedExtremeValuePDF (m s ξ x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (generalizedExtremeValuePDFReal m s ξ x)

/-- The extended density is obtained from the real density by `ENNReal.ofReal`. -/
theorem generalizedExtremeValuePDF_eq_ofReal (m s ξ x : ℝ) :
    generalizedExtremeValuePDF m s ξ x =
      ENNReal.ofReal (generalizedExtremeValuePDFReal m s ξ x) :=
  (rfl)

/-- At shape zero, the real generalized extreme-value density is the Gumbel density. -/
@[simp]
theorem generalizedExtremeValuePDFReal_zero (m s x : ℝ) :
    generalizedExtremeValuePDFReal m s 0 x = gumbelPDFReal m s x := by
  simp [generalizedExtremeValuePDFReal]

/-- At shape zero, the extended generalized extreme-value density is the Gumbel density. -/
@[simp]
theorem generalizedExtremeValuePDF_zero (m s x : ℝ) :
    generalizedExtremeValuePDF m s 0 x = gumbelPDF m s x := by
  rw [generalizedExtremeValuePDF, generalizedExtremeValuePDFReal_zero,
    ← gumbelPDF_eq_ofReal]

/-- The real generalized extreme-value density vanishes at nonpositive scale. -/
@[simp]
theorem generalizedExtremeValuePDFReal_of_scale_nonpos (hs : s ≤ 0) (m ξ x : ℝ) :
    generalizedExtremeValuePDFReal m s ξ x = 0 := by
  by_cases hξ : ξ = 0
  · subst ξ
    rw [generalizedExtremeValuePDFReal_zero, gumbelPDFReal_of_nonpos hs]
  · simp [generalizedExtremeValuePDFReal, hξ, not_lt.mpr hs]

/-- The extended generalized extreme-value density vanishes at nonpositive scale. -/
@[simp]
theorem generalizedExtremeValuePDF_of_scale_nonpos (hs : s ≤ 0) (m ξ x : ℝ) :
    generalizedExtremeValuePDF m s ξ x = 0 := by
  simp [generalizedExtremeValuePDF, generalizedExtremeValuePDFReal_of_scale_nonpos hs]

/-- On its open support, the nonzero-shape density has the classical formula. -/
theorem generalizedExtremeValuePDFReal_of_shape_ne_zero (hξ : ξ ≠ 0) (hs : 0 < s)
    (hx : 0 < 1 + ξ * ((x - m) / s)) :
    generalizedExtremeValuePDFReal m s ξ x =
      (1 + ξ * ((x - m) / s)) ^ (-ξ⁻¹ - 1) *
        Real.exp (-((1 + ξ * ((x - m) / s)) ^ (-ξ⁻¹))) / s := by
  simp [generalizedExtremeValuePDFReal, hξ, hs, hx]

/-- The real density vanishes outside the open support at nonzero shape. -/
theorem generalizedExtremeValuePDFReal_of_shape_ne_zero_of_not_pos (hξ : ξ ≠ 0)
    (hx : ¬0 < 1 + ξ * ((x - m) / s)) : generalizedExtremeValuePDFReal m s ξ x = 0 := by
  simp [generalizedExtremeValuePDFReal, hξ, hx]

/-- The real generalized extreme-value density is nonnegative for all parameters. -/
theorem generalizedExtremeValuePDFReal_nonneg (m s ξ x : ℝ) :
    0 ≤ generalizedExtremeValuePDFReal m s ξ x := by
  by_cases hξ : ξ = 0
  · simp [hξ, gumbelPDFReal_nonneg]
  · unfold generalizedExtremeValuePDFReal
    simp only [hξ, ↓reduceIte]
    split_ifs with h
    · exact div_nonneg (mul_nonneg (Real.rpow_nonneg h.2.le _) (Real.exp_pos _).le) h.1.le
    · exact le_rfl

/-- At positive scale, the density is positive exactly at every point for shape zero and on the
open support for nonzero shape. -/
@[simp]
theorem generalizedExtremeValuePDFReal_pos_iff (hs : 0 < s) :
    0 < generalizedExtremeValuePDFReal m s ξ x ↔
      ξ = 0 ∨ 0 < 1 + ξ * ((x - m) / s) := by
  by_cases hξ : ξ = 0
  · simp [hξ, gumbelPDFReal_pos hs]
  · rw [generalizedExtremeValuePDFReal]
    simp only [hξ, ↓reduceIte, false_or]
    split_ifs with h
    · exact iff_of_true (div_pos (mul_pos (Real.rpow_pos_of_pos h.2 _)
        (Real.exp_pos _)) hs) h.2
    · simpa [hs] using h

/-- At positive scale, the extended density is positive exactly at every point for shape zero
and on the open support for nonzero shape. -/
@[simp]
theorem generalizedExtremeValuePDF_pos_iff (hs : 0 < s) :
    0 < generalizedExtremeValuePDF m s ξ x ↔
      ξ = 0 ∨ 0 < 1 + ξ * ((x - m) / s) := by
  rw [generalizedExtremeValuePDF_eq_ofReal, ENNReal.ofReal_pos,
    generalizedExtremeValuePDFReal_pos_iff hs]

/-- Converting the extended density back to `ℝ` recovers the real density. -/
@[simp]
theorem toReal_generalizedExtremeValuePDF (m s ξ x : ℝ) :
    (generalizedExtremeValuePDF m s ξ x).toReal =
      generalizedExtremeValuePDFReal m s ξ x := by
  rw [generalizedExtremeValuePDF, ENNReal.toReal_ofReal
    (generalizedExtremeValuePDFReal_nonneg m s ξ x)]

/-- The extended generalized extreme-value density is finite everywhere. -/
@[simp]
theorem generalizedExtremeValuePDF_ne_top (m s ξ x : ℝ) :
    generalizedExtremeValuePDF m s ξ x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The real generalized extreme-value density is jointly measurable in all four inputs. -/
@[fun_prop]
theorem measurable_uncurry_generalizedExtremeValuePDFReal :
    Measurable fun q : ((ℝ × ℝ) × ℝ) × ℝ ↦
      generalizedExtremeValuePDFReal q.1.1.1 q.1.1.2 q.1.2 q.2 := by
  unfold generalizedExtremeValuePDFReal
  apply Measurable.ite (by measurability)
  · exact measurable_uncurry_gumbelPDFReal.comp
      (((measurable_fst.fst.fst.prodMk measurable_fst.fst.snd).prodMk measurable_snd))
  · apply Measurable.ite (by measurability) <;> fun_prop

/-- The extended generalized extreme-value density is jointly measurable in all four inputs. -/
@[fun_prop]
theorem measurable_uncurry_generalizedExtremeValuePDF :
    Measurable fun q : ((ℝ × ℝ) × ℝ) × ℝ ↦
      generalizedExtremeValuePDF q.1.1.1 q.1.1.2 q.1.2 q.2 :=
  measurable_uncurry_generalizedExtremeValuePDFReal.ennreal_ofReal

/-- The real generalized extreme-value density is measurable in its argument. -/
@[fun_prop]
theorem measurable_generalizedExtremeValuePDFReal (m s ξ : ℝ) :
    Measurable (generalizedExtremeValuePDFReal m s ξ) :=
  measurable_uncurry_generalizedExtremeValuePDFReal.comp
    (measurable_prodMk_left (x := ((m, s), ξ)))

/-- The extended generalized extreme-value density is measurable in its argument. -/
@[fun_prop]
theorem measurable_generalizedExtremeValuePDF (m s ξ : ℝ) :
    Measurable (generalizedExtremeValuePDF m s ξ) :=
  (measurable_generalizedExtremeValuePDFReal m s ξ).ennreal_ofReal

/-! ### Density of the measure -/

private theorem generalizedExtremeValueMap_eq_add_generalizedParetoMap (m s ξ e : ℝ) :
    generalizedExtremeValueMap m s ξ e = m + generalizedParetoMap s ξ (-Real.log e) := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [generalizedExtremeValueMap_zero, generalizedParetoMap_zero]
    ring
  · rw [generalizedExtremeValueMap_of_shape_ne_zero hξ,
      generalizedParetoMap_of_shape_ne_zero hξ]
    ring_nf

private theorem one_add_mul_add_generalizedParetoMap_sub_div (hs : s ≠ 0) (_hξ : ξ ≠ 0)
    (m y : ℝ) :
    1 + ξ * ((m + generalizedParetoMap s ξ y - m) / s) = Real.exp (ξ * y) := by
  rw [add_sub_cancel_left]
  convert one_add_mul_generalizedParetoMap_div hs ξ y using 1
  ring

private theorem image_add_generalizedParetoMap_univ (hs : 0 < s) (hξ : ξ ≠ 0) (m : ℝ) :
    (fun y ↦ m + generalizedParetoMap s ξ y) '' univ =
      {x | 0 < 1 + ξ * ((x - m) / s)} := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    rw [Set.mem_ofPred_eq, one_add_mul_add_generalizedParetoMap_sub_div hs.ne' hξ]
    exact Real.exp_pos _
  · intro hx
    have hx' : 0 < 1 + ξ * ((x - m) / s) := hx
    have hlog : Real.exp (Real.log (1 + ξ * ((x - m) / s))) =
        1 + ξ * ((x - m) / s) := Real.exp_log hx'
    refine ⟨Real.log (1 + ξ * ((x - m) / s)) / ξ, Set.mem_univ _, ?_⟩
    dsimp only
    rw [generalizedParetoMap_of_shape_ne_zero hξ, mul_div_cancel₀ _ hξ, hlog]
    field_simp [hs.ne', hξ]
    ring

private theorem transform_weight (hs : 0 < s) (hξ : ξ ≠ 0) (m y : ℝ) :
    ENNReal.ofReal |s * Real.exp (ξ * y)| *
        generalizedExtremeValuePDF m s ξ (m + generalizedParetoMap s ξ y) =
      gumbelPDF 0 1 y := by
  have ht := one_add_mul_add_generalizedParetoMap_sub_div hs.ne' hξ m y
  rw [generalizedExtremeValuePDF_eq_ofReal,
    generalizedExtremeValuePDFReal_of_shape_ne_zero hξ hs (ht ▸ Real.exp_pos _),
    gumbelPDF_of_pos one_pos, sub_zero, div_one, abs_of_pos (mul_pos hs (Real.exp_pos _)),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [ht, ← Real.exp_mul]
  have hexp : ξ * y * (-ξ⁻¹) = -y := by field_simp
  have hpow : Real.exp (ξ * y) ^ (-ξ⁻¹) = Real.exp (-y) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, hexp]
  have hexp' : ξ * y * (-ξ⁻¹ - 1) = -y - ξ * y := by field_simp
  rw [hpow, hexp', Real.exp_sub]
  simp only [div_one]
  field_simp [Real.exp_ne_zero]

/-- The generalized extreme-value law is Lebesgue measure weighted by its named density, at
every parameter value. -/
theorem generalizedExtremeValueMeasure_eq_withDensity (m s ξ : ℝ) :
    generalizedExtremeValueMeasure m s ξ =
      volume.withDensity (generalizedExtremeValuePDF m s ξ) := by
  rcases le_or_gt s 0 with hs | hs
  · have hpdf : generalizedExtremeValuePDF m s ξ = 0 := funext fun x ↦ by
      rw [generalizedExtremeValuePDF_of_scale_nonpos hs, Pi.zero_apply]
    rw [generalizedExtremeValueMeasure_of_nonpos hs, hpdf, withDensity_zero]
  · by_cases hξ : ξ = 0
    · subst ξ
      rw [generalizedExtremeValueMeasure_zero, funext (generalizedExtremeValuePDF_zero m s),
        gumbelMeasure_eq_withDensity]
    · let φ : ℝ → ℝ := fun y ↦ m + generalizedParetoMap s ξ y
      have hmap := TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul
        (s := univ) (φ := φ) (φ' := fun y ↦ s * Real.exp (ξ * y))
        (f := generalizedExtremeValuePDF m s ξ) MeasurableSet.univ (by fun_prop)
        (fun y _ ↦ (hasDerivAt_generalizedParetoMap s ξ y).const_add m |>.hasDerivWithinAt)
        ((strictMono_generalizedParetoMap hs ξ).const_add m).injective.injOn
      have hw : (fun y ↦ ENNReal.ofReal |s * Real.exp (ξ * y)| *
          generalizedExtremeValuePDF m s ξ (φ y)) =ᵐ[volume.restrict univ]
            gumbelPDF 0 1 := by
        filter_upwards with y
        exact transform_weight hs hξ m y
      rw [withDensity_congr_ae hw, image_add_generalizedParetoMap_univ hs hξ m,
        Measure.restrict_univ] at hmap
      have hgev : generalizedExtremeValueMap m s ξ =
          φ ∘ fun e : ℝ ↦ -Real.log e := by
        funext e
        exact generalizedExtremeValueMap_eq_add_generalizedParetoMap m s ξ e
      have hgumbel : gumbelMeasure 0 1 =
          (expMeasure 1).map (fun e : ℝ ↦ -Real.log e) := by
        simpa only [zero_sub, one_mul] using gumbelMeasure_of_pos one_pos 0
      rw [generalizedExtremeValueMeasure_of_pos hs, hgev,
        ← Measure.map_map (by fun_prop : Measurable φ)
          (by fun_prop : Measurable fun e : ℝ ↦ -Real.log e),
        ← hgumbel, gumbelMeasure_eq_withDensity, hmap,
        ← withDensity_indicator (by measurability)]
      congr 1
      ext z
      by_cases hz : 0 < 1 + ξ * ((z - m) / s)
      · simp [hz]
      · simp [hz, generalizedExtremeValuePDF,
          generalizedExtremeValuePDFReal_of_shape_ne_zero_of_not_pos hξ hz]

/-- The extended generalized extreme-value density has total mass one at positive scale. -/
theorem lintegral_generalizedExtremeValuePDF_eq_one (hs : 0 < s) (m ξ : ℝ) :
    ∫⁻ x, generalizedExtremeValuePDF m s ξ x = 1 := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  have h : generalizedExtremeValueMeasure m s ξ univ = 1 := measure_univ
  rwa [generalizedExtremeValueMeasure_eq_withDensity,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with generalized extreme-value law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_generalizedExtremeValueMeasure
    (hX : HasLaw X (generalizedExtremeValueMeasure m s ξ) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_generalizedExtremeValuePDF m s ξ).aemeasurable
    (by rwa [generalizedExtremeValueMeasure_eq_withDensity] at hX)

/-- The canonical density of a random variable with generalized extreme-value law is its named
density. -/
theorem pdf_eq_generalizedExtremeValuePDF_of_hasLaw_generalizedExtremeValueMeasure
    (hX : HasLaw X (generalizedExtremeValueMeasure m s ξ) P) :
    pdf X P volume =ᵐ[volume] generalizedExtremeValuePDF m s ξ :=
  pdf_eq_of_hasLaw_withDensity (measurable_generalizedExtremeValuePDF m s ξ).aemeasurable
    (by rwa [generalizedExtremeValueMeasure_eq_withDensity] at hX)

/-- The Radon–Nikodym derivative of a generalized extreme-value law is its named density. -/
theorem rnDeriv_generalizedExtremeValueMeasure (m s ξ : ℝ) :
    (generalizedExtremeValueMeasure m s ξ).rnDeriv volume =ᵐ[volume]
      generalizedExtremeValuePDF m s ξ := by
  rw [generalizedExtremeValueMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_generalizedExtremeValuePDF m s ξ)

/-! ### Topological support -/

/-- At positive scale and positive shape, the open support begins at the finite lower endpoint. -/
theorem setOf_generalizedExtremeValue_pos_eq_Ioi (hs : 0 < s) (hξ : 0 < ξ) :
    {x : ℝ | 0 < 1 + ξ * ((x - m) / s)} = Ioi (m - s / ξ) := by
  have hfactor (x : ℝ) :
      1 + ξ * ((x - m) / s) = (ξ / s) * (x - (m - s / ξ)) := by
    field_simp [hs.ne', hξ.ne']
    ring
  ext x
  rw [Set.mem_ofPred_eq, mem_Ioi, hfactor,
    mul_pos_iff_of_pos_left (div_pos hξ hs), sub_pos]

/-- At positive scale and negative shape, the open support ends at the finite upper endpoint. -/
theorem setOf_generalizedExtremeValue_neg_eq_Iio (hs : 0 < s) (hξ : ξ < 0) :
    {x : ℝ | 0 < 1 + ξ * ((x - m) / s)} = Iio (m - s / ξ) := by
  have hfactor (x : ℝ) :
      1 + ξ * ((x - m) / s) = (ξ / s) * (x - (m - s / ξ)) := by
    field_simp [hs.ne', hξ.ne]
    ring
  ext x
  rw [Set.mem_ofPred_eq, mem_Iio, hfactor, mul_pos_iff]
  have hneg : ξ / s < 0 := div_neg_of_neg_of_pos hξ hs
  have hnot : ¬0 < ξ / s := not_lt.mpr (le_of_lt hneg)
  simp only [hnot, false_and, hneg, true_and, false_or, sub_neg]

/-- At positive scale, the function support of the generalized extreme-value density is all of
`ℝ` at shape zero and the natural open support at nonzero shape. -/
@[simp]
theorem support_generalizedExtremeValuePDF (hs : 0 < s) (m ξ : ℝ) :
    Function.support (generalizedExtremeValuePDF m s ξ) =
      if ξ = 0 then univ else {x | 0 < 1 + ξ * ((x - m) / s)} := by
  ext x
  rw [Function.mem_support, ← pos_iff_ne_zero,
    generalizedExtremeValuePDF_pos_iff hs]
  split_ifs with hξ
  · simp [hξ]
  · simp [hξ]

/-- A positive-scale generalized extreme-value law has full support at shape zero, a closed
lower half-line at positive shape, and a closed upper half-line at negative shape. -/
theorem support_generalizedExtremeValueMeasure (hs : 0 < s) (m ξ : ℝ) :
    (generalizedExtremeValueMeasure m s ξ).support =
      if ξ = 0 then univ else if 0 < ξ then Ici (m - s / ξ) else Iic (m - s / ξ) := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [support_gumbelMeasure hs]
  · have hopen : IsOpen {x : ℝ | 0 < 1 + ξ * ((x - m) / s)} := by
      exact isOpen_lt continuous_const
        (continuous_const.add (continuous_const.mul
          ((continuous_id.sub continuous_const).div_const s)))
    rw [generalizedExtremeValueMeasure_eq_withDensity,
      Measure.support_withDensity_eq_closure
        (measurable_generalizedExtremeValuePDF m s ξ) hopen
        (by rw [support_generalizedExtremeValuePDF hs m ξ, ite_eq_right hξ]),
      ite_eq_right hξ]
    rcases lt_or_gt_of_ne hξ with hξneg | hξpos
    · rw [ite_eq_right (not_lt.mpr (le_of_lt hξneg)),
        setOf_generalizedExtremeValue_neg_eq_Iio hs hξneg,
        closure_Iio]
    · rw [ite_eq_left hξpos, setOf_generalizedExtremeValue_pos_eq_Ioi hs hξpos,
        closure_Ioi]

/-- A nonpositive scale gives the zero measure and hence empty topological support. -/
theorem support_generalizedExtremeValueMeasure_of_nonpos (hs : s ≤ 0) (m ξ : ℝ) :
    (generalizedExtremeValueMeasure m s ξ).support = ∅ := by
  rw [generalizedExtremeValueMeasure_of_nonpos hs, Measure.support_zero]

end TauCeti.Probability
