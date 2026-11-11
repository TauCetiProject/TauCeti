/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.Area
public import TauCeti.Analysis.Fourier.IsoperimetricTrace
public import TauCeti.Analysis.Green.Examples.CurveArea.Jordan
public import TauCeti.MeasureTheory.Function.AreaFormula.Circle
public import TauCeti.Topology.JordanCurve.Length

/-!
# The isoperimetric inequality for planar Jordan curves

Let `C ⊆ ℂ` be a Jordan curve, with inside `Ω = filledHull C \ C`, area `A = volume Ω` and
length `L = μHE[1] C`, its one-dimensional Euclidean Hausdorff measure. The classical
**isoperimetric inequality** is

`4π A ≤ L²`,

with equality exactly when `C` is a circle of positive radius. In extended nonnegative reals
both statements hold for every Jordan curve
(`TauCeti.IsJordanCurve.ofReal_four_pi_mul_volume_filledHull_sdiff_le` and
`TauCeti.IsJordanCurve.ofReal_four_pi_mul_volume_filledHull_sdiff_eq_iff`). A non-rectifiable
Jordan curve has `L = ∞` while its inside has finite area, so the inequality is strict for it.
The real forms assume rectifiability, `L < ∞`
(`TauCeti.IsJordanCurve.four_pi_mul_volume_real_filledHull_sdiff_le` and
`TauCeti.IsJordanCurve.four_pi_mul_volume_real_filledHull_sdiff_eq_iff`). The equality case is
literal equality of `C` with a circle, not equality up to null sets.

The same statements hold for a parametrized curve: a continuous `γ : ℝ → ℂ` on `[a, b]`,
`a < b`, with `γ a = γ b`, injective on `[a, b)` and of bounded variation on `[a, b]`, whose trace
`γ '' Icc a b` replaces `C` and whose total variation `eVariationOn γ (Icc a b)` replaces `L`
(`BoundedVariationOn.four_pi_mul_volume_real_filledHull_sdiff_le` and
`BoundedVariationOn.four_pi_mul_volume_real_filledHull_sdiff_eq_iff`). The parametrization need
not be absolutely continuous, Lipschitz or differentiable. The two formulations agree:
rectifiable Jordan curves are exactly the traces of such curves
(`TauCeti.isJordanCurve_and_hausdorffMeasure_lt_top_iff`), and the total variation of such a
curve is the length of its trace
(`ContinuousOn.eVariationOn_eq_euclideanHausdorffMeasure_image`).

The area of the inside is the absolute value of the geometric signed area of the curve
(`BoundedVariationOn.abs_rectifiableSignedArea_eq_volume_real`, from the Jordan index theorem).
So the inequality is the length–signed-area inequality
`TauCeti.four_pi_mul_abs_rectifiableSignedArea_le`, and the equality case is the circular-trace
theorem for that inequality, `BoundedVariationOn.exists_image_eq_sphere_of_isoperimetric_eq`.

For a simple closed absolutely continuous curve with square-integrable derivative `γ'`, the same
inside satisfies the area–energy form `4π A ≤ (b - a) ∫ₐᵇ ‖γ'‖²`, with equality exactly for a
circle traversed once at constant angular speed
(`AbsolutelyContinuousOnInterval.four_pi_mul_volume_real_filledHull_sdiff_le` and
`AbsolutelyContinuousOnInterval.four_pi_mul_volume_real_filledHull_sdiff_eq_iff`). For an
arclength parametrization the energy term is `L²`, which recovers the inequality above.

## Main results

* `AbsolutelyContinuousOnInterval.four_pi_mul_volume_real_filledHull_sdiff_le` and
  `AbsolutelyContinuousOnInterval.four_pi_mul_volume_real_filledHull_sdiff_eq_iff`: the area–energy
  inequality and its equality case for the inside of a simple closed absolutely continuous curve.
* `BoundedVariationOn.four_pi_mul_volume_real_filledHull_sdiff_le` and
  `BoundedVariationOn.four_pi_mul_volume_real_filledHull_sdiff_eq_iff`: the inequality and its
  equality case for a parametrized rectifiable simple closed curve.
* `TauCeti.IsJordanCurve.four_pi_mul_volume_real_filledHull_sdiff_le` and
  `TauCeti.IsJordanCurve.four_pi_mul_volume_real_filledHull_sdiff_eq_iff`: the same for a
  rectifiable Jordan curve.
* `TauCeti.IsJordanCurve.ofReal_four_pi_mul_volume_filledHull_sdiff_le` and
  `TauCeti.IsJordanCurve.ofReal_four_pi_mul_volume_filledHull_sdiff_eq_iff`: the same in `ℝ≥0∞`
  for every Jordan curve.

## References

* A. Hurwitz, *Sur quelques applications géométriques des séries de Fourier*, Ann. Sci. École
  Norm. Sup. (3) **19** (1902), 357–408, for the Fourier-series proof of the inequality.
* R. Osserman, *The isoperimetric inequality*, Bull. Amer. Math. Soc. **84** (1978), 1182–1238,
  for the statement for rectifiable Jordan curves and its equality case.
-/

public section

open Complex MeasureTheory Metric Set
open scoped ENNReal Real

namespace AbsolutelyContinuousOnInterval

variable {γ γ' : ℝ → ℂ} {a b : ℝ}

/-- **The area–energy form of the isoperimetric inequality for a simple closed curve.** For a
simple closed absolutely continuous curve on `[a, b]` (`a < b`) with square-integrable derivative
`γ'`, the Lebesgue area `A` of the inside of its trace satisfies `4π A ≤ (b - a) ∫ₐᵇ ‖γ'‖²`. For
a curve parametrized proportionally to arclength the right side is the square of its length. -/
theorem four_pi_mul_volume_real_filledHull_sdiff_le (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγ' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (γ' t) t) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hL2 : MemLp γ' 2 (volume.restrict (Ioc a b))) :
    4 * π * volume.real (TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) ≤
      (b - a) * ∫ t in a..b, ‖γ' t‖ ^ 2 := by
  rw [← hγ.abs_signedArea_eq_volume_real hab hclosed hinj]
  exact TauCeti.four_pi_mul_abs_signedArea_le hab hγ hγ' hclosed hL2

/-- **Equality in the area–energy form of the isoperimetric inequality for a simple closed
curve.** For a simple closed absolutely continuous curve on `[a, b]` (`a < b`) with
square-integrable derivative `γ'`, the Lebesgue area `A` of the inside of its trace satisfies
`4π A = (b - a) ∫ₐᵇ ‖γ'‖²` exactly when the curve traverses a circle once at constant angular
speed, in either orientation. -/
theorem four_pi_mul_volume_real_filledHull_sdiff_eq_iff (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγ' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (γ' t) t) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hL2 : MemLp γ' 2 (volume.restrict (Ioc a b))) :
    4 * π * volume.real (TauCeti.filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) =
        (b - a) * ∫ t in a..b, ‖γ' t‖ ^ 2 ↔
      ∃ c w : ℂ, (∀ t ∈ Icc a b, γ t = c + w * exp (2 * π * I * t / (b - a))) ∨
        ∀ t ∈ Icc a b, γ t = c + w * exp (-(2 * π * I * t / (b - a))) := by
  rw [← hγ.abs_signedArea_eq_volume_real hab hclosed hinj, eq_comm]
  exact TauCeti.mul_integral_norm_sq_eq_four_pi_mul_abs_signedArea_iff hab hγ hγ' hclosed hL2

end AbsolutelyContinuousOnInterval

namespace BoundedVariationOn

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- **The isoperimetric inequality for a rectifiable simple closed curve.** For a continuous
simple closed curve of bounded variation on `[a, b]` (`a < b`), with length `L` its total
variation, the Lebesgue area `A` of the inside of its trace satisfies `4π A ≤ L²`. The curve need
not be absolutely continuous. -/
theorem four_pi_mul_volume_real_filledHull_sdiff_le (hab : a < b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hcont : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    4 * π * volume.real (TauCeti.filledHull (γ '' Icc a b) \ (γ '' Icc a b)) ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 := by
  rw [← hγ.abs_rectifiableSignedArea_eq_volume_real hab hcont hclosed hinj]
  exact TauCeti.four_pi_mul_abs_rectifiableSignedArea_le hcont hclosed

/-- **Equality in the isoperimetric inequality for a rectifiable simple closed curve.** For a
continuous simple closed curve of bounded variation on `[a, b]` (`a < b`), with length `L` its
total variation, the Lebesgue area `A` of the inside of its trace satisfies `4π A = L²` exactly
when the trace is a circle of positive radius. -/
theorem four_pi_mul_volume_real_filledHull_sdiff_eq_iff (hab : a < b)
    (hγ : BoundedVariationOn γ (Icc a b)) (hcont : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    4 * π * volume.real (TauCeti.filledHull (γ '' Icc a b) \ (γ '' Icc a b)) =
        (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ γ '' Icc a b = sphere c r := by
  rw [← hγ.abs_rectifiableSignedArea_eq_volume_real hab hcont hclosed hinj, eq_comm]
  exact eVariationOn_toReal_sq_eq_four_pi_mul_abs_rectifiableSignedArea_iff_exists_image_eq_sphere
    hγ hcont hclosed hinj hab

end BoundedVariationOn

namespace TauCeti

variable {C : Set ℂ}

/-- **The isoperimetric inequality for a rectifiable Jordan curve.** For a Jordan curve `C ⊆ ℂ`
of finite length `L = μHE[1] C`, the Lebesgue area `A` of its inside `filledHull C \ C`
satisfies `4π A ≤ L²`. -/
theorem IsJordanCurve.four_pi_mul_volume_real_filledHull_sdiff_le (hC : IsJordanCurve C)
    (hfin : μHE[1] C ≠ ∞) :
    4 * π * volume.real (filledHull C \ C) ≤ (μHE[1] C).toReal ^ 2 := by
  rw [Measure.euclideanHausdorffMeasure_one] at hfin ⊢
  obtain ⟨γ, hcont, hclosed, hinj, hγ, rfl⟩ :=
    (isJordanCurve_and_hausdorffMeasure_lt_top_iff zero_lt_one).1 ⟨hC, hfin.lt_top⟩
  rw [← hcont.eVariationOn_eq_hausdorffMeasure_image (hinj.mono Ioo_subset_Ico_self)]
  exact hγ.four_pi_mul_volume_real_filledHull_sdiff_le zero_lt_one hcont hclosed hinj

/-- **The isoperimetric inequality for a Jordan curve.** For every Jordan curve `C ⊆ ℂ`, with
length `L = μHE[1] C` and the Lebesgue area `A` of its inside `filledHull C \ C`, the inequality
`4π A ≤ L²` holds in `ℝ≥0∞`. No rectifiability is assumed: if `L = ∞` the inequality is
immediate. -/
theorem IsJordanCurve.ofReal_four_pi_mul_volume_filledHull_sdiff_le (hC : IsJordanCurve C) :
    ENNReal.ofReal (4 * π) * volume (filledHull C \ C) ≤ μHE[1] C ^ 2 := by
  by_cases hfin : μHE[1] C = ∞
  · simp [hfin]
  have hA := hC.measure_filledHull_sdiff_lt_top
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow, ← measureReal_def]
  exact hC.four_pi_mul_volume_real_filledHull_sdiff_le hfin

/-- **Equality in the isoperimetric inequality for a rectifiable Jordan curve.** For a Jordan
curve `C ⊆ ℂ` of finite length `L = μHE[1] C`, the Lebesgue area `A` of its inside
`filledHull C \ C` satisfies `4π A = L²` exactly when `C` is a circle of positive radius. -/
theorem IsJordanCurve.four_pi_mul_volume_real_filledHull_sdiff_eq_iff (hC : IsJordanCurve C)
    (hfin : μHE[1] C ≠ ∞) :
    4 * π * volume.real (filledHull C \ C) = (μHE[1] C).toReal ^ 2 ↔
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ C = sphere c r := by
  rw [Measure.euclideanHausdorffMeasure_one] at hfin ⊢
  obtain ⟨γ, hcont, hclosed, hinj, hγ, rfl⟩ :=
    (isJordanCurve_and_hausdorffMeasure_lt_top_iff zero_lt_one).1 ⟨hC, hfin.lt_top⟩
  rw [← hcont.eVariationOn_eq_hausdorffMeasure_image (hinj.mono Ioo_subset_Ico_self)]
  exact hγ.four_pi_mul_volume_real_filledHull_sdiff_eq_iff zero_lt_one hcont hclosed hinj

/-- **Equality in the isoperimetric inequality for a Jordan curve.** For every Jordan curve
`C ⊆ ℂ`, with length `L = μHE[1] C` and the Lebesgue area `A` of its inside `filledHull C \ C`,
the equality `4π A = L²` holds in `ℝ≥0∞` exactly when `C` is a circle of positive radius. No
rectifiability is assumed: a Jordan curve of infinite length has finite area, so it is not an
equality case, and a circle has finite length. -/
theorem IsJordanCurve.ofReal_four_pi_mul_volume_filledHull_sdiff_eq_iff (hC : IsJordanCurve C) :
    ENNReal.ofReal (4 * π) * volume (filledHull C \ C) = μHE[1] C ^ 2 ↔
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ C = sphere c r := by
  have hA := hC.measure_filledHull_sdiff_lt_top
  by_cases hfin : μHE[1] C = ∞
  · refine iff_of_false (fun h ↦ ?_) ?_
    · rw [hfin, ENNReal.top_pow two_ne_zero] at h
      exact (by finiteness : ENNReal.ofReal (4 * π) * volume (filledHull C \ C) ≠ ∞) h
    · rintro ⟨c, r, hr, rfl⟩
      simp [Complex.euclideanHausdorffMeasure_sphere c hr.le] at hfin
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow, ← measureReal_def,
    hC.four_pi_mul_volume_real_filledHull_sdiff_eq_iff hfin]

end TauCeti
