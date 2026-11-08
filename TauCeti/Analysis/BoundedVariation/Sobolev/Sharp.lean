/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.BoundedVariation.Coarea
import TauCeti.Analysis.BoundedVariation.Composition
import TauCeti.Analysis.BoundedVariation.Isoperimetric
import TauCeti.MeasureTheory.Function.LpSeminorm.LayerCake

/-!
# The sharp BV Sobolev bound

In a real Euclidean space of dimension `n ≥ 2`, put `ωₙ = volume (ball 0 1)` and
`p = n / (n - 1)`. Every integrable real-valued function satisfies

`‖u‖ₚ ≤ (n ωₙ^(1/n))⁻¹ |Du|(E)`.

The bound allows infinite variation. Finite variation gives membership in `Lᵖ`, not just
a bound on a seminorm. The exponent is expressed by `NNReal.HolderConjugate n p`, as in
the nonsharp BV Sobolev inequality.

For a nonnegative function, integral Minkowski bounds its norm by the integral of the
superlevel-set norms. The sharp perimeter inequality bounds these norms, and scalar
coarea integrates the perimeters. Lipschitz composition with absolute value extends
the result to signed functions. The geometric inputs are
`MeasureTheory.NullMeasurableSet.ofReal_mul_volume_real_rpow_mul_le_perimeter` and
`TauCeti.totalVariationOn_eq_lintegral_perimeter`; the absolute-value step uses
`TauCeti.totalVariationOn_comp_lipschitz_le`. No regularity or bounded support is required
of `u`. This file proves the bound and membership, not the classification of equality cases.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*,
  revised edition, §5.6.1 (Sobolev inequalities for BV functions).
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*,
  Theorem 12.37 (the sharp BV Sobolev inequality).
-/

public noncomputable section

open MeasureTheory Metric Module Set
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {u : E → ℝ} {p : ℝ≥0}

private theorem sharpSobolevConst_pos (hp : NNReal.HolderConjugate (finrank ℝ E) p) :
    0 < (finrank ℝ E : ℝ) * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ := by
  have hn : 0 < (finrank ℝ E : ℝ) := by exact_mod_cast hp.pos
  have hball : 0 < volume.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  positivity

private theorem mul_eLpNorm_le_totalVariationOn_of_nonneg (hu : Integrable u)
    (hu0 : 0 ≤ᵐ[volume] u) (hp : NNReal.HolderConjugate (finrank ℝ E) p) :
    ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^
      (finrank ℝ E : ℝ)⁻¹) * eLpNorm u p volume ≤ totalVariationOn volume ⊤ u := by
  let C := ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^
    (finrank ℝ E : ℝ)⁻¹)
  have hn : finrank ℝ E ≠ 0 := by
    exact_mod_cast hp.pos.ne'
  have hpower : 1 / (p : ℝ) = 1 - (finrank ℝ E : ℝ)⁻¹ := by
    simpa only [one_div, NNReal.coe_natCast] using hp.coe.one_sub_inv.symm
  have hlevel (t : ℝ) (ht : 0 < t) :
      C * volume {x | t < u x} ^ (1 / (p : ℝ)) ≤
        perimeter volume ⊤ {x | t < u x} := by
    have hs : NullMeasurableSet {x | t < u x} volume :=
      nullMeasurableSet_lt aemeasurable_const hu.aemeasurable
    have hfin : volume {x | t < u x} ≠ ∞ := (hu.measure_gt_lt_top ht).ne
    by_cases hzero : volume {x | t < u x} = 0
    · simp [hzero, inv_pos.mpr hp.coe.symm.pos]
    · have h := hs.ofReal_mul_volume_real_rpow_mul_le_perimeter hfin hn hzero
      rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
        measureReal_nonneg _)), ← ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg
        (by rw [← hpower]; positivity), ofReal_measureReal hfin] at h
      simpa only [C, hpower] using h
  have hlayer := eLpNorm_le_lintegral_measure_norm_gt hu.aestronglyMeasurable
    (p := (p : ℝ≥0∞)) (by exact_mod_cast hp.symm.lt.le) ENNReal.coe_ne_top
  have hnorm (t : ℝ) : volume {x | t < ‖u x‖} = volume {x | t < u x} := by
    exact measure_congr (hu0.mono fun x hx ↦ by simp [Real.norm_eq_abs, abs_of_nonneg hx])
  simp_rw [hnorm, ENNReal.coe_toReal] at hlayer
  calc
    C * eLpNorm u p volume ≤
        C * ∫⁻ t in Ioi (0 : ℝ), volume {x | t < u x} ^ (1 / (p : ℝ)) :=
      by gcongr
    _ = ∫⁻ t in Ioi (0 : ℝ), C * volume {x | t < u x} ^ (1 / (p : ℝ)) :=
      (lintegral_const_mul' C _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), perimeter volume ⊤ {x | t < u x} :=
      setLIntegral_mono' measurableSet_Ioi hlevel
    _ ≤ ∫⁻ t : ℝ, perimeter volume ⊤ {x | t < u x} := setLIntegral_le_lintegral _ _
    _ = totalVariationOn volume ⊤ u :=
      (totalVariationOn_eq_lintegral_perimeter
        (hu.locallyIntegrable.locallyIntegrableOn ⊤)).symm

/-- **The sharp BV Sobolev bound.** In dimension `n ≥ 2`, every integrable real-valued
function satisfies `‖u‖ₚ ≤ (n ωₙ^(1/n))⁻¹ |Du|(E)` for `p = n / (n - 1)`.
The total variation may be infinite. -/
theorem eLpNorm_le_inv_mul_totalVariationOn (hu : Integrable u)
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) :
    eLpNorm u p volume ≤
      (ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^
        (finrank ℝ E : ℝ)⁻¹))⁻¹ * totalVariationOn volume ⊤ u := by
  have habs := mul_eLpNorm_le_totalVariationOn_of_nonneg hu.norm
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg (u x)) hp
  rw [eLpNorm_norm u hu.aestronglyMeasurable] at habs
  have hvar : totalVariationOn volume ⊤ (fun x ↦ ‖u x‖) ≤
      totalVariationOn volume ⊤ u := by
    simpa only [Function.comp_def, ENNReal.coe_one, one_mul] using
      totalVariationOn_comp_lipschitz_le (hu.locallyIntegrable.locallyIntegrableOn ⊤)
        (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ))
  let C := ENNReal.ofReal ((finrank ℝ E : ℝ) * volume.real (ball (0 : E) 1) ^
    (finrank ℝ E : ℝ)⁻¹)
  calc
    eLpNorm u p volume = C⁻¹ * (C * eLpNorm u p volume) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel
        (ENNReal.ofReal_pos.mpr (sharpSobolevConst_pos hp)).ne' ENNReal.ofReal_ne_top, one_mul]
    _ ≤ C⁻¹ * totalVariationOn volume ⊤ u := by gcongr; exact habs.trans hvar

/-- A whole-space BV function belongs to the critical Lebesgue space `L^(n/(n-1))`. -/
theorem MemBV.memLp_of_holderConjugate (hu : MemBV volume ⊤ u)
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) : MemLp u p volume := by
  obtain ⟨hint, hvar⟩ := memBV_iff.mp hu
  have hint' : Integrable u := by simpa using hint
  apply memLp_iff.mpr
  refine (eLpNorm_le_inv_mul_totalVariationOn hint' hp).trans_lt ?_
  apply ENNReal.mul_lt_top _ hvar
  exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (sharpSobolevConst_pos hp))

end TauCeti
