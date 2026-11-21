/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Taylor
public import TauCeti.RingTheory.PowerSeries.Radius

/-!
# Series on an open disc and the radius of convergence

A power series lies on the open disc of radius `R₀` (`PowerSeries.OnOpenDisc`) exactly when its
radius (`PowerSeries.radius`) is at least `R₀`. The open-disc condition is stated at a real radius,
whereas the radius lives in `ℝ≥0∞`, so this comparison lets statements about discs of possibly
infinite radius use the open-disc algebra at every finite smaller radius.

Over an ultrametric normed commutative ring, Taylor translation by a point `a` with `‖a‖` strictly
below the radius does not decrease the radius. Over the complex numbers the translate only
converges on the largest disc about `a` inside the original disc, so this is a genuinely
nonarchimedean phenomenon: in an ultrametric space every point of an open ball is a centre.

## Main results

* `PowerSeries.onOpenDisc_iff_ofReal_le_radius`: `f` lies on the open disc of radius `R₀` exactly
  when `R₀ ≤ radius f`.
* `PowerSeries.exists_onOpenDisc_of_ofReal_lt_radius`: below the radius, a point lies in some
  open disc of real radius on which the series lies.
* `PowerSeries.radius_le_radius_taylor`: Taylor translation by a point inside the radius does not
  decrease the radius of a series over an ultrametric ring.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open scoped ENNReal

namespace PowerSeries

section NormedRing

variable {R : Type*} [NormedRing R] {f : R⟦X⟧}

/-- A series lies on the open disc of radius `R₀` exactly when its radius is at least `R₀`. -/
theorem onOpenDisc_iff_ofReal_le_radius {R₀ : ℝ} :
    f.OnOpenDisc R₀ ↔ ENNReal.ofReal R₀ ≤ f.radius := by
  refine ⟨fun hf ↦ ENNReal.le_of_forall_nnreal_lt fun s hs ↦ ?_, fun h ↦ ?_⟩
  · rcases eq_or_ne s 0 with rfl | hs0
    · simp
    · have hsR : (s : ℝ) < R₀ := by
        rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at hs
        exact hs.1
      simpa using le_radius_of_isRestricted (onOpenDisc_iff.mp hf s (by positivity) hsR)
  · refine onOpenDisc_iff.mpr fun t ht htR ↦ isRestricted_of_lt_radius ?_
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos ht]
    exact ((ENNReal.ofReal_lt_ofReal_iff (ht.trans htR)).mpr htR).trans_le h

/-- If `t` lies strictly below the radius of `f`, then `f` lies on an open disc of some real
radius `R₀ > t`. -/
theorem exists_onOpenDisc_of_ofReal_lt_radius {t : ℝ} (ht : ENNReal.ofReal t < f.radius) :
    ∃ R₀ : ℝ, t < R₀ ∧ f.OnOpenDisc R₀ := by
  obtain ⟨R₀, -, htR, hR⟩ := ENNReal.lt_iff_exists_real_btwn.mp ht
  exact ⟨R₀, (ENNReal.ofReal_lt_ofReal_iff'.mp htR).1, onOpenDisc_iff_ofReal_le_radius.mpr hR.le⟩

end NormedRing

section Ultrametric

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {f : R⟦X⟧} {a : R}

/-- **Taylor translation preserves the radius bound.** Over an ultrametric normed commutative
ring, the translate of `f` by a point `a` with `‖a‖` strictly below the radius of `f` has radius
at least that of `f`. -/
theorem radius_le_radius_taylor (ha : ‖a‖ₑ < f.radius) : f.radius ≤ (taylor a f).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun s hs ↦ ?_
  -- Choose a real radius `R₀` beyond both `s` and `‖a‖` but inside the radius of `f`.
  obtain ⟨R₀, hR₀, hf⟩ := exists_onOpenDisc_of_ofReal_lt_radius (f := f) (t := max s ‖a‖)
    (by rw [ENNReal.ofReal_max, ENNReal.ofReal_coe_nnreal, ofReal_norm]; exact max_lt hs ha)
  have := onOpenDisc_iff_ofReal_le_radius.mp (hf.taylor ((le_max_right _ _).trans_lt hR₀))
  refine le_trans ?_ this
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans hR₀.le)

end Ultrametric

section Field

variable {K : Type*} [NontriviallyNormedField K]

/-- **Comparison with `HasFPowerSeriesOnBall`.** A series `g` of positive radius is the power
series at `a` of the function `z ↦ g(z - a)` on the open ball of radius `radius g` about `a`. -/
theorem hasFPowerSeriesOnBall_evalAt_sub [CompleteSpace K] (g : K⟦X⟧) (hg : 0 < g.radius) (a : K) :
    HasFPowerSeriesOnBall (fun z ↦ g.evalAt (z - a))
      (FormalMultilinearSeries.ofScalars K fun n ↦ coeff n g) a g.radius := by
  have hrad := radius_eq_radius_ofScalars K g
  have h := ((FormalMultilinearSeries.ofScalars K fun n ↦ coeff n g).hasFPowerSeriesOnBall
    (hrad ▸ hg)).comp_sub a
  rw [zero_add, ← hrad] at h
  convert h using 2 with z
  exact evalAt_eq_ofScalarsSum g (z - a)

/-- If `F` has the power series `P` on the open ball of radius `r` about `a`, then the series with
the coefficients of `P` has radius at least `r`. -/
theorem _root_.HasFPowerSeriesOnBall.le_radius_mk_coeff {F : K → K}
    {P : FormalMultilinearSeries K K K} {a : K} {r : ℝ≥0∞} (hF : HasFPowerSeriesOnBall F P a r) :
    r ≤ (mk P.coeff).radius := by
  rw [radius_eq_radius_of_norm_eq P fun n ↦ by simp]
  exact hF.r_le

/-- **Comparison with `HasFPowerSeriesOnBall`, converse.** If `F` has the power series `P` on the
open ball of radius `r` about `a`, then the series with the coefficients of `P` takes the value
`F z` at `z - a` for every `z` in that ball. -/
theorem _root_.HasFPowerSeriesOnBall.evalAt_mk_coeff_sub {F : K → K}
    {P : FormalMultilinearSeries K K K} {a : K} {r : ℝ≥0∞} (hF : HasFPowerSeriesOnBall F P a r)
    {z : K} (hz : z ∈ Metric.eball a r) : (mk P.coeff).evalAt (z - a) = F z := by
  have h := hF.hasSum (y := z - a) (by simpa [eDist_eq_eNorm_sub] using hz)
  rw [add_sub_cancel] at h
  rw [evalAt_def, ← h.tsum_eq]
  simp [mul_comm]

end Field

end PowerSeries
