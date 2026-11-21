/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.OpenDisc.Taylor
public import TauCeti.RingTheory.PowerSeries.Radius
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Series on an open disc and the radius of convergence

A power series lies on the open disc of radius `R₀` (`PowerSeries.OnOpenDisc`) exactly when its
radius (`PowerSeries.radius`) is at least `R₀`. The open-disc condition is stated at a real radius,
whereas the radius lives in `ℝ≥0∞`, so this comparison lets statements about discs of possibly
infinite radius use the open-disc algebra at every finite smaller radius.

Over an ultrametric normed commutative ring, Taylor translation by a point `a` with `‖a‖` strictly
below the radius does not decrease the radius. Over the complex numbers the translate is in general
only guaranteed to converge on the largest disc about `a` inside the original disc, so this is a
genuinely nonarchimedean phenomenon: in an ultrametric space every point of an open ball is a
centre. Consequently, over a complete ultrametric ring, the expansion of a series about `a` and the
expansion of its Taylor translate about any point `b` of the open disc of radius `r` about `a`
agree on that whole disc.

## Main results

* `PowerSeries.onOpenDisc_iff_ofReal_le_radius`: `f` lies on the open disc of radius `R₀` exactly
  when `R₀ ≤ radius f`.
* `PowerSeries.exists_onOpenDisc_of_ofReal_lt_radius` and
  `PowerSeries.exists_onOpenDisc_of_le_radius`: below the radius, a point lies in some open disc of
  real radius on which the series (or two series) lie.
* `PowerSeries.radius_le_radius_taylor`: Taylor translation by a point inside the radius does not
  decrease the radius of a series over an ultrametric ring.
* `PowerSeries.le_radius_taylor_sub` and `PowerSeries.evalAt_sub_eq_evalAt_taylor_sub`: over a
  complete ultrametric ring, the Taylor translate of a series of radius at least `r` to any point
  `b` of the open disc of radius `r` about `a` has radius at least `r` and represents the same
  function on that whole disc.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Metric
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

/-- Two series whose radii are at least `r` both lie on one open disc of real radius containing a
given point of norm less than `r`. -/
theorem exists_onOpenDisc_of_le_radius {g : R⟦X⟧} {r : ℝ≥0∞} (hf : r ≤ f.radius)
    (hg : r ≤ g.radius) {y : R} (hy : ‖y‖ₑ < r) :
    ∃ R₀ : ℝ, ‖y‖ < R₀ ∧ f.OnOpenDisc R₀ ∧ g.OnOpenDisc R₀ := by
  obtain ⟨R₁, hR₁, hf₁⟩ := exists_onOpenDisc_of_ofReal_lt_radius (f := f) (t := ‖y‖)
    (by rw [ofReal_norm]; exact hy.trans_le hf)
  obtain ⟨R₂, hR₂, hg₂⟩ := exists_onOpenDisc_of_ofReal_lt_radius (f := g) (t := ‖y‖)
    (by rw [ofReal_norm]; exact hy.trans_le hg)
  exact ⟨min R₁ R₂, lt_min hR₁ hR₂, hf₁.mono (min_le_left _ _), hg₂.mono (min_le_right _ _)⟩

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

/-- The Taylor translate of a series of radius at least `r` to a point of the open disc of radius
`r` has radius at least `r`. -/
theorem le_radius_taylor_sub {b : R} {r : ℝ≥0∞} (hf : r ≤ f.radius) (hb : b ∈ eball a r) :
    r ≤ (taylor (b - a) f).radius :=
  hf.trans (radius_le_radius_taylor ((TauCeti.mem_eball_iff_eNorm.mp hb).trans_le hf))

/-- **Recentring a series on an open disc.** Over a complete ultrametric normed commutative ring,
if `f` has radius at least `r` and `b` lies in the open disc of radius `r` about `a`, then the
expansion of `f` about `a` and the expansion of its Taylor translate to `b` about `b` agree on the
whole disc. -/
theorem evalAt_sub_eq_evalAt_taylor_sub [CompleteSpace R] {b z : R} {r : ℝ≥0∞}
    (hf : r ≤ f.radius) (hb : b ∈ eball a r) (hz : z ∈ eball a r) :
    f.evalAt (z - a) = (taylor (b - a) f).evalAt (z - b) := by
  have hba := TauCeti.mem_eball_iff_eNorm.mp hb
  have hza := TauCeti.mem_eball_iff_eNorm.mp hz
  -- A real radius beyond `‖b - a‖` and `‖z - a‖`, hence beyond `‖z - b‖`, on which `f` lies.
  obtain ⟨R₀, hR₀, hR⟩ := exists_onOpenDisc_of_ofReal_lt_radius (f := f)
    (t := max ‖b - a‖ ‖z - a‖)
    (by rw [ENNReal.ofReal_max, ofReal_norm, ofReal_norm]; exact (max_lt hba hza).trans_le hf)
  have hzb : ‖z - b‖ < R₀ := by
    have := dist_triangle_max z a b
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev a b] at this
    exact this.trans_lt (by rwa [max_comm])
  rw [hR.evalAt_taylor ((le_max_left _ _).trans_lt hR₀) hzb, sub_add_sub_cancel]

end Ultrametric

end PowerSeries
