/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import TauCeti.Analysis.Convex.Sequence.Asymptotic
public import TauCeti.NumberTheory.NewtonPolygon.GaussNorm
public import TauCeti.RingTheory.PowerSeries.Radius

/-!
# The radius of a power series from its Newton polygon

Fix a real additive valuation `v` on a normed division ring and a base `b > 1` with
`‖x‖ = b ^ (-(v x).untop₀)` for nonzero `x`. The radius `PowerSeries.radius f` of a power series
`f = ∑ aₙ Xⁿ` is the supremum of the radii at which it is restricted. It is determined by the
asymptotic growth of the coefficient heights,
`λ = liminf_{n → ∞} v (aₙ) / n ∈ [-∞, ∞]`, Mathlib's `LinearGrowth.linearGrowthInf`, through
`radius f = b ^ λ`, read in `ℝ≥0∞` with `b ^ (-∞) = 0` and `b ^ ∞ = ∞`. Formally `b ^ λ` is
`EReal.exp (λ * Real.log b)`.

Both directions come from the dictionary between weighted coefficient bounds and supporting
lines: a slope `σ < λ` gives an affine minorant of slope `σ`, hence bounded weighted coefficient
norms at the radius `b ^ σ`, while restrictedness at `b ^ σ` gives an affine minorant of slope
`σ`, hence `σ ≤ λ`.

The formula covers every case at once:

* for coefficient heights with no affine lower bound (a vertical sequence), `λ = -∞` and the
  radius is `0`;
* for finitely many nonzero coefficients, including the zero series, `λ = ∞` and the radius is
  `∞`, whatever the finite slopes of the Newton polygon are; the largest slope of a polynomial
  is not its radius;
* for admissible coefficient heights with infinitely many nonzero coefficients, `λ` is the
  supremum of the finite slopes of the Newton polygon, so the radius is `b` to the power of that
  supremum. In particular such a series is entire exactly when its Newton slopes are unbounded.

At a finite positive radius the limiting slope alone decides nothing about restrictedness at
the radius itself, and restrictedness at one positive radius does not bound the slopes.

## Main results

* `PowerSeries.radius_eq_exp_linearGrowthInf`: the radius is `b ^ λ`.
* `PowerSeries.radius_eq_ofReal_rpow`: the radius is the real power `b ^ t` when `λ = t` is
  finite.
* `PowerSeries.radius_eq_zero_iff_not_isAdmissible`: the radius vanishes exactly for vertical
  coefficient heights.
* `PowerSeries.isEntire_iff_linearGrowthInf_eq_top`: a series is entire exactly when `λ = ∞`.
* `PowerSeries.radius_eq_exp_iSup_unitSlope_newtonPolygon` and
  `PowerSeries.isEntire_iff_iSup_unitSlope_newtonPolygon_eq_top`: for admissible, infinitely
  supported coefficient heights, the radius is `b` to the power of the supremum of the finite
  Newton slopes, and the series is entire exactly when these slopes are unbounded.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open TauCeti LinearGrowth
open scoped NNReal ENNReal

namespace PowerSeries

variable {K : Type*} [NormedDivisionRing K] (f : PowerSeries K)
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- A slope strictly below the asymptotic growth of the coefficient heights gives a radius
below the radius of the series. -/
private theorem ofReal_rpow_le_radius {σ : ℝ}
    (hσ : (σ : EReal) < linearGrowthInf fun n => (v (coeff n f)).toEReal) :
    ENNReal.ofReal (b ^ σ) ≤ f.radius := by
  obtain ⟨c, hc⟩ := exists_affine_le_of_lt_linearGrowthInf hσ
  have hbound := (isSupportingLine_addValuation_coeff_iff f v hb hv σ c).mp
    (isSupportingLine_iff_forall.mpr hc)
  have hpos : 0 ≤ b ^ σ := (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ).le
  rw [ENNReal.ofReal_eq_coe_nnreal hpos]
  exact le_radius_of_bound (b ^ (-c)) hbound

/-- Restrictedness at the radius `b ^ σ` bounds `σ` by the asymptotic growth of the coefficient
heights. -/
private theorem coe_le_linearGrowthInf_of_isRestricted {σ : ℝ}
    (hf : f.IsRestricted (b ^ σ)) :
    (σ : EReal) ≤ linearGrowthInf fun n => (v (coeff n f)).toEReal := by
  obtain ⟨c, hc⟩ := supportingValue_ne_bot_iff.mp
    ((hasGaussNorm_iff_supportingValue_ne_bot f v hb hv σ).mp
      (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf))
  exact le_linearGrowthInf_of_affine_le hc

/-- **The radius from coefficient growth.** The radius of a power series is `b ^ λ`, where
`λ = liminf v (aₙ) / n` is the lower linear growth of the coefficient heights, read in `ℝ≥0∞`
with `b ^ (-∞) = 0` and `b ^ ∞ = ∞`. This holds for every series, including vertical
coefficient heights, with radius `0`, and finitely supported series, with radius `∞`. -/
theorem radius_eq_exp_linearGrowthInf :
    f.radius =
      EReal.exp ((linearGrowthInf fun n => (v (coeff n f)).toEReal) * Real.log b) := by
  have hL : (0 : EReal) ≤ (Real.log b : EReal) := EReal.coe_nonneg.mpr (Real.log_pos hb).le
  have hb0 : 0 < b := zero_lt_one.trans hb
  -- A positive radius `r` is `b ^ σ` for the slope `σ = Real.logb b r`.
  have hexp {r : ℝ≥0} (hr : r ≠ 0) :
      (r : ℝ≥0∞) = EReal.exp ((Real.logb b r : EReal) * Real.log b) := by
    rw [← EReal.coe_mul, EReal.exp_coe, Real.logb, div_mul_cancel₀ _ (Real.log_pos hb).ne',
      Real.exp_log (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)), ENNReal.ofReal_coe_nnreal]
  apply le_antisymm
  · -- A radius of restrictedness strictly above `b ^ λ` would give a slope above `λ`.
    by_contra hlt
    obtain ⟨r, hEr, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hlt)
    have hr : r ≠ 0 := by
      rintro rfl
      simp at hEr
    have hrσ := hexp hr
    have hres : f.IsRestricted (b ^ Real.logb b r) := by
      rw [Real.rpow_logb hb0 hb.ne' (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr))]
      exact isRestricted_of_lt_radius (by simpa using hrR)
    have hle := mul_le_mul_of_nonneg_right
      (coe_le_linearGrowthInf_of_isRestricted f v hb hv hres) hL
    exact (EReal.exp_monotone hle).not_gt (hrσ ▸ hEr)
  · -- Every radius strictly below `b ^ λ` is `b ^ σ` for a slope `σ < λ`.
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    rw [hexp hr0, EReal.exp_lt_exp_iff] at hr
    have hσ := ofReal_rpow_le_radius f v hb hv (lt_of_mul_lt_mul_right hr hL)
    rwa [Real.rpow_logb hb0 hb.ne' (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr0)),
      ENNReal.ofReal_coe_nnreal] at hσ

/-- When the lower linear growth of the coefficient heights is a real number `t`, the radius
is the real power `b ^ t`. -/
theorem radius_eq_ofReal_rpow {t : ℝ}
    (ht : (linearGrowthInf fun n => (v (coeff n f)).toEReal) = t) :
    f.radius = ENNReal.ofReal (b ^ t) := by
  rw [radius_eq_exp_linearGrowthInf f v hb hv, ht, ← EReal.coe_mul, EReal.exp_coe,
    Real.rpow_def_of_pos (zero_lt_one.trans hb), mul_comm]

/-- **The vertical case.** The radius vanishes exactly when the coefficient heights have no
real affine lower bound. -/
theorem radius_eq_zero_iff_not_isAdmissible :
    f.radius = 0 ↔ ¬IsAdmissible fun n => v (coeff n f) := by
  rw [isAdmissible_addValuation_coeff_iff_exists_isRestricted f v hb hv, ← radius_pos_iff,
    pos_iff_ne_zero, not_not]

/-- A series is entire exactly when the lower linear growth of its coefficient heights is
`∞`. -/
theorem isEntire_iff_linearGrowthInf_eq_top :
    f.IsEntire ↔ (linearGrowthInf fun n => (v (coeff n f)).toEReal) = ⊤ := by
  have hL : (0 : EReal) < (Real.log b : EReal) := EReal.coe_pos.mpr (Real.log_pos hb)
  rw [← radius_eq_top_iff, radius_eq_exp_linearGrowthInf f v hb hv, EReal.exp_eq_top_iff,
    EReal.mul_eq_top]
  simp [hL, hL.not_gt]

/-- **The radius from Newton slopes.** For admissible coefficient heights with infinitely many
nonzero coefficients, the radius is `b` to the power of the supremum of the finite slopes of
the Newton polygon, taken in `EReal`, so unbounded slopes give radius `∞`. -/
theorem radius_eq_exp_iSup_unitSlope_newtonPolygon
    (hf : IsAdmissible fun n => v (coeff n f)) (hinf : {n | coeff n f ≠ 0}.Infinite) :
    f.radius = EReal.exp ((⨆ i : finiteEdges (f.newtonPolygon v),
      (unitSlope (f.newtonPolygon v) i : EReal)) * Real.log b) := by
  rw [radius_eq_exp_linearGrowthInf f v hb hv, newtonPolygon_def,
    linearGrowthInf_eq_iSup_unitSlope_lowerConvexEnvelope hf (by simpa using hinf)]

/-- For admissible coefficient heights with infinitely many nonzero coefficients, the series is
entire exactly when the finite slopes of its Newton polygon are unbounded. -/
theorem isEntire_iff_iSup_unitSlope_newtonPolygon_eq_top
    (hf : IsAdmissible fun n => v (coeff n f)) (hinf : {n | coeff n f ≠ 0}.Infinite) :
    f.IsEntire ↔ ⨆ i : finiteEdges (f.newtonPolygon v),
      (unitSlope (f.newtonPolygon v) i : EReal) = ⊤ := by
  rw [isEntire_iff_linearGrowthInf_eq_top f v hb hv, newtonPolygon_def,
    linearGrowthInf_eq_iSup_unitSlope_lowerConvexEnvelope hf (by simpa using hinf)]

end PowerSeries
