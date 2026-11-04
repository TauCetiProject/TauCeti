/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.AreaEnergy
public import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Contour.Curve.Circle.Basic
import TauCeti.MeasureTheory.Function.AreaFormula.Circle

/-!
# Circular traces in the rectifiable isoperimetric equality case

A nonconstant continuous closed curve of bounded variation that attains equality in the
length–signed-area inequality traces a circle exactly. Its bounded inside, expressed as its
filled hull minus its trace, is therefore an open disk. The supplied parametrization need not be
absolutely continuous or have constant speed.

The equality theorem in `TauCeti.Analysis.Fourier.AreaEnergy` identifies the curve as a circular
exponential in its cumulative arclength. Cumulative arclength maps the parameter interval onto
the whole length interval, so the pointwise formula gives equality of traces, rather than only
containment in a circle. Nonconstancy excludes the radius-zero case.

Conversely, every continuous simple closed parametrization of a circle of radius `r > 0` attains
equality. It is automatically rectifiable, of length `2 π r`, because the length of a simple curve
is the one-dimensional Hausdorff measure of its trace. Its geometric signed area is `π r²` or
`-π r²`: a continuous angle function lifts the curve through `circleMap`, injectivity on `[a, b)`
makes the angle strictly monotone with a total turn of exactly `± 2π`, and the geometric signed
area is invariant under increasing and changes sign under decreasing continuous reparametrizations.
Neither absolute continuity nor constant speed of the parametrization is assumed. Thus a
rectifiable simple closed curve attains equality exactly when its trace is a circle.

These results concern equality for geometric signed area. For a circle, the Lebesgue area of the
inside is computed directly, so its length `L` and inside area `A` also satisfy `L² = 4π A`.
Identifying the signed area, up to orientation, with the Lebesgue area enclosed by an arbitrary
simple curve requires the Jordan index theorem separately.

## Main results

In the `BoundedVariationOn` namespace:

* `exists_image_eq_sphere_of_isoperimetric_eq`: equality forces a circular trace.
* `eVariationOn_toReal_sq_eq_four_pi_mul_abs_rectifiableSignedArea_iff_exists_image_eq_sphere`:
  a rectifiable simple closed curve attains equality exactly when its trace is a circle.

In the `ContinuousOn` namespace:

* `rectifiableSignedArea_eq_or_eq_neg_of_image_eq_sphere`: a simple closed parametrization of a
  circle of radius `r` has geometric signed area `π r²` or `-π r²`.
* `eVariationOn_toReal_sq_eq_four_pi_mul_abs_rectifiableSignedArea_of_image_eq_sphere`: simple
  closed parametrizations of circles attain equality for the geometric signed area.
* `eVariationOn_toReal_sq_eq_four_pi_mul_volume_real_filledHull_sdiff_of_image_eq_sphere`: they
  also attain equality for the Lebesgue area of the inside.
-/

public section

open TauCeti MeasureTheory Set Complex Metric
open scoped Real Interval Pointwise

namespace ContinuousOn

variable {γ : ℝ → ℂ} {a b : ℝ} {c : ℂ} {r : ℝ}

/-- A simple closed curve that traces the circle `sphere c r` of positive radius has geometric
signed area `π r²` or `-π r²`, according to its orientation. The parametrization need not be
absolutely continuous; it is a continuous monotone reparametrization of a single traversal of
the circle. -/
theorem rectifiableSignedArea_eq_or_eq_neg_of_image_eq_sphere (hcont : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) (himage : γ '' Icc a b = sphere c r)
    (hr : 0 < r) :
    rectifiableSignedArea γ a b = π * r ^ 2 ∨ rectifiableSignedArea γ a b = -(π * r ^ 2) := by
  -- The trace has the two distinct points `c + r` and `c - r`, so the interval is nontrivial.
  have hab : a < b := by
    by_contra hba
    have hsub : (sphere c r).Subsingleton :=
      himage ▸ (subsingleton_Icc_of_ge (not_lt.1 hba)).image γ
    have h := hsub (show c + r ∈ sphere c r by simp [abs_of_pos hr])
      (show c - r ∈ sphere c r by simp [abs_of_pos hr])
    have h' := congrArg re h
    simp only [add_re, sub_re, ofReal_re] at h'
    linarith
  obtain ⟨θ, hθ, hγθ⟩ := hcont.exists_continuousOn_circleMap_comp_eqOn
    (himage ▸ mapsTo_image γ (Icc a b))
  have hinj' : InjOn (circleMap c r ∘ θ) (Ico a b) :=
    hinj.congr (hγθ.symm.mono Ico_subset_Icc_self)
  have hclosed' : circleMap c r (θ a) = circleMap c r (θ b) :=
    (hγθ (left_mem_Icc.2 hab.le)).trans (hclosed.trans (hγθ (right_mem_Icc.2 hab.le)).symm)
  have hcirc (s : Set ℝ) : ContinuousOn (circleMap c r) s := (continuous_circleMap c r).continuousOn
  rw [← rectifiableSignedArea_congr hγθ]
  rcases hθ.monotoneOn_and_eq_add_two_pi_or_antitoneOn_and_eq_add_two_pi hr.ne' hab hinj'
    hclosed' with ⟨hmono, hb⟩ | ⟨hanti, ha⟩
  · left
    rw [rectifiableSignedArea_comp_of_monotoneOn (hcirc _) hab.le hθ hmono rfl rfl, hb,
      rectifiableSignedArea_circleMap]
  · right
    rw [rectifiableSignedArea_comp_of_antitoneOn (hcirc _) hab.le hθ hanti rfl rfl, ha,
      rectifiableSignedArea_circleMap]

/-- **The circle attains equality in the isoperimetric inequality.** A simple closed curve that
traces a circle of positive radius satisfies `L² = 4π |A|`, where `L` is its length and `A` its
geometric signed area. The parametrization need not be absolutely continuous; its bounded
variation is a consequence. -/
theorem eVariationOn_toReal_sq_eq_four_pi_mul_abs_rectifiableSignedArea_of_image_eq_sphere
    (hcont : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (himage : γ '' Icc a b = sphere c r) (hr : 0 < r) :
    (eVariationOn γ (Icc a b)).toReal ^ 2 = 4 * π * |rectifiableSignedArea γ a b| := by
  have habs : |rectifiableSignedArea γ a b| = π * r ^ 2 := by
    rcases hcont.rectifiableSignedArea_eq_or_eq_neg_of_image_eq_sphere hclosed hinj himage hr
      with h | h <;> simp [h, abs_of_pos, Real.pi_pos, hr]
  rw [hcont.eVariationOn_eq_of_image_eq_sphere (hinj.mono Ioo_subset_Ico_self) himage hr.le,
    ENNReal.toReal_ofReal (by positivity), habs]
  ring

/-- A continuous curve on `[a, b]` that is injective on `(a, b)` and traces a circle satisfies
`L² = 4π A`, where `L` is its length and `A` is the Lebesgue area of the inside of its trace,
its filled hull minus the trace. -/
theorem eVariationOn_toReal_sq_eq_four_pi_mul_volume_real_filledHull_sdiff_of_image_eq_sphere
    (hcont : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b))
    (himage : γ '' Icc a b = sphere c r) (hr : 0 ≤ r) :
    (eVariationOn γ (Icc a b)).toReal ^ 2 =
      4 * π * volume.real (filledHull (γ '' Icc a b) \ γ '' Icc a b) := by
  rw [hcont.eVariationOn_eq_of_image_eq_sphere hinj himage hr, himage, filledHull_sphere c hr,
    closedBall_sdiff_sphere, measureReal_def, Complex.volume_ball,
    ENNReal.toReal_ofReal (by positivity)]
  simp [ENNReal.toReal_pow, hr]
  ring

end ContinuousOn

namespace BoundedVariationOn

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- A nonconstant continuous closed rectifiable curve attaining equality in the sharp
length–signed-area inequality has trace exactly a circle of positive radius. The original
parameter need not be absolutely continuous. -/
theorem exists_image_eq_sphere_of_isoperimetric_eq
    (hγ : BoundedVariationOn γ (Icc a b)) (hcont : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hnonconstant : ¬ (γ '' Icc a b).Subsingleton)
    (heq : (eVariationOn γ (Icc a b)).toReal ^ 2 =
      4 * π * |rectifiableSignedArea γ a b|) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ γ '' Icc a b = sphere c r := by
  have hab : a ≤ b := by
    by_contra h
    exact hnonconstant (by simp [Icc_eq_empty_of_lt (lt_of_not_ge h)])
  set L := (eVariationOn γ (Icc a b)).toReal
  have hL : 0 < L := by
    refine lt_of_le_of_ne ENNReal.toReal_nonneg ?_
    intro h0
    have hvar : eVariationOn γ (Icc a b) = 0 :=
      (ENNReal.toReal_eq_zero_iff _).1 h0.symm |>.resolve_right hγ
    apply hnonconstant
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    exact edist_eq_zero.1 ((eVariationOn.eq_zero_iff γ).1 hvar s hs t ht)
  obtain ⟨c, w, hform⟩ :=
    (eVariationOn_toReal_sq_eq_four_pi_mul_abs_rectifiableSignedArea_iff hγ hcont hclosed).1 heq
  -- Rescaling a full length interval gives a full angular period, including both endpoints.
  have hangle : (fun t : ℝ ↦ 2 * π * t / L) '' Icc 0 L = uIcc 0 (2 * π) := by
    rw [← uIcc_of_le hL.le]
    have hscale : (fun t : ℝ ↦ 2 * π * t / L) = fun t ↦ t * (2 * π / L) := by
      funext t
      ring
    rw [hscale, image_mul_const_uIcc]
    congr 1
    · simp
    · field_simp
  have hunit : (fun t : ℝ ↦ exp (2 * π * I * t / L)) '' Icc 0 L = sphere (0 : ℂ) 1 := by
    calc
      _ = circleMap 0 1 '' ((fun t : ℝ ↦ 2 * π * t / L) '' Icc 0 L) := by
        rw [image_image]
        congr 1
        funext t
        simp only [circleMap, ofReal_one, one_mul, zero_add, ofReal_div, ofReal_mul,
          ofReal_ofNat]
        congr 1
        ring
      _ = sphere (0 : ℂ) 1 := by rw [hangle, image_circleMap_uIcc]; simp
  have hnegunit : (fun t : ℝ ↦ exp (-(2 * π * I * t / L))) '' Icc 0 L =
      sphere (0 : ℂ) 1 := by
    calc
      _ = conjLIE '' ((fun t : ℝ ↦ exp (2 * π * I * t / L)) '' Icc 0 L) := by
        rw [image_image]
        congr 1
        funext t
        simp [conjLIE_apply, ← exp_conj, map_ofNat, neg_div]
      _ = sphere (0 : ℂ) 1 := by
        rw [hunit, conjLIE.image_sphere]
        simp
  -- Surjectivity of cumulative arclength transfers the entire circular trace back to γ.
  have htrace (g : ℝ → ℂ) (hg : g '' Icc 0 L = sphere (0 : ℂ) 1)
      (hform : ∀ t ∈ Icc a b,
        γ t = c + w * g (variationOnFromTo γ (Icc a b) a t)) :
      γ '' Icc a b = sphere c ‖w‖ := by
    calc
      _ = (fun t ↦ c + w * g (variationOnFromTo γ (Icc a b) a t)) '' Icc a b :=
        image_congr hform
      _ = c +ᵥ w • (g '' (variationOnFromTo γ (Icc a b) a '' Icc a b)) := by
        rw [← image_vadd, ← image_smul, image_image, image_image, image_image]
        rfl
      _ = sphere c ‖w‖ := by
        rw [hγ.image_variationOnFromTo_Icc hcont hab, hg, smul_sphere w 0 zero_le_one]
        simp
  have hcircle : γ '' Icc a b = sphere c ‖w‖ := by
    rcases hform with hpos | hneg
    · exact htrace _ hunit hpos
    · exact htrace _ hnegunit hneg
  refine ⟨c, ‖w‖, ?_, hcircle⟩
  by_contra h
  have hw : ‖w‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
  apply hnonconstant
  rw [hcircle, hw, sphere_zero]
  exact subsingleton_singleton

/-- The inside of a nonconstant continuous closed rectifiable curve attaining equality in the
length–signed-area inequality is exactly an open disk of positive radius. -/
theorem exists_filledHull_sdiff_eq_ball_of_isoperimetric_eq
    (hγ : BoundedVariationOn γ (Icc a b)) (hcont : ContinuousOn γ (Icc a b))
    (hclosed : γ a = γ b) (hnonconstant : ¬ (γ '' Icc a b).Subsingleton)
    (heq : (eVariationOn γ (Icc a b)).toReal ^ 2 =
      4 * π * |rectifiableSignedArea γ a b|) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
      filledHull (γ '' Icc a b) \ (γ '' Icc a b) = ball c r := by
  obtain ⟨c, r, hr, htrace⟩ :=
    hγ.exists_image_eq_sphere_of_isoperimetric_eq hcont hclosed hnonconstant heq
  exact ⟨c, r, hr, by rw [htrace, filledHull_sphere c hr.le, closedBall_sdiff_sphere]⟩

/-- **Equality in the isoperimetric inequality for simple closed curves.** A rectifiable simple
closed curve on `[a, b]` satisfies `L² = 4π |A|`, for its length `L` and geometric signed area
`A`, exactly when its trace is a circle of positive radius. -/
theorem eVariationOn_toReal_sq_eq_four_pi_mul_abs_rectifiableSignedArea_iff_exists_image_eq_sphere
    (hγ : BoundedVariationOn γ (Icc a b)) (hcont : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hab : a < b) :
    (eVariationOn γ (Icc a b)).toReal ^ 2 = 4 * π * |rectifiableSignedArea γ a b| ↔
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ γ '' Icc a b = sphere c r := by
  refine ⟨fun heq ↦ hγ.exists_image_eq_sphere_of_isoperimetric_eq hcont hclosed (fun hsub ↦ ?_)
    heq, fun ⟨c, r, hr, himage⟩ ↦
      hcont.eVariationOn_toReal_sq_eq_four_pi_mul_abs_rectifiableSignedArea_of_image_eq_sphere
        hclosed hinj himage hr⟩
  -- Injectivity on `[a, b)` gives the trace two distinct points.
  have hm : (a + b) / 2 ∈ Ico a b := ⟨by linarith, by linarith⟩
  have h := hinj ⟨le_rfl, hab⟩ hm (hsub (mem_image_of_mem γ (left_mem_Icc.2 hab.le))
    (mem_image_of_mem γ (Ico_subset_Icc_self hm)))
  linarith

end BoundedVariationOn
