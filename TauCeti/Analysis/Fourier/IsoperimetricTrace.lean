/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.AreaEnergy
public import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Analysis.Contour.Curve.Circle

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

These results concern equality for geometric signed area. Identifying that signed area, up to
orientation, with the Lebesgue area enclosed by an arbitrary simple curve requires the Jordan
index theorem separately.
-/

public section

open TauCeti MeasureTheory Set Complex Metric
open scoped Real Interval Pointwise

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

end BoundedVariationOn
