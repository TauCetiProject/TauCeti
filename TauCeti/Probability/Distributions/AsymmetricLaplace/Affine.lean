/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Affine
public import TauCeti.Probability.Distributions.AsymmetricLaplace.Basic

/-!
# Affine transport of asymmetric Laplace laws

An affine image `a + b * X` of an asymmetric Laplace variable with location `m`, left rate `l`
and right rate `r` has location `a + b * m`. A positive slope divides both rates by `b`;
a negative slope exchanges the left and right rates and divides them by `|b|`.
In particular, negation exchanges the two exponential tails.

The density and measure identities include invalid rate parameters, which give zero laws on
both sides. A zero slope is covered by `MeasureTheory.Measure.map_const`: a valid input law
maps to the Dirac mass at `a`.

The density argument follows the affine transport API for Laplace laws in
`TauCeti.Probability.Distributions.Laplace.Affine`, using the shared change-of-variables theorem
`TauCeti.Probability.map_affine_withDensity_volume`.

## References

* S. Kotz, T. J. Kozubowski, K. Podgórski, *The Laplace Distribution and Generalizations*,
  Birkhäuser (2001), ch. 3.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- A positive affine change of variables divides both asymmetric Laplace rates by its slope.
The real density identity holds for all rate parameters. -/
theorem asymmetricLaplacePDFReal_affine_pos (m l r a x : ℝ) {b : ℝ} (hb : 0 < b) :
    asymmetricLaplacePDFReal (a + b * m) (l / b) (r / b) x =
      b⁻¹ * asymmetricLaplacePDFReal m l r ((x - a) / b) := by
  by_cases hl : 0 < l
  · by_cases hr : 0 < r
    · have hbranch : (x - a) / b ≤ m ↔ x ≤ a + b * m := by
        rw [div_le_iff₀ hb]
        constructor <;> intro h <;> nlinarith
      have hleft : l / b * (x - (a + b * m)) = l * ((x - a) / b - m) := by
        field_simp
        ring
      have hright : r / b * (x - (a + b * m)) = r * ((x - a) / b - m) := by
        field_simp
        ring
      have hcoeff : (l / b) * (r / b) / (l / b + r / b) =
          b⁻¹ * (l * r / (l + r)) := by
        field_simp
      by_cases hx : x ≤ a + b * m
      · rw [asymmetricLaplacePDFReal_of_le (div_pos hl hb) (div_pos hr hb) hx,
          asymmetricLaplacePDFReal_of_le hl hr (hbranch.mpr hx), hleft, hcoeff]
        ring
      · rw [asymmetricLaplacePDFReal_of_lt (div_pos hl hb) (div_pos hr hb) (lt_of_not_ge hx),
          asymmetricLaplacePDFReal_of_lt hl hr (lt_of_not_ge (mt hbranch.mp hx)),
          hright, hcoeff]
        ring
    · simp [asymmetricLaplacePDFReal_of_nonpos_right (le_of_not_gt hr),
        asymmetricLaplacePDFReal_of_nonpos_right
          (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) hb.le)]
  · simp [asymmetricLaplacePDFReal_of_nonpos_left (le_of_not_gt hl),
      asymmetricLaplacePDFReal_of_nonpos_left
        (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hl) hb.le)]

/-- Negating the location and argument exchanges the two rates in the real asymmetric
Laplace density. -/
theorem asymmetricLaplacePDFReal_neg (m l r x : ℝ) :
    asymmetricLaplacePDFReal (-m) r l x = asymmetricLaplacePDFReal m l r (-x) := by
  by_cases h : 0 < l ∧ 0 < r
  · have hcoeff : r * l / (r + l) = l * r / (l + r) := by ring
    have hleft : r * (x - -m) = -(r * (-x - m)) := by ring
    have hright : -(l * (x - -m)) = l * (-x - m) := by ring
    rcases lt_trichotomy x (-m) with hx | hx | hx
    · rw [asymmetricLaplacePDFReal_of_le h.2 h.1 hx.le,
        asymmetricLaplacePDFReal_of_lt h.1 h.2 (by linarith), hcoeff, hleft]
    · subst x
      rw [asymmetricLaplacePDFReal_of_le h.2 h.1 le_rfl,
        asymmetricLaplacePDFReal_of_le h.1 h.2 (by simp)]
      simp [hcoeff]
    · rw [asymmetricLaplacePDFReal_of_lt h.2 h.1 hx,
        asymmetricLaplacePDFReal_of_le h.1 h.2 (by linarith), hcoeff, hright]
  · rcases not_and_or.mp h with hl | hr
    · simp [asymmetricLaplacePDFReal_of_nonpos_left (le_of_not_gt hl),
        asymmetricLaplacePDFReal_of_nonpos_right (le_of_not_gt hl)]
    · simp [asymmetricLaplacePDFReal_of_nonpos_left (le_of_not_gt hr),
        asymmetricLaplacePDFReal_of_nonpos_right (le_of_not_gt hr)]

/-- The affine density of an asymmetric Laplace law at a positive slope is the named density
with divided rates. -/
-- Prefer the family density to the generic expansion by affineDensity_apply.
@[simp 1100]
theorem affineDensity_asymmetricLaplacePDF_pos (m l r a x : ℝ) {b : ℝ} (hb : 0 < b) :
    affineDensity a b (asymmetricLaplacePDF m l r) x =
      asymmetricLaplacePDF (a + b * m) (l / b) (r / b) x := by
  rw [affineDensity_apply, abs_of_pos hb, asymmetricLaplacePDF_eq_ofReal,
    asymmetricLaplacePDF_eq_ofReal, asymmetricLaplacePDFReal_affine_pos m l r a x hb,
    ENNReal.ofReal_mul (inv_nonneg.mpr hb.le)]

/-- Positive affine transport of asymmetric Laplace laws, including invalid-rate zero laws. -/
@[simp]
theorem asymmetricLaplaceMeasure_map_affine_pos (m l r a : ℝ) {b : ℝ} (hb : 0 < b) :
    (asymmetricLaplaceMeasure m l r).map (fun x ↦ a + b * x) =
      asymmetricLaplaceMeasure (a + b * m) (l / b) (r / b) := by
  rw [asymmetricLaplaceMeasure_eq_withDensity, map_affine_withDensity_volume _ hb.ne',
    asymmetricLaplaceMeasure_eq_withDensity]
  congr 1
  ext x
  exact affineDensity_asymmetricLaplacePDF_pos m l r a x hb

/-- Negation exchanges the left and right rates and negates the location of an asymmetric
Laplace law. -/
@[simp]
theorem asymmetricLaplaceMeasure_map_neg (m l r : ℝ) :
    (asymmetricLaplaceMeasure m l r).map (fun x ↦ -x) =
      asymmetricLaplaceMeasure (-m) r l := by
  have hmap : (fun x : ℝ ↦ -x) = fun x ↦ 0 + (-1) * x := by funext x; ring
  rw [hmap, asymmetricLaplaceMeasure_eq_withDensity,
    map_affine_withDensity_volume _ (by norm_num : (-1 : ℝ) ≠ 0),
    asymmetricLaplaceMeasure_eq_withDensity]
  congr 1
  ext x
  simp [affineDensity_apply, asymmetricLaplacePDF_eq_ofReal, asymmetricLaplacePDFReal_neg,
    div_neg]

/-- Negative affine transport exchanges the asymmetric Laplace rates and divides them by
the absolute value of the slope. This includes invalid-rate zero laws. -/
@[simp]
theorem asymmetricLaplaceMeasure_map_affine_neg (m l r a : ℝ) {b : ℝ} (hb : b < 0) :
    (asymmetricLaplaceMeasure m l r).map (fun x ↦ a + b * x) =
      asymmetricLaplaceMeasure (a + b * m) (r / |b|) (l / |b|) := by
  have h := asymmetricLaplaceMeasure_map_affine_pos (-m) r l a (neg_pos.mpr hb)
  rw [← asymmetricLaplaceMeasure_map_neg, Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa [Function.comp_def, abs_of_neg hb] using h

/-- A positive affine image of an asymmetric Laplace random variable has the transformed
location and divided rates. No assumption on the source measure is needed. -/
theorem hasLaw_affine_pos_asymmetricLaplaceMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {m l r a b : ℝ} (hb : 0 < b)
    (hX : HasLaw X (asymmetricLaplaceMeasure m l r) P) :
    HasLaw (fun ω ↦ a + b * X ω)
      (asymmetricLaplaceMeasure (a + b * m) (l / b) (r / b)) P :=
  (HasLaw.mk (by fun_prop) (asymmetricLaplaceMeasure_map_affine_pos m l r a hb)).fun_comp hX

/-- A negative affine image of an asymmetric Laplace random variable exchanges and rescales
the two rates. No assumption on the source measure is needed. -/
theorem hasLaw_affine_neg_asymmetricLaplaceMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {m l r a b : ℝ} (hb : b < 0)
    (hX : HasLaw X (asymmetricLaplaceMeasure m l r) P) :
    HasLaw (fun ω ↦ a + b * X ω)
      (asymmetricLaplaceMeasure (a + b * m) (r / |b|) (l / |b|)) P :=
  (HasLaw.mk (by fun_prop) (asymmetricLaplaceMeasure_map_affine_neg m l r a hb)).fun_comp hX

end TauCeti.Probability
