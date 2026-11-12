/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Affine
public import TauCeti.Probability.Distributions.GeneralizedNormal.Basic

/-!
# Affine transport of generalized normal laws

An affine image `a + c * X` of a generalized normal variable with location `m`, scale `s` and
shape `p` is generalized normal with location `a + c * m`, scale `|c| * s` and the same shape,
provided `c ≠ 0`. The density and measure identities hold at every scale and shape: invalid
parameters give zero on both sides. At slope zero the image of a probability law is
`Measure.dirac a`, not a generalized normal law.

The reflection `x ↦ 2 * m - x` fixes the law with location `m`, so the law is symmetric about its
location.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- The real generalized normal density satisfies the affine scaling identity at every slope and
parameter. At slope zero, both sides vanish. -/
theorem generalizedNormalPDFReal_affine (m s p a c x : ℝ) :
    generalizedNormalPDFReal (a + c * m) (|c| * s) p x =
      |c|⁻¹ * generalizedNormalPDFReal m s p ((x - a) / c) := by
  by_cases hc : c = 0
  · subst c
    simp
  have hc' : 0 < |c| := abs_pos.mpr hc
  by_cases h : 0 < s ∧ 0 < p
  · have harg : ((x - a) / c - m) / s = (x - (a + c * m)) / c / s := by
      field_simp
      ring
    have habs : |(x - (a + c * m)) / (|c| * s)| = |((x - a) / c - m) / s| := by
      rw [harg]
      simp [abs_div, abs_mul, div_div]
    rw [generalizedNormalPDFReal_of_pos (mul_pos hc' h.1) h.2,
      generalizedNormalPDFReal_of_pos h.1 h.2, habs]
    field_simp
  · have h' : ¬ (0 < |c| * s ∧ 0 < p) := fun h'' =>
      h ⟨pos_of_mul_pos_right h''.1 hc'.le, h''.2⟩
    rw [generalizedNormalPDFReal_of_not_pos h', generalizedNormalPDFReal_of_not_pos h, mul_zero]

/-- Applying `affineDensity` to a generalized normal density yields the generalized normal
density at the transformed location and scale. This also holds at slope zero, where both sides
vanish. -/
-- Prefer the generalized normal form to the generic expansion by `affineDensity_apply`.
@[simp 1100]
theorem affineDensity_generalizedNormalPDF (m s p a c x : ℝ) :
    affineDensity a c (generalizedNormalPDF m s p) x =
      generalizedNormalPDF (a + c * m) (|c| * s) p x := by
  rw [affineDensity_apply, generalizedNormalPDF_eq_ofReal, generalizedNormalPDF_eq_ofReal,
    generalizedNormalPDFReal_affine m s p a c,
    ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg c))]

/-- **Affine transport.** A nonconstant affine image of a generalized normal law has location
`a + c * m`, scale `|c| * s` and the same shape. This includes the invalid-parameter zero laws. -/
@[simp]
theorem generalizedNormalMeasure_map_affine (m s p a : ℝ) {c : ℝ} (hc : c ≠ 0) :
    (generalizedNormalMeasure m s p).map (fun x ↦ a + c * x) =
      generalizedNormalMeasure (a + c * m) (|c| * s) p := by
  rw [generalizedNormalMeasure_eq_withDensity, map_affine_withDensity_volume _ hc,
    generalizedNormalMeasure_eq_withDensity]
  congr 1
  ext x
  exact affineDensity_generalizedNormalPDF m s p a c x

/-- Affine transport of a generalized normal random variable. -/
theorem hasLaw_affine_generalizedNormalMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m s p a c : ℝ} (hc : c ≠ 0)
    (hX : HasLaw X (generalizedNormalMeasure m s p) P) :
    HasLaw (fun ω ↦ a + c * X ω) (generalizedNormalMeasure (a + c * m) (|c| * s) p) P :=
  (HasLaw.mk (by fun_prop) (generalizedNormalMeasure_map_affine m s p a hc)).fun_comp hX

/-- **Symmetry.** Reflection through the location fixes a generalized normal law. -/
theorem generalizedNormalMeasure_map_two_mul_sub (m s p : ℝ) :
    (generalizedNormalMeasure m s p).map (fun x ↦ 2 * m - x) = generalizedNormalMeasure m s p := by
  have h := generalizedNormalMeasure_map_affine m s p (2 * m) (c := -1) (by norm_num)
  simp only [abs_neg, abs_one, one_mul, neg_one_mul, ← sub_eq_add_neg] at h
  rwa [show 2 * m - m = m by ring] at h

end TauCeti.Probability
