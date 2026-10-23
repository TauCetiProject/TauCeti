/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Affine
public import TauCeti.Probability.Distributions.Laplace.Basic

/-!
# Affine transport of Laplace laws

An affine image `a + c * X` of a Laplace variable with location `m` and scale `b` has
location `a + c * m` and scale `|c| * b`, provided `c ≠ 0`. In particular, a negative
slope reflects the location and rescales the scale by its absolute value.

The density and measure identities below hold for every scale parameter: nonpositive scales
give zero on both sides. The density identities also hold at slope zero, where both sides
vanish. For a positive input scale, a zero slope instead gives
`Measure.dirac a` by `MeasureTheory.Measure.map_const`; it is not a scale-zero Laplace law.

The measure identity specializes `TauCeti.Probability.map_affine_withDensity_volume` using
the Laplace density, and the random-variable corollary applies on any measurable source space.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), ch. 24.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- The real Laplace density satisfies the affine scaling identity at every slope and scale.
At slope zero, both sides vanish. -/
theorem laplacePDFReal_affine (m b a c x : ℝ) :
    laplacePDFReal (a + c * m) (|c| * b) x =
      |c|⁻¹ * laplacePDFReal m b ((x - a) / c) := by
  by_cases hc : c = 0
  · subst c
    simp
  by_cases hb : 0 < b
  · have hsub : (x - a) / c - m = (x - (a + c * m)) / c := by
      field_simp
      ring
    have hexp : -(|x - (a + c * m)| / |c|) / b =
        -|x - (a + c * m)| / (|c| * b) := by ring
    rw [laplacePDFReal_of_pos (mul_pos (abs_pos.mpr hc) hb),
      laplacePDFReal_of_pos hb, hsub, abs_div, hexp]
    simp only [mul_inv_rev]
    ring
  · have hcb : |c| * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg c) (le_of_not_gt hb)
    simp [laplacePDFReal_of_nonpos (le_of_not_gt hb), laplacePDFReal_of_nonpos hcb]

/-- Applying `affineDensity` to a Laplace density yields the Laplace density at the transformed
location and scale. This also holds at slope zero, where both sides vanish. -/
-- Prefer the Laplace normal form to the generic expansion by affineDensity_apply.
@[simp 1100]
theorem affineDensity_laplacePDF (m b a c x : ℝ) :
    affineDensity a c (laplacePDF m b) x = laplacePDF (a + c * m) (|c| * b) x := by
  rw [affineDensity_apply, laplacePDF_eq_ofReal, laplacePDF_eq_ofReal,
    laplacePDFReal_affine m b a c, ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg c))]

/-- A nonconstant affine image of a Laplace law has transformed location `a + c * m` and
scale `|c| * b`. This includes the nonpositive-scale zero laws. -/
@[simp]
theorem laplaceMeasure_map_affine (m b a : ℝ) {c : ℝ} (hc : c ≠ 0) :
    (laplaceMeasure m b).map (fun x ↦ a + c * x) =
      laplaceMeasure (a + c * m) (|c| * b) := by
  rw [laplaceMeasure_eq_withDensity, map_affine_withDensity_volume _ hc,
    laplaceMeasure_eq_withDensity]
  congr 1
  ext x
  exact affineDensity_laplacePDF m b a c x

/-- Affine transport of a Laplace random variable, with no assumptions on its source measure
or on the sign of the nonzero slope. -/
theorem hasLaw_affine_laplaceMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {m b a c : ℝ} (hc : c ≠ 0) (hX : HasLaw X (laplaceMeasure m b) P) :
    HasLaw (fun ω ↦ a + c * X ω) (laplaceMeasure (a + c * m) (|c| * b)) P :=
  (HasLaw.mk (by fun_prop) (laplaceMeasure_map_affine m b a hc)).fun_comp hX

end TauCeti.Probability
