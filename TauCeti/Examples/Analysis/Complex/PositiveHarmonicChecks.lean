/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.PositiveHarmonic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Uniqueness

/-!
# Checks for the representation of positive harmonic functions on the half-plane

A nonnegative harmonic function on the upper half-plane is `c Im z + P[ν](z)` for a unique `c ≥ 0`
and a unique Poisson-finite measure `ν`
(`TauCeti.exists_eq_mul_im_add_upperHalfPlanePoissonIntegral`,
`TauCeti.eq_and_eq_of_mul_im_add_upperHalfPlanePoissonIntegral_eq`). The Checks:

* `u = Im z` has `c = 1` and `ν = 0`
  (`TauCeti.Examples.PositiveHarmonic.eq_one_and_eq_zero_of_im_eq`);
* `u = P[δ₀]`, `u(z) = Im z / (π |z|²)`, has `c = 0` and `ν = δ₀`, and `π y u(iy) = 1 = δ₀(ℝ)` for
  every `y > 0` (`TauCeti.Examples.PositiveHarmonic.upperHalfPlanePoissonIntegral_dirac_zero`,
  `TauCeti.Examples.PositiveHarmonic.eq_zero_and_eq_dirac_of_poisson_dirac_eq`,
  `TauCeti.Examples.PositiveHarmonic.pi_mul_mul_upperHalfPlanePoissonIntegral_dirac_zero_mul_I`);
* `u ≡ 1 = P[dx]` has a measure of infinite mass, and `π y u(iy) = π y → ∞`;
* `u = Re z` takes the value `-1` at `-1 + i`, so positivity is a hypothesis.

These are the Checks of §2.2 of the DiracScatteringAndNonlinearFourierTransform roadmap.
-/

public section

open Complex MeasureTheory Set Filter Topology
open UpperHalfPlane (upperHalfPlaneSet)
open scoped Real

namespace TauCeti.Examples.PositiveHarmonic

/-- **`u = Im z`.** If `Im z = c Im z + P[ν](z)` on the upper half-plane for a Poisson-finite `ν`,
then `c = 1` and `ν = 0`. -/
theorem eq_one_and_eq_zero_of_im_eq {c : ℝ} {ν : Measure ℝ} (hν : IsPoissonFinite ν)
    (h : ∀ z ∈ upperHalfPlaneSet, z.im = c * z.im + upperHalfPlanePoissonIntegral ν z) :
    c = 1 ∧ ν = 0 := by
  have h0 : IsPoissonFinite (0 : Measure ℝ) := by simp [isPoissonFinite_iff]
  exact eq_and_eq_of_mul_im_add_upperHalfPlanePoissonIntegral_eq (c := c) (c' := 1) hν h0
    fun z hz ↦ by rw [← h z hz]; simp [upperHalfPlanePoissonIntegral_def]

/-- **`P[δ₀]`.** The Poisson integral of the Dirac mass at `0` is `Im z / (π |z|²)`. -/
theorem upperHalfPlanePoissonIntegral_dirac_zero (z : ℂ) :
    upperHalfPlanePoissonIntegral (Measure.dirac 0) z = z.im / (π * normSq z) := by
  rw [upperHalfPlanePoissonIntegral_def, integral_dirac, upperHalfPlanePoissonKernel_eq]
  simp [normSq_neg]

/-- If `P[δ₀] = c Im z + P[ν]` on the upper half-plane for a Poisson-finite `ν`, then `c = 0` and
`ν = δ₀`. -/
theorem eq_zero_and_eq_dirac_of_poisson_dirac_eq {c : ℝ} {ν : Measure ℝ} (hν : IsPoissonFinite ν)
    (h : ∀ z ∈ upperHalfPlaneSet, upperHalfPlanePoissonIntegral (Measure.dirac 0) z =
      c * z.im + upperHalfPlanePoissonIntegral ν z) :
    c = 0 ∧ ν = Measure.dirac 0 := by
  have hδ : IsPoissonFinite (Measure.dirac (0 : ℝ)) := isPoissonFinite_of_isFiniteMeasure _
  exact eq_and_eq_of_mul_im_add_upperHalfPlanePoissonIntegral_eq (c := c) (c' := 0) hν hδ
    fun z hz ↦ by rw [← h z hz]; simp

/-- For `u = P[δ₀]`, `π y u(iy) = 1` for every `y > 0`: the mass `δ₀(ℝ) = 1` is reached at every
height. -/
theorem pi_mul_mul_upperHalfPlanePoissonIntegral_dirac_zero_mul_I {y : ℝ} (hy : 0 < y) :
    π * y * upperHalfPlanePoissonIntegral (Measure.dirac 0) (y * I) = 1 := by
  rw [pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I, integral_dirac]
  field_simp
  ring

/-- **`u ≡ 1 = P[dx]`.** Lebesgue measure has infinite mass, and `π y P[dx](iy) = π y → ∞`. -/
theorem volume_univ_eq_top_and_tendsto :
    volume (univ : Set ℝ) = ⊤ ∧
      Tendsto (fun y : ℝ ↦ π * y * upperHalfPlanePoissonIntegral volume (y * I)) atTop atTop := by
  refine ⟨Real.volume_univ, ?_⟩
  refine (tendsto_id.const_mul_atTop Real.pi_pos).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [upperHalfPlanePoissonIntegral_volume (by simpa using hy), mul_one, id]

/-- **`u = Re z`** is negative at `-1 + i`, a point of the upper half-plane. -/
theorem re_neg_one_add_I : (-1 + I).re = -1 ∧ (-1 + I) ∈ upperHalfPlaneSet := by
  simp [upperHalfPlaneSet]

end TauCeti.Examples.PositiveHarmonic
