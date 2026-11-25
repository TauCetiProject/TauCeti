/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.PositiveHarmonic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Uniqueness
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Checks for the representation of positive harmonic functions on the half-plane

A nonnegative harmonic function on the upper half-plane is `c Im z + P[ν](z)` for a unique `c ≥ 0`
and a unique Poisson-finite measure `ν`
(`TauCeti.exists_eq_mul_im_add_upperHalfPlanePoissonIntegral`,
`TauCeti.eq_and_eq_of_mul_im_add_upperHalfPlanePoissonIntegral_eq`). Worked examples of the
representation and of its hypotheses, in the namespace `TauCeti.Examples.PositiveHarmonic`:

* `u = Im z` has `c = 1` and `ν = 0` (`eq_one_and_eq_zero_of_im_eq`);
* `u = P[δ₀]`, `u(z) = Im z / (π |z|²)`, has `c = 0` and `ν = δ₀`, and `π y u(iy) = 1 = δ₀(ℝ)` for
  every `y > 0` (`upperHalfPlanePoissonIntegral_dirac_zero`,
  `eq_zero_and_eq_dirac_of_upperHalfPlanePoissonIntegral_dirac_eq`,
  `pi_mul_mul_upperHalfPlanePoissonIntegral_dirac_zero_mul_I`);
* `u ≡ 1 = P[dx]` has a measure of infinite mass, and `π y u(iy) = π y → ∞`
  (`volume_univ_eq_top_and_tendsto_pi_mul_mul_upperHalfPlanePoissonIntegral_volume_mul_I`);
* `u = Re z` is harmonic on the upper half-plane but not nonnegative there, so positivity is a
  hypothesis (`harmonicOnNhd_re_and_not_forall_re_nonneg`).
-/

public section

open Complex InnerProductSpace MeasureTheory Set Filter Topology
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
  rw [upperHalfPlanePoissonIntegral_dirac, upperHalfPlanePoissonKernel_eq]
  simp [normSq_neg]

/-- If `P[δ₀] = c Im z + P[ν]` on the upper half-plane for a Poisson-finite `ν`, then `c = 0` and
`ν = δ₀`. -/
theorem eq_zero_and_eq_dirac_of_upperHalfPlanePoissonIntegral_dirac_eq {c : ℝ} {ν : Measure ℝ}
    (hν : IsPoissonFinite ν)
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
theorem volume_univ_eq_top_and_tendsto_pi_mul_mul_upperHalfPlanePoissonIntegral_volume_mul_I :
    volume (univ : Set ℝ) = ⊤ ∧
      Tendsto (fun y : ℝ ↦ π * y * upperHalfPlanePoissonIntegral volume (y * I)) atTop atTop := by
  refine ⟨Real.volume_univ, ?_⟩
  refine (tendsto_id.const_mul_atTop Real.pi_pos).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [upperHalfPlanePoissonIntegral_volume (by simpa using hy), mul_one, id]

/-- **`u = Re z`** is harmonic on the upper half-plane but not nonnegative there (it is `-1` at
`-1 + i`), so it satisfies every hypothesis of
`TauCeti.exists_eq_mul_im_add_upperHalfPlanePoissonIntegral` except positivity. -/
theorem harmonicOnNhd_re_and_not_forall_re_nonneg :
    HarmonicOnNhd (fun z : ℂ ↦ z.re) upperHalfPlaneSet ∧ ¬∀ z ∈ upperHalfPlaneSet, 0 ≤ z.re := by
  refine ⟨fun z _ ↦ (analyticAt_id (𝕜 := ℂ)).harmonicAt_re, fun h ↦ ?_⟩
  have := h (-1 + I) (by simp [upperHalfPlaneSet])
  norm_num at this

end TauCeti.Examples.PositiveHarmonic
