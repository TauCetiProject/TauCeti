/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import TauCeti.MeasureTheory.Constructions.HaarToSphere
public import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Integral.Lebesgue.InitialSegment

/-!
# The Gauss measure of a star-shaped set and the ball of volume one

Let `E` be a finite-dimensional real inner product space. The Gauss density
`exp (-π ‖x‖ ^ 2)` and the indicator of the closed ball `B` of volume one both have total mass
one. This file proves that the Gauss measure of a measurable set `A` that is star-shaped about
the origin (for instance a convex set symmetric about the origin) is at most the volume of
`A ∩ B`:

`∫⁻ x in A, exp (-π ‖x‖ ^ 2) ≤ volume (A ∩ B)`.

This is the case of a single block in Bombieri–Gubler's Lemma C.3.7, which bounds the Gauss
measure of a convex symmetric set by its volume inside a product of balls of volume one. That
lemma is the analytic input to Vaaler's cube-slicing theorem: every `k`-dimensional central slice
of the cube `[-1, 1] ^ n` has `k`-dimensional volume at least `2 ^ k`.

The comparison is made ray by ray, in polar coordinates. A set that is star-shaped about the
origin meets each ray from the origin in an initial segment. Either that segment contains the
segment of the ray inside `B`, or it is contained in it, and the two cases need only
`exp (-π r ^ 2) ≤ 1` and comparison of the two radial integrals. This comparison follows from
comparison of the two total masses, since the radial integrals do not depend on the direction of
the ray. So the argument works for any radial density `φ (‖x‖)` with `φ r ≤ 1` for `r > 0`,
against any closed ball of at least the same total mass, and for any additive Haar measure;
the general statement is
`TauCeti.setLIntegral_comp_norm_le_measure_inter_closedBall`.

With the factor `π` in the exponent the Gauss density has total mass one in every dimension, so
no Gamma function and no closed form for the radius of the ball of volume one is needed.

## Main results

* `TauCeti.setLIntegral_comp_norm_le_measure_inter_closedBall`: for a radial density bounded by
  one away from the origin whose total mass is at most the measure of a closed ball, its integral
  over a measurable set star-shaped about the origin is at most the measure of the set inside
  the ball.
* `TauCeti.lintegral_ofReal_exp_neg_pi_mul_sq_norm`: the Gauss density `exp (-π ‖x‖ ^ 2)` has
  total mass one.
* `TauCeti.setLIntegral_ofReal_exp_neg_pi_mul_sq_norm_le_volume_inter_closedBall`: the Gauss
  measure of a measurable set star-shaped about the origin is at most its volume inside a closed
  ball of volume at least one.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Lemma C.3.7 and Remarks C.3.5, C.3.6.
* J. D. Vaaler, *A geometric inequality with applications to linear forms*, Pacific J. Math. 83
  (1979), 543–553.

The ray-by-ray argument and the normalization of the Gauss density are adapted from the
Apache-2.0 formalization of Vaaler's theorem in `rwst/Subspace-Theorems` (files
`ArithmeticHeights/GaussMeasure.lean` and `ArithmeticHeights/SliceBound.lean`), by Ralf Stephan.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Metric Set
open scoped ENNReal Real

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A point at radius `r > 0` on the ray in direction `u` has norm `r`. -/
private lemma norm_smul_of_mem_sphere (u : sphere (0 : E) 1) {r : ℝ} (hr : r ∈ Ioi 0) :
    ‖r • (u : E)‖ = r := by
  rw [norm_smul, norm_eq_of_mem_sphere u, mul_one, Real.norm_of_nonneg (le_of_lt hr)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Along the ray in direction `u`, the closed ball `closedBall 0 ρ` is the radii `(0, ρ]`. -/
private lemma indicator_closedBall_smul (u : sphere (0 : E) 1) {r ρ : ℝ} (hr : r ∈ Ioi 0) :
    (closedBall (0 : E) ρ).indicator 1 (r • (u : E)) = (Iic ρ).indicator (1 : ℝ → ℝ≥0∞) r := by
  classical
  rw [indicator_apply, indicator_apply, mem_closedBall_zero_iff, norm_smul_of_mem_sphere u hr]
  simp only [mem_Iic, Pi.one_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The comparison along the ray in direction `u`, for a set `A` star-shaped about the origin:
under the hypotheses of `setLIntegral_indicator_mul_le_setLIntegral_indicator_inter_Iic`, the
integral of `φ ‖x‖` over the ray's part in `A` is at most the weight of the ray's part in
`A ∩ closedBall 0 ρ`. -/
private lemma lintegral_ray_le {w φ : ℝ → ℝ≥0∞} {ρ : ℝ}
    (hφ : ∀ r ∈ Ioi (0 : ℝ), φ r ≤ 1)
    (hmass : ∫⁻ r in Ioi (0 : ℝ), w r * φ r ≤ ∫⁻ r in Ioi (0 : ℝ), (Iic ρ).indicator w r)
    {A : Set E} (hA₀ : StarConvex ℝ 0 A) (u : sphere (0 : E) 1) :
    ∫⁻ r in Ioi (0 : ℝ), w r * A.indicator (fun x ↦ φ ‖x‖) (r • (u : E)) ≤
      ∫⁻ r in Ioi (0 : ℝ), w r * (A ∩ closedBall 0 ρ).indicator 1 (r • (u : E)) := by
  -- The radii of the ray that meet `A` form an initial segment.
  set R := (fun r : ℝ ↦ r • (u : E)) ⁻¹' A
  have hR : ∀ ⦃r s⦄, 0 < s → s ≤ r → r ∈ R → s ∈ R := fun r s hs hsr hr ↦ by
    have := hA₀.smul_mem (mem_preimage.1 hr) (div_nonneg hs.le (hs.trans_le hsr).le)
      (div_le_one_of_le₀ hsr (hs.trans_le hsr).le)
    rwa [smul_smul, div_mul_cancel₀ _ (hs.trans_le hsr).ne'] at this
  calc ∫⁻ r in Ioi (0 : ℝ), w r * A.indicator (fun x ↦ φ ‖x‖) (r • (u : E))
      = ∫⁻ r in Ioi (0 : ℝ), R.indicator (fun r ↦ w r * φ r) r := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
        by_cases hrA : r • (u : E) ∈ A
        · rw [indicator_of_mem hrA, indicator_of_mem (s := R) (mem_preimage.2 hrA),
            norm_smul_of_mem_sphere u hr]
        · rw [indicator_of_notMem hrA, indicator_of_notMem (s := R) (mt mem_preimage.1 hrA),
            mul_zero]
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), (R ∩ Iic ρ).indicator w r :=
        setLIntegral_indicator_mul_le_setLIntegral_indicator_inter_Iic hφ hmass hR
    _ = ∫⁻ r in Ioi (0 : ℝ), w r * (A ∩ closedBall 0 ρ).indicator 1 (r • (u : E)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
        rw [inter_indicator_one, Pi.mul_apply, indicator_closedBall_smul u hr]
        by_cases hrA : r ∈ R
        · rw [indicator_of_mem (s := A) hrA, ← indicator_indicator, indicator_of_mem hrA]
          by_cases hrρ : r ∈ Iic ρ <;> simp [hrρ]
        · rw [indicator_of_notMem (s := A) hrA,
            indicator_of_notMem (s := R ∩ Iic ρ) fun h ↦ hrA h.1]
          simp

/-- **The Gauss measure against a ball, for radial densities.** Let `μ` be an additive Haar
measure on a finite-dimensional real normed space, and `φ : ℝ → ℝ≥0∞` a measurable function
bounded by `1` at positive radii such that the radial density `φ ‖x‖` has total mass at most that
of the closed ball `closedBall 0 ρ`. Then for every measurable set `A` that is star-shaped about
the origin, the mass of `φ ‖x‖` on `A` is at most `μ (A ∩ closedBall 0 ρ)`.

With `φ r = exp (-π r ^ 2)` and `μ` the volume of an inner product space this is the case of a
single block in Bombieri–Gubler's Lemma C.3.7; see
`TauCeti.setLIntegral_ofReal_exp_neg_pi_mul_sq_norm_le_volume_inter_closedBall`. -/
theorem setLIntegral_comp_norm_le_measure_inter_closedBall {φ : ℝ → ℝ≥0∞} (hφm : Measurable φ)
    (hφ : ∀ r ∈ Ioi (0 : ℝ), φ r ≤ 1) {ρ : ℝ}
    (hmass : ∫⁻ x, φ ‖x‖ ∂μ ≤ μ (closedBall 0 ρ)) {A : Set E}
    (hA : MeasurableSet A) (hA₀ : StarConvex ℝ 0 A) :
    ∫⁻ x in A, φ ‖x‖ ∂μ ≤ μ (A ∩ closedBall 0 ρ) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the zero space `A` is empty or everything.
    rcases A.eq_empty_or_nonempty with rfl | hne
    · simp
    simpa only [Subsingleton.eq_univ_of_nonempty hne, Measure.restrict_univ, univ_inter] using hmass
  set k := Module.finrank ℝ E - 1
  -- The radial profiles of `φ ‖x‖` and of the ball do not depend on the direction `u`.
  set w : ℝ → ℝ≥0∞ := fun r ↦ ENNReal.ofReal (r ^ k)
  set c := ∫⁻ r in Ioi (0 : ℝ), w r * φ r
  set d := ∫⁻ r in Ioi (0 : ℝ), (Iic ρ).indicator w r
  have hc (u : sphere (0 : E) 1) : ∫⁻ r in Ioi (0 : ℝ), w r * φ ‖r • (u : E)‖ = c :=
    setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ by rw [norm_smul_of_mem_sphere u hr]
  have hd (u : sphere (0 : E) 1) :
      ∫⁻ r in Ioi (0 : ℝ), w r * (closedBall (0 : E) ρ).indicator 1 (r • (u : E)) = d := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
    rw [indicator_closedBall_smul u hr]
    by_cases hrρ : r ∈ Iic ρ <;> simp [hrρ]
  -- The two total masses are `μ.toSphere univ * c` and `μ.toSphere univ * d`, so `c ≤ d`.
  have hcd : c ≤ d := by
    have h₁ : ∫⁻ x, φ ‖x‖ ∂μ = μ.toSphere univ * c := by
      rw [lintegral_eq_lintegral_toSphere_lintegral_Ioi (f := fun x ↦ φ ‖x‖)
        (hφm.comp measurable_norm), lintegral_congr hc, lintegral_const, mul_comm]
    have h₂ : μ (closedBall 0 ρ) = μ.toSphere univ * d := by
      rw [← lintegral_indicator_one measurableSet_closedBall,
        lintegral_eq_lintegral_toSphere_lintegral_Ioi
          (measurable_one.indicator measurableSet_closedBall), lintegral_congr hd,
        lintegral_const, mul_comm]
    rw [h₁, h₂] at hmass
    refine (ENNReal.mul_le_mul_iff_right ?_ (measure_ne_top _ _)).1 hmass
    rw [Ne, measure_univ_eq_zero]
    exact toSphere_ne_zero μ
  -- Compare ray by ray.
  calc ∫⁻ x in A, φ ‖x‖ ∂μ = ∫⁻ x, A.indicator (fun x ↦ φ ‖x‖) x ∂μ :=
        (lintegral_indicator hA _).symm
    _ = ∫⁻ u : sphere (0 : E) 1, (∫⁻ r in Ioi (0 : ℝ),
          w r * A.indicator (fun x ↦ φ ‖x‖) (r • (u : E))) ∂μ.toSphere :=
        lintegral_eq_lintegral_toSphere_lintegral_Ioi ((hφm.comp measurable_norm).indicator hA)
    _ ≤ ∫⁻ u : sphere (0 : E) 1, (∫⁻ r in Ioi (0 : ℝ),
          w r * (A ∩ closedBall 0 ρ).indicator 1 (r • (u : E))) ∂μ.toSphere :=
        lintegral_mono fun u ↦ lintegral_ray_le hφ hcd hA₀ u
    _ = μ (A ∩ closedBall 0 ρ) := by
        rw [← lintegral_eq_lintegral_toSphere_lintegral_Ioi
            (measurable_one.indicator (hA.inter measurableSet_closedBall)),
          lintegral_indicator_one (hA.inter measurableSet_closedBall)]

end Radial

section Gauss

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The Gauss measure is a probability measure.** On a finite-dimensional real inner product
space the density `exp (-π ‖x‖ ^ 2)` has total mass one. -/
theorem lintegral_ofReal_exp_neg_pi_mul_sq_norm :
    ∫⁻ x : E, ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2)) = 1 := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) Real.pi_pos
  rw [div_self Real.pi_ne_zero, Real.one_rpow] at h
  rw [← ofReal_integral_eq_lintegral_ofReal
      (Integrable.of_integral_ne_zero (h ▸ one_ne_zero))
      (ae_of_all _ fun _ ↦ (Real.exp_pos _).le), h, ENNReal.ofReal_one]

/-- **The Gauss measure of a star-shaped set is at most its volume inside a ball of volume
at least one** (Bombieri–Gubler, Lemma C.3.7, for a single ball of volume one). On a
finite-dimensional real inner product space, let `closedBall 0 ρ` have volume at least one.
Then for every measurable set `A` that is star-shaped about the origin, in particular for every
measurable convex set symmetric about the origin,

`∫⁻ x in A, exp (-π ‖x‖ ^ 2) ≤ volume (A ∩ closedBall 0 ρ)`.

Such a radius `ρ` exists by `TauCeti.exists_volume_closedBall_eq_one`. -/
theorem setLIntegral_ofReal_exp_neg_pi_mul_sq_norm_le_volume_inter_closedBall {ρ : ℝ}
    (hρ : 1 ≤ volume (closedBall (0 : E) ρ)) {A : Set E} (hA : MeasurableSet A)
    (hA₀ : StarConvex ℝ 0 A) :
    ∫⁻ x in A, ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2)) ≤ volume (A ∩ closedBall 0 ρ) :=
  setLIntegral_comp_norm_le_measure_inter_closedBall (φ := fun r ↦ ENNReal.ofReal
      (Real.exp (-π * r ^ 2))) (by fun_prop)
    (fun r _ ↦ ENNReal.ofReal_le_one.2 <| Real.exp_le_one_iff.2 <|
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 Real.pi_pos.le) (sq_nonneg r))
    (lintegral_ofReal_exp_neg_pi_mul_sq_norm.le.trans hρ) hA hA₀

end Gauss

end TauCeti
