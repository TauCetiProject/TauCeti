/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FrechetMean.Basic
public import TauCeti.Topology.MetricSpace.CATZero

/-!
# Quadratic Fréchet barycenters in CAT(0) spaces

In a CAT(0) space the squared distance from a fixed point is strongly convex along geodesic
segments (`TauCeti.IsGeodesicSegment.dist_sq_le`). Integrating this against a measure `μ` shows
that the quadratic Fréchet functional `x ↦ ∫ d(x, y)² dμ(y)` is strongly convex along geodesic
segments as well, with modulus proportional to the total mass of `μ`. Two quadratic barycenters
would therefore have a midpoint with strictly smaller Fréchet functional, unless they are at
distance zero: a nonzero measure on a CAT(0) metric space has at most one quadratic Fréchet
barycenter.

Uniqueness needs nonpositive curvature. In a general geodesic space, even a proper one, a
probability measure can have several quadratic barycenters: the uniform law on two antipodal
points of a circle has two.

## Main results

* `TauCeti.IsGeodesicSegment.frechetPower_two_add_le` — strong convexity of the quadratic Fréchet
  functional along a geodesic segment of a CAT(0) space.
* `TauCeti.IsFrechetBarycenter.dist_eq_zero` — two quadratic Fréchet barycenters of a nonzero
  measure on a CAT(0) space are at distance zero.
* `TauCeti.subsingleton_frechetBarycenters_two` — on a CAT(0) metric space, a nonzero measure has
  at most one quadratic Fréchet barycenter.

## References

* K.-T. Sturm, *Probability measures on metric spaces of nonpositive curvature*, in *Heat
  Kernels and Analysis on Manifolds, Graphs, and Metric Spaces*, Contemp. Math. 338 (2003),
  357--390, Section 4.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [IsCATZeroSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- **Strong convexity of the quadratic Fréchet functional in a CAT(0) space.** Along a geodesic
segment `γ` from `x` to `y`, the functional `F(z) = ∫ d(z, w)² dμ(w)` satisfies
`F(γ t) + t (1 - t) d(x, y)² μ(X) ≤ (1 - t) F(x) + t F(y)` for every `t ∈ [0, 1]`. -/
theorem IsGeodesicSegment.frechetPower_two_add_le {γ : ℝ → X} {x y : X}
    (hγ : IsGeodesicSegment γ x y) (μ : Measure X) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    frechetPower 2 μ (γ t) + ENNReal.ofReal (t * (1 - t)) * edist x y ^ 2 * μ univ ≤
      ENNReal.ofReal (1 - t) * frechetPower 2 μ x + ENNReal.ofReal t * frechetPower 2 μ y := by
  have hmeas (z : X) : Measurable fun w => edist z w ^ 2 :=
    (continuous_const.edist continuous_id).measurable.pow_const 2
  have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht.2
  -- The pointwise inequality `TauCeti.IsGeodesicSegment.dist_sq_le`, moved to `ℝ≥0∞`.
  have hpt (w : X) : edist (γ t) w ^ 2 + ENNReal.ofReal (t * (1 - t)) * edist x y ^ 2 ≤
      ENNReal.ofReal (1 - t) * edist x w ^ 2 + ENNReal.ofReal t * edist y w ^ 2 := by
    simp only [edist_dist, ← ENNReal.ofReal_pow dist_nonneg,
      ← ENNReal.ofReal_mul (mul_nonneg ht.1 h1t), ← ENNReal.ofReal_mul h1t,
      ← ENNReal.ofReal_mul ht.1]
    rw [← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (mul_nonneg ht.1 h1t) (sq_nonneg _)),
      ← ENNReal.ofReal_add (mul_nonneg h1t (sq_nonneg _)) (mul_nonneg ht.1 (sq_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hγ.dist_sq_le w ht
    rw [dist_comm w, dist_comm w, dist_comm w] at this
    linarith
  simp only [frechetPower_def, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  calc ∫⁻ w, edist (γ t) w ^ 2 ∂μ + ENNReal.ofReal (t * (1 - t)) * edist x y ^ 2 * μ univ
      = ∫⁻ w, edist (γ t) w ^ 2 + ENNReal.ofReal (t * (1 - t)) * edist x y ^ 2 ∂μ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ ∫⁻ w, ENNReal.ofReal (1 - t) * edist x w ^ 2 + ENNReal.ofReal t * edist y w ^ 2 ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (1 - t) * ∫⁻ w, edist x w ^ 2 ∂μ +
          ENNReal.ofReal t * ∫⁻ w, edist y w ^ 2 ∂μ := by
        rw [lintegral_add_left ((hmeas x).const_mul _), lintegral_const_mul _ (hmeas x),
          lintegral_const_mul _ (hmeas y)]

/-- **Two quadratic barycenters are at distance zero.** On a CAT(0) space, two quadratic
Fréchet barycenters of a nonzero measure are at distance zero. -/
theorem IsFrechetBarycenter.dist_eq_zero {μ : Measure X} [NeZero μ] {x y : X}
    (hx : IsFrechetBarycenter 2 μ x) (hy : IsFrechetBarycenter 2 μ y) : dist x y = 0 := by
  have hm (z : X) : AEMeasurable (fun w => edist z w) μ :=
    (continuous_const.edist continuous_id).measurable.aemeasurable
  rw [isFrechetBarycenter_iff_forall_frechetPower_le two_ne_zero ENNReal.ofNat_ne_top (hm x) hm]
    at hx
  rw [isFrechetBarycenter_iff_forall_frechetPower_le two_ne_zero ENNReal.ofNat_ne_top (hm y) hm]
    at hy
  have hxtop : frechetPower 2 μ x ≠ ⊤ := by
    rw [← frechetRadius_rpow_eq_frechetPower two_ne_zero ENNReal.ofNat_ne_top (hm x)]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hx.1
  have hxy : frechetPower 2 μ y = frechetPower 2 μ x := le_antisymm (hy.2 x) (hx.2 y)
  -- Compare both barycenters with the midpoint of a geodesic segment joining them.
  obtain ⟨γ, hγ⟩ := IsGeodesicSpace.exists_isGeodesicSegment x y
  have key := hγ.frechetPower_two_add_le μ (t := 2⁻¹) ⟨by norm_num, by norm_num⟩
  have hhalf : ENNReal.ofReal (1 - 2⁻¹) * frechetPower 2 μ x +
      ENNReal.ofReal 2⁻¹ * frechetPower 2 μ x = frechetPower 2 μ x + 0 := by
    rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  rw [hxy, hhalf] at key
  have hmid : frechetPower 2 μ x + ENNReal.ofReal (2⁻¹ * (1 - 2⁻¹)) * edist x y ^ 2 * μ univ ≤
      frechetPower 2 μ (γ 2⁻¹) + ENNReal.ofReal (2⁻¹ * (1 - 2⁻¹)) * edist x y ^ 2 * μ univ := by
    gcongr
    exact hx.2 _
  have hzero := ENNReal.le_of_add_le_add_left hxtop (hmid.trans key)
  norm_num [Measure.measure_univ_eq_zero, NeZero.ne μ, ENNReal.ofReal_eq_zero, edist_dist] at hzero
  exact le_antisymm hzero dist_nonneg

/-- **Uniqueness of quadratic barycenters in CAT(0) spaces.** On a CAT(0) metric space, a nonzero
measure has at most one quadratic Fréchet barycenter. -/
theorem subsingleton_frechetBarycenters_two {X : Type*} [MetricSpace X] [IsCATZeroSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [NeZero μ] :
    (frechetBarycenters 2 μ).Subsingleton := fun _ hx _ hy =>
  dist_eq_zero.1 ((mem_frechetBarycenters.1 hx).dist_eq_zero (mem_frechetBarycenters.1 hy))

end TauCeti
