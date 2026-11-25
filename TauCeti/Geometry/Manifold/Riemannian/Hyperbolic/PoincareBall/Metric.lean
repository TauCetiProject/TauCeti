/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Artanh
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.PoincareBall.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.PoincareBall.Geodesic
import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.PoincareBall.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge

/-!
# Riemannian distance, completeness, and hyperbolic structure on the Poincaré ball

In `PoincareBall E`, the hyperbolic Riemannian distance from `0` to `x` is
`2 * artanh ‖x‖ = log ((1 + ‖x‖) / (1 - ‖x‖))`, proved by matching radial geodesic arc length
against the `1`-Lipschitz radial projection `y ↦ 2 * artanh ⟪u, y⟫`. Applying `inversionSwapZero`
gives the two-point distance formulas `dist_eq`, `sinh_half_dist`, and `cosh_dist`. Because `coe`
is `(1 / 2)`-Lipschitz, `PoincareBall E` is metrically complete for every real Hilbert space `E`,
giving geodesic completeness and a bundled `HyperbolicMetric` in every finite dimension `dim E ≥ 0`.

## Main definitions and results

* `TauCeti.PoincareBall.edist_coe_le_half_riemannianEDist`,
  `TauCeti.PoincareBall.lipschitzWith_coe`, `TauCeti.PoincareBall.riemannianEDist_eq`,
  `TauCeti.PoincareBall.dist_eq`, `TauCeti.PoincareBall.sinh_half_dist`, and
  `TauCeti.PoincareBall.cosh_dist`.
* `TauCeti.PoincareBall.completeSpace_of_riemannianMetric`,
  `TauCeti.PoincareBall.isGeodesicallyCompleteAt`, `TauCeti.PoincareBall.hyperbolicMetric`, and
  `TauCeti.PoincareBall.isHyperbolic`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Theorem 6.19.
* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Springer GTM 149 (2019), §4.5.
-/

public section

open Bundle Filter Manifold Set TauCeti.Manifold
open scoped ContDiff ENNReal Manifold NNReal Topology

noncomputable section

namespace TauCeti.PoincareBall

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean extended distance between two points of `PoincareBall E` is at most half their
hyperbolic Riemannian extended distance. -/
theorem edist_coe_le_half_riemannianEDist (x y : PoincareBall E) :
    edist (x : E) (y : E) ≤ (1 / 2 : ℝ≥0) * Manifold.riemannianEDist 𝓘(ℝ, E) x y := by
  refine TauCeti.Manifold.edist_le_mul_riemannianEDist
    (contMDiff_coe.of_le le_top) (by norm_num) (fun z v ↦ ?_) x y
  rw [mvfderiv_coe_apply, ← ofReal_norm, ← ofReal_norm]
  have h' : ‖tangentSpaceCastModel 𝓘(ℝ, E) z v‖ ≤ (1 / 2 : ℝ) * ‖v‖ := by
    linarith [two_mul_norm_le_norm z v]
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos zero_lt_two]
    simp
  exact (ENNReal.ofReal_le_ofReal h').trans_eq
    (by rw [ENNReal.ofReal_mul (by positivity), hhalf])

private def radialProjection (u : E) (y : PoincareBall E) : ℝ :=
  2 * Real.artanh (inner ℝ u (y : E))

private theorem inner_mem_Ioo {u : E} (hu : ‖u‖ ≤ 1) (y : PoincareBall E) :
    inner ℝ u (y : E) ∈ Ioo (-1 : ℝ) 1 := by
  rw [mem_Ioo, ← abs_lt]
  exact ((abs_real_inner_le_norm u (y : E)).trans
    (mul_le_mul_of_nonneg_right hu (norm_nonneg _))).trans_lt (by simpa using norm_lt_one y)

private theorem contMDiff_radialProjection {u : E} (hu : ‖u‖ ≤ 1) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 (radialProjection u) := fun z ↦
  (contDiffAt_const.mul ((innerSL ℝ u).contDiff.contDiffAt.artanh
    (inner_mem_Ioo hu z))).contMDiffAt.comp z (contMDiff_coe.of_le le_top z)

private theorem norm_mvfderiv_radialProjection_le {u : E} (hu : ‖u‖ ≤ 1) (z : PoincareBall E)
    (v : TangentSpace 𝓘(ℝ, E) z) :
    ‖mvfderiv 𝓘(ℝ, E) (radialProjection u) z v‖ ≤ ‖v‖ := by
  have hg : HasFDerivAt (fun p : E ↦ 2 * Real.artanh (inner ℝ u p))
      ((2 * (1 - inner ℝ u (z : E) ^ 2)⁻¹) • innerSL ℝ u) (z : E) :=
    ((Real.hasDerivAt_artanh (inner_mem_Ioo hu z)).const_mul 2).comp_hasFDerivAt (z : E)
      (innerSL ℝ u).hasFDerivAt
  have hcomp : radialProjection u = (fun p : E ↦ 2 * Real.artanh (inner ℝ u p)) ∘ coe := rfl
  rw [hcomp, TauCeti.mvfderiv_comp_apply_of_differentiableAt hg.differentiableAt
    (contMDiff_coe.mdifferentiable (by simp) z) v, hg.fderiv, mvfderiv_coe_apply]
  set w : E := tangentSpaceCastModel 𝓘(ℝ, E) z v
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hinner (p : E) : |inner ℝ u p| ≤ ‖p‖ :=
    (abs_real_inner_le_norm u p).trans
      ((mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans_eq (one_mul _))
  have hsq_le : inner ℝ u (z : E) ^ 2 ≤ ‖(z : E)‖ ^ 2 :=
    (sq_abs (inner ℝ u (z : E))).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hinner (z : E)) 2
  have hden_le : 1 - ‖(z : E)‖ ^ 2 ≤ 1 - inner ℝ u (z : E) ^ 2 := sub_le_sub_left hsq_le 1
  have hden_pos : 0 < 1 - inner ℝ u (z : E) ^ 2 := (one_sub_norm_sq_pos z).trans_le hden_le
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos zero_lt_two, abs_inv, abs_of_pos hden_pos,
    norm_def]
  calc 2 * (1 - inner ℝ u (z : E) ^ 2)⁻¹ * |inner ℝ u w|
      = 2 * |inner ℝ u w| / (1 - inner ℝ u (z : E) ^ 2) := by ring
    _ ≤ 2 * ‖w‖ / (1 - inner ℝ u (z : E) ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hinner w) zero_le_two) hden_pos.le
    _ ≤ 2 * ‖w‖ / (1 - ‖(z : E)‖ ^ 2) :=
      div_le_div_of_nonneg_left (mul_nonneg zero_le_two (norm_nonneg w))
        (one_sub_norm_sq_pos z) hden_le

private theorem le_riemannianEDist_zero_left (x : PoincareBall E) :
    ENNReal.ofReal (2 * Real.artanh ‖(x : E)‖) ≤ Manifold.riemannianEDist 𝓘(ℝ, E) 0 x := by
  let u : E := ‖(x : E)‖⁻¹ • (x : E)
  have hu : ‖u‖ ≤ 1 := by
    rcases eq_or_ne ‖(x : E)‖ 0 with hx0 | hx0 <;> simp [u, norm_smul, hx0]
  have hlip := TauCeti.Manifold.edist_le_mul_riemannianEDist (contMDiff_radialProjection hu)
    one_ne_zero (fun z v ↦ by
      rw [ENNReal.coe_one, one_mul, ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_mvfderiv_radialProjection_le hu z v)) 0 x
  have hx_inner : inner ℝ u (x : E) = ‖(x : E)‖ := by
    dsimp only [u]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    rcases eq_or_ne ‖(x : E)‖ 0 with hx0 | hx0
    · simp [hx0]
    · field_simp [hx0]
  simp only [ENNReal.coe_one, one_mul, radialProjection, coe_zero, inner_zero_right,
    Real.artanh_zero, mul_zero, hx_inner, edist_dist, Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg (mul_nonneg zero_le_two (Real.artanh_nonneg (norm_nonneg _)))] at hlip
  exact hlip

private theorem riemannianEDist_zero_left_le (x : PoincareBall E) :
    Manifold.riemannianEDist 𝓘(ℝ, E) 0 x ≤ ENNReal.ofReal (2 * Real.artanh ‖(x : E)‖) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Manifold.riemannianEDist_self]
  have hx0 : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.2 (coe_eq_zero.not.2 hx)
  let u : E := ‖(x : E)‖⁻¹ • (x : E)
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hx0]
  let T : ℝ := 2 * Real.artanh ‖(x : E)‖
  have hend : radialGeodesic hu T = x := by
    ext
    dsimp only [T, u]
    rw [coe_radialGeodesic, mul_div_cancel_left₀ _ two_ne_zero,
      Real.tanh_artanh ⟨by linarith [norm_nonneg (x : E)], norm_lt_one x⟩, smul_inv_smul₀ hx0]
  exact (Manifold.riemannianEDist_le_pathELength (contMDiff_radialGeodesic (n := 1) hu).contMDiffOn
    (radialGeodesic_zero hu) hend (mul_nonneg zero_le_two
      (Real.artanh_nonneg (norm_nonneg _)))).trans_eq (by rw [pathELength_radialGeodesic, sub_zero])

/-- The hyperbolic Riemannian extended distance from `0` to `x` in `PoincareBall E` is
`ENNReal.ofReal (2 * artanh ‖x‖)`. -/
@[simp] theorem riemannianEDist_zero_left (x : PoincareBall E) :
    Manifold.riemannianEDist 𝓘(ℝ, E) 0 x = ENNReal.ofReal (2 * Real.artanh ‖(x : E)‖) :=
  le_antisymm (riemannianEDist_zero_left_le x) (le_riemannianEDist_zero_left x)

/-- The hyperbolic Riemannian extended distance from `x` to `0` in `PoincareBall E` is
`ENNReal.ofReal (2 * artanh ‖x‖)`. -/
@[simp] theorem riemannianEDist_zero_right (x : PoincareBall E) :
    Manifold.riemannianEDist 𝓘(ℝ, E) x 0 = ENNReal.ofReal (2 * Real.artanh ‖(x : E)‖) := by
  rw [Manifold.riemannianEDist_comm, riemannianEDist_zero_left]

/-- Closed-form hyperbolic Riemannian extended distance between any two points of
`PoincareBall E`. -/
theorem riemannianEDist_eq (x y : PoincareBall E) :
    Manifold.riemannianEDist 𝓘(ℝ, E) x y =
      ENNReal.ofReal (2 * Real.artanh (‖(x : E) - (y : E)‖ /
        Real.sqrt (‖(x : E) - (y : E)‖ ^ 2 + (1 - ‖(x : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2)))) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [riemannianEDist_zero_left]
    congr 3
    have hrad : ‖(0 : E) - (y : E)‖ ^ 2 + (1 - ‖(0 : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2) = 1 := by simp
    rw [coe_zero, hrad, Real.sqrt_one, div_one, zero_sub, norm_neg]
  · rw [← (inversionSwapZero hx).riemannianEDist_eq x y, inversionSwapZero_self hx,
      riemannianEDist_zero_left, norm_coe_inversionSwapZero hx y]

section AmbientMetric

variable [MetricSpace (PoincareBall E)] [IsRiemannianManifold 𝓘(ℝ, E) (PoincareBall E)]

/-- The coordinate inclusion `PoincareBall E → E` is `(1 / 2)`-Lipschitz for the hyperbolic
Riemannian distance. -/
theorem lipschitzWith_coe : LipschitzWith (1 / 2) (coe : PoincareBall E → E) := fun x y ↦ by
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, E)) (M := PoincareBall E)]
  exact edist_coe_le_half_riemannianEDist x y

/-- The hyperbolic Riemannian distance from `0` to `x` in `PoincareBall E` is `2 * artanh ‖x‖`. -/
@[simp] theorem dist_zero_left (x : PoincareBall E) : dist 0 x = 2 * Real.artanh ‖(x : E)‖ := by
  rw [dist_edist, IsRiemannianManifold.out (I := 𝓘(ℝ, E)), riemannianEDist_zero_left,
    ENNReal.toReal_ofReal (mul_nonneg zero_le_two (Real.artanh_nonneg (norm_nonneg _)))]

/-- The hyperbolic Riemannian distance from `x` to `0` in `PoincareBall E` is `2 * artanh ‖x‖`. -/
@[simp] theorem dist_zero_right (x : PoincareBall E) : dist x 0 = 2 * Real.artanh ‖(x : E)‖ := by
  rw [dist_comm, dist_zero_left]

/-- Logarithmic formula for the hyperbolic Riemannian distance from `0` to `x`:
`dist 0 x = log ((1 + ‖x‖) / (1 - ‖x‖))`. -/
theorem dist_zero_left_eq_log (x : PoincareBall E) :
    dist 0 x = Real.log ((1 + ‖(x : E)‖) / (1 - ‖(x : E)‖)) := by
  rw [dist_zero_left, Real.artanh_eq_half_log ⟨by linarith [norm_nonneg (x : E)], norm_le_one x⟩]
  ring

/-- Logarithmic formula for the hyperbolic Riemannian distance from `x` to `0`:
`dist x 0 = log ((1 + ‖x‖) / (1 - ‖x‖))`. -/
theorem dist_zero_right_eq_log (x : PoincareBall E) :
    dist x 0 = Real.log ((1 + ‖(x : E)‖) / (1 - ‖(x : E)‖)) := by
  rw [dist_comm, dist_zero_left_eq_log]

/-- Closed-form hyperbolic Riemannian distance between any two points of `PoincareBall E`. -/
theorem dist_eq (x y : PoincareBall E) :
    dist x y = 2 * Real.artanh (‖(x : E) - (y : E)‖ /
      Real.sqrt (‖(x : E) - (y : E)‖ ^ 2 + (1 - ‖(x : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2))) := by
  rw [dist_edist, IsRiemannianManifold.out (I := 𝓘(ℝ, E)), riemannianEDist_eq,
    ENNReal.toReal_ofReal (mul_nonneg zero_le_two
      (Real.artanh_nonneg (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))))]

/-- Half-distance formula in the Poincaré ball:
`sinh (dist x y / 2) = ‖x - y‖ / √((1 - ‖x‖²)(1 - ‖y‖²))`. -/
theorem sinh_half_dist (x y : PoincareBall E) :
    Real.sinh (dist x y / 2) =
      ‖(x : E) - (y : E)‖ / Real.sqrt ((1 - ‖(x : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2)) := by
  set A : ℝ := ‖(x : E) - (y : E)‖
  set B : ℝ := (1 - ‖(x : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2)
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 < B := mul_pos (one_sub_norm_sq_pos x) (one_sub_norm_sq_pos y)
  have hAB : 0 < A ^ 2 + B := add_pos_of_nonneg_of_pos (sq_nonneg A) hB
  have hsqrtAB : 0 < Real.sqrt (A ^ 2 + B) := Real.sqrt_pos.2 hAB
  let r : ℝ := A / Real.sqrt (A ^ 2 + B)
  have hr_lt : r < 1 := (div_lt_one hsqrtAB).2 <|
    (Real.sqrt_sq hA).symm.trans_lt (Real.sqrt_lt_sqrt (sq_nonneg A) (lt_add_of_pos_right _ hB))
  have hhalf : dist x y / 2 = Real.artanh r := by
    rw [dist_eq]
    dsimp only [r]
    ring
  have h1 : 1 - r ^ 2 = B / (A ^ 2 + B) := by
    dsimp only [r]
    rw [div_pow, Real.sq_sqrt hAB.le]
    field_simp [hAB.ne']
    ring
  rw [hhalf, Real.sinh_artanh ⟨by linarith [div_nonneg hA hsqrtAB.le], hr_lt⟩, h1,
    Real.sqrt_div hB.le]
  dsimp only [r]
  field_simp [hsqrtAB.ne', (Real.sqrt_pos.2 hB).ne']

/-- Hyperbolic cosine formula for the Riemannian distance on `PoincareBall E`:
`cosh (dist x y) = 1 + 2 ‖x - y‖² / ((1 - ‖x‖²)(1 - ‖y‖²))`. -/
theorem cosh_dist (x y : PoincareBall E) :
    Real.cosh (dist x y) =
      1 + 2 * ‖(x : E) - (y : E)‖ ^ 2 / ((1 - ‖(x : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2)) := by
  have hB : 0 ≤ (1 - ‖(x : E)‖ ^ 2) * (1 - ‖(y : E)‖ ^ 2) :=
    mul_nonneg (one_sub_norm_sq_pos x).le (one_sub_norm_sq_pos y).le
  rw [Real.cosh_eq_one_add_two_mul_sinh_half_sq, sinh_half_dist, div_pow, Real.sq_sqrt hB,
    mul_div_assoc]

end AmbientMetric

/-- The Riemannian distance of `PoincareBall E` is metrically complete whenever `E` is complete. -/
theorem completeSpace_of_riemannianMetric [CompleteSpace E] :
    @CompleteSpace (PoincareBall E)
      (MetricSpace.ofRiemannianMetric 𝓘(ℝ, E)
        (PoincareBall E)).toPseudoMetricSpace.toUniformSpace := by
  let : MetricSpace (PoincareBall E) := MetricSpace.ofRiemannianMetric 𝓘(ℝ, E) (PoincareBall E)
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete
    (lipschitzWith_coe.uniformContinuous.comp_cauchySeq hu)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu 1 zero_lt_one
  let R : ℝ := dist 0 (u N) + 1
  have hbound : ∀ᶠ n in atTop, ‖(u n : E)‖ ≤ Real.tanh (R / 2) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hdist : dist 0 (u n) ≤ R :=
      (dist_triangle 0 (u N) (u n)).trans (add_le_add_right (hN N le_rfl n hn).le _)
    rw [dist_zero_left] at hdist
    calc ‖(u n : E)‖
        = Real.tanh (Real.artanh ‖(u n : E)‖) :=
          (Real.tanh_artanh ⟨by linarith [norm_nonneg (u n : E)], norm_lt_one (u n)⟩).symm
      _ ≤ Real.tanh (R / 2) := Real.tanh_strictMono.monotone (by linarith)
  exact ⟨mk p ((le_of_tendsto hp.norm hbound).trans_lt (Real.tanh_lt_one (R / 2))),
    isInducing_coe.tendsto_nhds_iff.2 (by simpa using hp)⟩

end InnerProductSpace

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "J" => 𝓘(ℝ, E)

/-- Radial geodesics from the origin realize the exact Riemannian extended distance for all tangent
vectors `v` at `0`. -/
@[simp 1100] theorem riemannianEDist_zero_riemannianExp (v : TangentSpace J (0 : PoincareBall E)) :
    Manifold.riemannianEDist J 0 (riemannianExp J (PoincareBall E) 0 v) = ‖v‖ₑ := by
  rw [riemannianEDist_zero_left, norm_coe_riemannianExp_zero, Real.artanh_tanh,
    mul_div_cancel₀ _ two_ne_zero, ofReal_norm]

/-- Radial geodesics from the origin realize the exact Riemannian distance for all tangent vectors
`v` at `0`. -/
@[simp 1100] theorem dist_zero_riemannianExp [MetricSpace (PoincareBall E)]
    [IsRiemannianManifold J (PoincareBall E)] (v : TangentSpace J (0 : PoincareBall E)) :
    dist 0 (riemannianExp J (PoincareBall E) 0 v) = ‖v‖ := by
  rw [dist_zero_left, norm_coe_riemannianExp_zero, Real.artanh_tanh, mul_div_cancel₀ _ two_ne_zero]

/-- `PoincareBall E` is geodesically complete at every point. -/
theorem isGeodesicallyCompleteAt (p : PoincareBall E) :
    IsGeodesicallyCompleteAt J (PoincareBall E) p := by
  let : MetricSpace (PoincareBall E) := MetricSpace.ofRiemannianMetric J (PoincareBall E)
  have : CompleteSpace (PoincareBall E) := completeSpace_of_riemannianMetric
  exact isGeodesicallyCompleteAt_of_completeSpace p

/-- The Riemannian exponential map of `PoincareBall E` is defined on the whole tangent space at
every point. -/
@[simp] theorem expDomain_eq_univ (p : PoincareBall E) : expDomain J (PoincareBall E) p = univ :=
  expDomain_eq_univ_iff.2 (isGeodesicallyCompleteAt p)

/-- The bundled complete hyperbolic metric of constant curvature `-1` on `PoincareBall E`, in every
finite dimension `dim E ≥ 0`. -/
def hyperbolicMetric : HyperbolicMetric (I := J) (M := PoincareBall E) where
  metric := { riemannianMetric with contMDiff := riemannianMetric.contMDiff.of_le le_top }
  complete := completeSpace_of_riemannianMetric
  curvature := by
    rw [ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff]
    exact curvatureTensor_eq

/-- Forgetting completeness and curvature recovers the Poincaré ball metric. -/
@[simp] theorem hyperbolicMetric_toRiemannianMetric :
    (hyperbolicMetric (E := E)).metric.toRiemannianMetric = riemannianMetric.toRiemannianMetric :=
  (rfl)

/-- `PoincareBall E` admits a complete hyperbolic metric in every finite dimension `dim E ≥ 0`. -/
theorem isHyperbolic : IsHyperbolic (I := J) (M := PoincareBall E) :=
  TauCeti.isHyperbolic_iff.2 ⟨hyperbolicMetric⟩

end FiniteDimensional

end TauCeti.PoincareBall

end
