/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Flux
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.WithMetric

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Calculus.ContDiff.SymbolClass.Infinity

/-!
# Smooth spatial Schwarzschild model manifold

Cutting off the conformal profile `(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2))` (`3 ≤ n`) smoothly inside
a ball yields a globally smooth, strictly positive conformal factor
`TauCeti.schwarzschildModelFactor` on `ℝⁿ` and a smooth Riemannian metric
`TauCeti.schwarzschildModelMetric` (non-flat for `c ≠ 0`). On `TauCeti.WithMetric`, this defines a
one-ended finite-ended asymptotically Euclidean manifold of decay order `n - 2` whose ADM
coordinate flux converges to `2 c` (`c = m / 2` corresponds to spatial Schwarzschild mass `m`).

## Main definitions

* `TauCeti.schwarzschildModelFactor` and `TauCeti.schwarzschildModelMetric`: smooth globally
  positive conformal model on `ℝⁿ` (`3 ≤ n`) agreeing outside `{x | ‖x‖ ≤ max 1 (2 |c|) + 1}` with
  `(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2)) • g_eucl` and equal to `1` on `{x | ‖x‖ ≤ max 1 (2 |c|)}`.

## Main results

* `TauCeti.contDiff_schwarzschildModelFactor`, `TauCeti.schwarzschildModelFactor_pos`,
  `TauCeti.schwarzschildModelFactor_eq_one_of_norm_le`, and
  `TauCeti.schwarzschildModelFactor_of_lt_norm`: global smoothness, positivity, interior value `1`,
  and exterior formula for `schwarzschildModelFactor`.
* `TauCeti.isAsymptoticallyEuclideanEnd_schwarzschildModelMetric`,
  `TauCeti.isFiniteEndedAsymptoticallyEuclidean_schwarzschildModelMetric`, and
  `TauCeti.tendsto_normalizedCoordinateFlux_schwarzschildModelMetric`: the Schwarzschild model
  manifold (`3 ≤ n`) is asymptotically Euclidean of order `n - 2` with ADM mass `2 c`.

## References

* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, Trans. Amer. Math. Soc. 377 (2024), 5271-5288 (arXiv:2108.11972), Section 2.
-/

public section

noncomputable section

open Bornology Bundle Filter Metric Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace TauCeti

private def schwarzschildBaseProfile (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if x = 0 then 1
  else 1 + c * Real.smoothTransition (‖x‖ - max 1 (2 * |c|)) * ‖x‖ ^ (2 - (n : ℝ))

/-- Smooth conformal factor on `ℝⁿ` equal on `{x | max 1 (2 |c|) + 1 < ‖x‖}` to
`(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2))` and to `1` on `{x | ‖x‖ ≤ max 1 (2 |c|)}`. For `3 ≤ n` it
is globally smooth and strictly positive. -/
def schwarzschildModelFactor (n : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (schwarzschildBaseProfile n c x) ^ (4 / ((n : ℝ) - 2))

private theorem abs_mul_norm_rpow_le_half {n : ℕ} (hn : 3 ≤ n) (c : ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : max 1 (2 * |c|) < ‖y‖) :
    |c * ‖y‖ ^ (2 - (n : ℝ))| ≤ 1 / 2 := by
  set R₀ : ℝ := max 1 (2 * |c|)
  have h1 : 1 ≤ R₀ := le_max_left _ _
  have hR0 : 0 < R₀ := zero_lt_one.trans_le h1
  have hrp : ‖y‖ ^ (2 - (n : ℝ)) ≤ R₀⁻¹ :=
    (Real.rpow_le_rpow_of_exponent_le (h1.trans hy.le)
      (by linarith [(Nat.ofNat_le_cast.2 hn : (3 : ℝ) ≤ n)] : 2 - (n : ℝ) ≤ -1)).trans <| by
        rw [Real.rpow_neg_one]; exact inv_anti₀ hR0 hy.le
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _)]
  calc |c| * ‖y‖ ^ (2 - (n : ℝ)) ≤ (R₀ / 2) * R₀⁻¹ :=
        mul_le_mul (by linarith [le_max_right 1 (2 * |c|)]) hrp
          (Real.rpow_nonneg (norm_nonneg y) _) (by positivity)
    _ = 1 / 2 := by field_simp [hR0.ne']

private theorem half_le_schwarzschildBaseProfile {n : ℕ} (hn : 3 ≤ n) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (1 / 2 : ℝ) ≤ schwarzschildBaseProfile n c x := by
  set R₀ : ℝ := max 1 (2 * |c|)
  by_cases hx0 : x = 0
  · simp [schwarzschildBaseProfile, hx0]; norm_num
  · simp only [schwarzschildBaseProfile, hx0, ↓reduceIte]
    by_cases hle : ‖x‖ ≤ R₀
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : ‖x‖ - R₀ ≤ 0)]; norm_num
    · have hgt : R₀ < ‖x‖ := lt_of_not_ge hle
      have hst0 := Real.smoothTransition.nonneg (‖x‖ - R₀)
      have hst1 := Real.smoothTransition.le_one (‖x‖ - R₀)
      have habs : |c * Real.smoothTransition (‖x‖ - R₀) * ‖x‖ ^ (2 - (n : ℝ))| ≤ 1 / 2 := by
        calc |c * Real.smoothTransition (‖x‖ - R₀) * ‖x‖ ^ (2 - (n : ℝ))|
            = Real.smoothTransition (‖x‖ - R₀) * |c * ‖x‖ ^ (2 - (n : ℝ))| := by
                rw [abs_mul, abs_mul, abs_of_nonneg hst0, abs_mul]; ring
          _ ≤ 1 * (1 / 2) := mul_le_mul hst1 (abs_mul_norm_rpow_le_half hn c hgt)
                (abs_nonneg _) zero_le_one
          _ = 1 / 2 := one_mul _
      linarith [neg_abs_le (c * Real.smoothTransition (‖x‖ - R₀) * ‖x‖ ^ (2 - (n : ℝ)))]

private theorem contDiff_schwarzschildBaseProfile (n : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (schwarzschildBaseProfile n c) := by
  set R₀ : ℝ := max 1 (2 * |c|)
  have hR0 : 0 < R₀ := zero_lt_one.trans_le (le_max_left _ _)
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · refine contDiffAt_const (c := (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) hR0] with y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · simp [schwarzschildBaseProfile]
    · have hle : ‖y‖ - R₀ ≤ 0 := by linarith [mem_ball_zero_iff.1 hy]
      simp [schwarzschildBaseProfile, hy0, R₀, Real.smoothTransition.zero_of_nonpos hle]
  · have hst : ContDiffAt ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin n) ↦ Real.smoothTransition (‖y‖ - R₀)) x :=
      Real.smoothTransition.contDiff.contDiffAt.comp x
        ((contDiffAt_norm ℝ hx).sub (contDiffAt_const (c := R₀)))
    have hrp : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (2 - (n : ℝ))) x :=
      (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.2 hx)
    refine ((contDiffAt_const (c := (1 : ℝ))).add
      (((contDiffAt_const (c := c)).mul hst).mul hrp)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [schwarzschildBaseProfile, hy, R₀]

/-- In dimension `3 ≤ n`, `schwarzschildModelFactor n c` is globally smooth on `ℝⁿ`. -/
theorem contDiff_schwarzschildModelFactor {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    ContDiff ℝ ∞ (schwarzschildModelFactor n c) :=
  contDiff_iff_contDiffAt.2 fun x ↦
    ((contDiff_schwarzschildBaseProfile n c).contDiffAt.rpow_const_of_ne
      (by linarith [half_le_schwarzschildBaseProfile hn c x]))

/-- In dimension `3 ≤ n`, `schwarzschildModelFactor n c` is everywhere strictly positive. -/
theorem schwarzschildModelFactor_pos {n : ℕ} (hn : 3 ≤ n) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    0 < schwarzschildModelFactor n c x :=
  Real.rpow_pos_of_pos (by linarith [half_le_schwarzschildBaseProfile hn c x]) _

/-- On the closed ball `{x | ‖x‖ ≤ max 1 (2 |c|)}`, `schwarzschildModelFactor n c` is identically
`1`. -/
theorem schwarzschildModelFactor_eq_one_of_norm_le (n : ℕ) (c : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ max 1 (2 * |c|)) :
    schwarzschildModelFactor n c x = 1 := by
  by_cases hx0 : x = 0
  · simp [schwarzschildModelFactor, schwarzschildBaseProfile, hx0]
  · have hle : ‖x‖ - max 1 (2 * |c|) ≤ 0 := sub_nonpos.2 hx
    simp [schwarzschildModelFactor, schwarzschildBaseProfile, hx0,
      Real.smoothTransition.zero_of_nonpos hle]

/-- Outside `{x | ‖x‖ ≤ max 1 (2 |c|) + 1}`, `schwarzschildModelFactor n c` agrees with the exact
conformal Schwarzschild profile `(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2))`. -/
theorem schwarzschildModelFactor_of_lt_norm (n : ℕ) (c : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : max 1 (2 * |c|) + 1 < ‖x‖) :
    schwarzschildModelFactor n c x =
      (1 + c * ‖x‖ ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2)) := by
  have hx0 : x ≠ 0 := norm_pos_iff.1 (by linarith [le_max_left (1 : ℝ) (2 * |c|)])
  have h1 : 1 ≤ ‖x‖ - max 1 (2 * |c|) := by linarith
  simp [schwarzschildModelFactor, schwarzschildBaseProfile, hx0,
    Real.smoothTransition.one_of_one_le h1]

private theorem isSymbolAtInfinity_schwarzschildModelFactor_sub_one {n : ℕ} (hn : 3 ≤ n)
    (c : ℝ) :
    IsSymbolAtInfinity 2 (-((n : ℝ) - 2))
      fun x : EuclideanSpace ℝ (Fin n) ↦ schwarzschildModelFactor n c x - 1 := by
  set q : ℝ := 2 - (n : ℝ)
  -- Compose `x ↦ c * ‖x‖ ^ (2 - n)` with `s ↦ (1 + s) ^ (4 / (n - 2))`, which is smooth at `0`.
  have hcmul : IsSymbolAtInfinity 2 q
      (fun x : EuclideanSpace ℝ (Fin n) ↦ c * ‖x‖ ^ q - 0) := by
    simpa only [smul_eq_mul, sub_zero] using
      (isSymbolAtInfinity_norm_rpow (E := EuclideanSpace ℝ (Fin n)) q).const_smul c
  have hg : ContDiffAt ℝ (max 2 1 : ℕ) (fun s : ℝ ↦ (1 + s) ^ (4 / ((n : ℝ) - 2))) 0 :=
    (contDiffAt_const.add contDiffAt_id).rpow_const_of_ne (by norm_num)
  have hcomp := hcmul.comp_sub (by dsimp [q]; linarith [(Nat.ofNat_le_cast.2 hn : (3 : ℝ) ≤ n)]) hg
  have hq : q = -((n : ℝ) - 2) := by dsimp [q]; ring
  rw [hq] at hcomp
  refine hcomp.congr ?_
  filter_upwards [isBounded_def.1 (isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n)))
    (r := max 1 (2 * |c|) + 1))] with x hx
  rw [schwarzschildModelFactor_of_lt_norm n c (by simpa using hx), ← hq, add_zero, Real.one_rpow]

private theorem exists_schwarzschildModelFactor_decay {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    ∃ C : ℝ, ∀ m ≤ 2, ∀ x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) (max 1 (2 * |c|) + 1))ᶜ,
      ‖iteratedFDeriv ℝ m (fun y ↦ schwarzschildModelFactor n c y - 1) x‖ ≤
        C * ‖x‖ ^ (-((n : ℝ) - 2) - m) := by
  obtain ⟨C, hC⟩ := (isSymbolAtInfinity_schwarzschildModelFactor_sub_one hn c
    ).exists_norm_iteratedFDeriv_le_of_compl_ball (R := max 1 (2 * |c|) + 1)
    (by linarith [le_max_left (1 : ℝ) (2 * |c|)]) fun _ _ ↦
      (((contDiff_schwarzschildModelFactor hn c).sub contDiff_const).of_le (by simp)).contDiffAt
  exact ⟨C, fun m hm x hx ↦ hC m hm x fun hxb ↦ hx (ball_subset_closedBall hxb)⟩

/-- The smooth conformally Euclidean Riemannian metric `schwarzschildModelFactor n c • g_eucl` on
`ℝⁿ` (`3 ≤ n`), equal outside a ball to `(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2)) • g_eucl`. -/
def schwarzschildModelMetric {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  ((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top).rescale
    (schwarzschildModelFactor n c) (contDiff_schwarzschildModelFactor hn c).contMDiff
    (schwarzschildModelFactor_pos hn c)

/-- Unfolding lemma for `TauCeti.schwarzschildModelMetric`. -/
theorem schwarzschildModelMetric_def {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    schwarzschildModelMetric hn c =
      ((riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n))).ofLE (m := ∞) le_top).rescale
        (schwarzschildModelFactor n c) (contDiff_schwarzschildModelFactor hn c).contMDiff
        (schwarzschildModelFactor_pos hn c) :=
  (rfl)

/-- The inner product of `schwarzschildModelMetric hn c` is `schwarzschildModelFactor n c x` times
the standard Euclidean inner product. -/
@[simp]
theorem schwarzschildModelMetric_inner {n : ℕ} (hn : 3 ≤ n) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    (schwarzschildModelMetric hn c).inner x v w =
      schwarzschildModelFactor n c x *
        ⟪NormedSpace.fromTangentSpace x v, NormedSpace.fromTangentSpace x w⟫ := by
  rw [schwarzschildModelMetric_def, ContMDiffRiemannianMetric.rescale_inner,
    ContMDiffRiemannianMetric.ofLE_inner, riemannianMetricVectorSpace_inner]

/-- In dimension `3 ≤ n`, `WithMetric.toWithMetric (schwarzschildModelMetric hn c)` is an
asymptotically Euclidean end of order `n - 2` outside `closedBall 0 (max 1 (2 |c|) + 1)`
(non-flat for `c ≠ 0`). -/
theorem isAsymptoticallyEuclideanEnd_schwarzschildModelMetric {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    IsAsymptoticallyEuclideanEnd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((n : ℝ) - 2)
      (max 1 (2 * |c|) + 1) (WithMetric.toWithMetric (schwarzschildModelMetric hn c)) :=
  isAsymptoticallyEuclideanEnd_toWithMetric_rescale (by omega) (by simp)
    (by linarith [le_max_left (1 : ℝ) (2 * |c|)]) (contDiff_schwarzschildModelFactor hn c)
    (schwarzschildModelFactor_pos hn c) (exists_schwarzschildModelFactor_decay hn c)

/-- In dimension `3 ≤ n`, `WithMetric (schwarzschildModelMetric hn c)` is a one-ended finite-ended
asymptotically Euclidean manifold of order `n - 2`. -/
theorem isFiniteEndedAsymptoticallyEuclidean_schwarzschildModelMetric {n : ℕ} (hn : 3 ≤ n)
    (c : ℝ) :
    IsFiniteEndedAsymptoticallyEuclidean 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((n : ℝ) - 2)
      (fun _ : Unit ↦ max 1 (2 * |c|) + 1)
      (fun _ ↦ WithMetric.toWithMetric (schwarzschildModelMetric hn c)) :=
  isFiniteEndedAsymptoticallyEuclidean_toWithMetric_rescale (by omega) (by simp)
    (by linarith [le_max_left (1 : ℝ) (2 * |c|)]) (contDiff_schwarzschildModelFactor hn c)
    (schwarzschildModelFactor_pos hn c) (exists_schwarzschildModelFactor_decay hn c)

/-- Outside `{x | ‖x‖ ≤ max 1 (2 |c|) + 1}`, the pulled-back metric coefficient matrix of
`schwarzschildModelMetric hn c` equals `(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2)) • 1`. -/
theorem pullbackMetricCoeff_toWithMetric_schwarzschildModelMetric_of_lt_norm {n : ℕ} (hn : 3 ≤ n)
    (c : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : max 1 (2 * |c|) + 1 < ‖x‖) :
    pullbackMetricCoeff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (WithMetric.toWithMetric (schwarzschildModelMetric hn c)) x =
      (1 + c * ‖x‖ ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2)) • 1 := by
  rw [schwarzschildModelMetric_def,
    pullbackMetricCoeff_toWithMetric_rescale_riemannianMetricVectorSpace,
    schwarzschildModelFactor_of_lt_norm n c hx]

/-- **Schwarzschild model manifold ADM mass check.** For every `3 ≤ n` and `c : ℝ`, the smooth
conformally Euclidean manifold `WithMetric (schwarzschildModelMetric hn c)` of order `n - 2`
(non-flat for `c ≠ 0`) has ADM mass `2 c`. -/
theorem tendsto_normalizedCoordinateFlux_schwarzschildModelMetric {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    Tendsto
      (normalizedCoordinateFlux
        (pullbackMetricCoeff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (WithMetric.toWithMetric (schwarzschildModelMetric hn c))))
      atTop (𝓝 (2 * c)) := by
  refine (tendsto_normalizedCoordinateFlux_conformal_one_add_mul_rpow hn c).congr' ?_
  refine (normalizedCoordinateFlux_eventuallyEq_of_eqOn (R := max 1 (2 * |c|) + 1) ?_).symm
  intro x hx
  ext i j
  rw [pullbackMetricCoeff_toWithMetric_schwarzschildModelMetric_of_lt_norm hn c hx]
  simp [Matrix.one_apply]

end TauCeti
