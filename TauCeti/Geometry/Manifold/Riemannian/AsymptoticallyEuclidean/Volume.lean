/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Distance
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Decay
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Large balls in a manifold with an asymptotically Euclidean end

Let `φ` be an asymptotically Euclidean end of order `t > 0` of a Riemannian manifold `M`, and let
`p` be any point of `M`. This file shows that the Riemannian volume of the metric ball `B_r(p)` is
asymptotically at least the Euclidean volume `ωₙ rⁿ` of a ball of the same radius in `ℝⁿ`:

`liminf_{r → ∞} Vol(B_r(p)) / (ωₙ rⁿ) ≥ 1`.

Two facts about the end combine. The ratio of the Riemannian distance from `p` to `φ x` and of
`‖x‖` tends to `1` (`TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_dist_div_norm`), so for `q < 1`
the ball `B_r(p)` contains the image of the Euclidean annulus `{a < ‖x‖ < q r}` for a fixed `a`
and every `r`. The volume density
`√(det g)` of the end tends to `1`
(`TauCeti.IsAsymptoticallyEuclideanEnd.isSymbolAtInfinity_sqrt_det_pullbackMetricCoeff_sub_one`),
so by the change of variables formula for the Riemannian volume the image of that annulus has
volume at least `q` times its Euclidean volume, which is `qⁿ ωₙ rⁿ` up to a constant.

Only the end enters: nothing is assumed about the rest of `M`, which may have other ends or be
incomplete. Combined with the Bishop–Gromov inequality, which bounds the same ratio by `1` when
the Ricci curvature is nonnegative, this lower bound forces equality in volume comparison, the
input to the rigidity of a complete manifold with nonnegative Ricci curvature and an
asymptotically Euclidean end.

## Main results

* `TauCeti.IsAsymptoticallyEuclideanEnd.setLIntegral_riemannianVolume_image`: change of variables
  along an end, with the volume density `√(det g)` of its metric coefficients as Jacobian.
* `TauCeti.IsAsymptoticallyEuclideanEnd.eventually_mul_volume_ball_le_riemannianVolume_ball`: for
  every `c < 1`, eventually `c ωₙ rⁿ ≤ Vol(B_r(p))`.
* `TauCeti.IsAsymptoticallyEuclideanEnd.one_le_liminf_riemannianVolume_ball_div_volume_ball`:
  `liminf_{r → ∞} Vol(B_r(p)) / (ωₙ rⁿ) ≥ 1`.

## References

* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §8 and §9.
-/

public section

open Bornology Bundle Filter Manifold MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti

namespace IsAsymptoticallyEuclideanEnd

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {t R : ℝ}

section Topological

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {φ : EuclideanSpace ℝ (Fin n) → M}

/-- **Change of variables along an end.** Integrating a nonnegative function `f` over the image
under an end of a measurable subset `s` of the exterior of its ball, against the Riemannian volume,
is integrating `f ∘ φ` over `s` against Lebesgue measure weighted by the volume density
`√(det g)` of the pulled-back metric coefficients. The function `f` need not be measurable. -/
theorem setLIntegral_riemannianVolume_image (h : IsAsymptoticallyEuclideanEnd I t R φ)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s) (hsR : s ⊆ (closedBall 0 R)ᶜ)
    (f : M → ℝ≥0∞) :
    ∫⁻ y in φ '' s, f y ∂riemannianVolume I M =
      ∫⁻ x in s, ENNReal.ofReal √(pullbackMetricCoeff I φ x).det * f (φ x) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hφ : IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ φ s :=
    fun x ↦ h.isLocalDiffeomorphOn ⟨x, hsR x.property⟩
  -- The Riemannian Jacobian of `φ` in the standard basis is the volume density `√(det g)`.
  have hJ (x : EuclideanSpace ℝ (Fin n)) :
      riemannianJacobian (I := I) b.toBasis φ x = √(pullbackMetricCoeff I φ x).det := by
    rw [riemannianJacobian_eq_sqrt_det_gram, pullbackMetricCoeff_def, OrthonormalBasis.coe_toBasis]
  simpa only [b.addHaar_eq_volume, hJ] using
    hφ.setLIntegral_riemannianVolume_image (by simp) hs (h.injOn.mono hsR) b.toBasis f

end Topological

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {φ : EuclideanSpace ℝ (Fin n) → M}

/-- For `0 < q < 1`, the metric ball `B_r(p)` has volume at least `q ^ (n + 1) ωₙ rⁿ`, up to an
additive constant: it contains the image of the annulus `{a < ‖x‖ < q r}`, on which the volume
density is at least `q`. -/
private theorem exists_ofReal_pow_mul_volume_ball_le (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (ht : 0 < t) (p : M) {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ r,
      ENNReal.ofReal (q ^ (n + 1)) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) ≤
        riemannianVolume I M (ball p r) + K := by
  -- Outside a large ball `a`, the volume density is at least `q` and `d(p, φ x) < ‖x‖ / q`.
  have hdens : ∀ᶠ x in cobounded (EuclideanSpace ℝ (Fin n)),
      q ≤ √(pullbackMetricCoeff I φ x).det :=
    ((h.isSymbolAtInfinity_sqrt_det_pullbackMetricCoeff_sub_one ht).tendsto_of_sub
      (neg_lt_zero.2 ht)).eventually (le_mem_nhds hq₁)
  have hdist := (h.tendsto_dist_div_norm ht p).eventually (gt_mem_nhds ((one_lt_inv₀ hq₀).2 hq₁))
  obtain ⟨a, -, ha⟩ :=
    (hasBasis_cobounded_compl_closedBall (0 : EuclideanSpace ℝ (Fin n))).eventually_iff.1
      ((hdens.and hdist).and (eventually_cobounded_le_norm (R + 1)))
  refine ⟨ENNReal.ofReal q * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) a),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne, fun r ↦ ?_⟩
  -- The annulus `{a < ‖x‖ < q r}` lies outside the ball of the end and maps into `B_r(p)`.
  set s := ball (0 : EuclideanSpace ℝ (Fin n)) (q * r) \ closedBall 0 a
  have hsR : s ⊆ (closedBall 0 R)ᶜ := fun x hx ↦ by
    simpa using (lt_add_one R).trans_le (ha hx.2).2
  have hsball : φ '' s ⊆ ball p r := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : 0 < ‖x‖ := h.radius_pos.trans (by simpa using hsR hx)
    have hxr : ‖x‖ < q * r := mem_ball_zero_iff.1 hx.1
    rw [mem_ball_comm, mem_ball]
    calc dist p (φ x) < q⁻¹ * ‖x‖ := (div_lt_iff₀ hx0).1 (ha hx.2).1.2
      _ < r := by rwa [inv_mul_lt_iff₀ hq₀]
  have himage : ENNReal.ofReal q * volume s ≤ riemannianVolume I M (φ '' s) := by
    have hcov := h.setLIntegral_riemannianVolume_image
      (measurableSet_ball.diff measurableSet_closedBall) hsR 1
    simp only [Pi.one_apply, mul_one, setLIntegral_one] at hcov
    rw [hcov, ← setLIntegral_const]
    exact setLIntegral_mono' (measurableSet_ball.diff measurableSet_closedBall)
      fun x hx ↦ ENNReal.ofReal_le_ofReal (ha hx.2).1.1
  -- Scaling the ball, `ωₙ (q r)ⁿ = qⁿ ωₙ rⁿ`, and removing the ball of radius `a`.
  have hscale : volume (ball (0 : EuclideanSpace ℝ (Fin n)) (q * r)) =
      ENNReal.ofReal (q ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
    rw [Measure.addHaar_ball_mul_of_pos _ _ hq₀, finrank_euclideanSpace_fin]
  have hcover : volume (ball (0 : EuclideanSpace ℝ (Fin n)) (q * r)) ≤
      volume s + volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) a) :=
    tsub_le_iff_right.1 le_measure_sdiff
  calc ENNReal.ofReal (q ^ (n + 1)) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r)
      = ENNReal.ofReal q * volume (ball (0 : EuclideanSpace ℝ (Fin n)) (q * r)) := by
        rw [hscale, ← mul_assoc, ← ENNReal.ofReal_mul hq₀.le, pow_succ', mul_comm q]
    _ ≤ ENNReal.ofReal q * volume s +
        ENNReal.ofReal q * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) a) := by
        rw [← mul_add]
        gcongr
    _ ≤ riemannianVolume I M (ball p r) +
        ENNReal.ofReal q * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) a) := by
        gcongr
        exact himage.trans (measure_mono hsball)

/-- **Large balls are at least Euclidean.** On a manifold with an asymptotically Euclidean end of
positive order, for every point `p` and every `c < 1`, the metric ball `B_r(p)` eventually has
Riemannian volume at least `c` times the volume `ωₙ rⁿ` of a Euclidean ball of the same radius. -/
theorem eventually_mul_volume_ball_le_riemannianVolume_ball
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) (p : M) {c : ℝ≥0∞} (hc : c < 1) :
    ∀ᶠ r in atTop,
      c * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) ≤ riemannianVolume I M (ball p r) := by
  -- Choose `0 < q < 1` with `c < q ^ (n + 1)`.
  have hc' : c.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hc.ne_top ENNReal.one_ne_top).2 hc
  have hpow : Tendsto (fun q : ℝ ↦ q ^ (n + 1)) (𝓝[<] 1) (𝓝 1) := by
    simpa using ((continuous_pow (M := ℝ) (n + 1)).tendsto 1).mono_left nhdsWithin_le_nhds
  obtain ⟨q, hqc, hq₀⟩ :=
    ((hpow.eventually (lt_mem_nhds hc')).and (Ioo_mem_nhdsLT zero_lt_one)).exists
  obtain ⟨K, hK, hle⟩ := h.exists_ofReal_pow_mul_volume_ball_le ht p hq₀.1 hq₀.2
  set d := ENNReal.ofReal (q ^ (n + 1))
  have hcd : c < d := by
    rw [← ENNReal.ofReal_toReal hc.ne_top]
    exact (ENNReal.ofReal_lt_ofReal_iff (pow_pos hq₀.1 _)).2 hqc
  -- The Euclidean ball volume `ωₙ rⁿ` tends to infinity, so it eventually absorbs `K`.
  have hlim : Tendsto (fun r : ℝ ↦ (d - c) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r))
      atTop (𝓝 ⊤) := by
    have : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
      have : Nonempty (Fin n) := ⟨⟨0, h.dim_pos⟩⟩
      infer_instance
    simpa [ENNReal.mul_top (tsub_pos_of_lt hcd).ne'] using ENNReal.Tendsto.const_mul (a := d - c)
      (Measure.tendsto_addHaar_ball_atTop volume (0 : EuclideanSpace ℝ (Fin n)))
      (Or.inl ENNReal.top_ne_zero)
  filter_upwards [hlim.eventually (lt_mem_nhds hK.lt_top)] with r hr
  refine ENNReal.le_of_add_le_add_right hK ?_
  calc c * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) + K
      ≤ c * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) +
          (d - c) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) := by gcongr
    _ = d * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
        rw [← add_mul, add_tsub_cancel_of_le hcd.le]
    _ ≤ riemannianVolume I M (ball p r) + K := hle r

/-- **The large-ball volume ratio of an asymptotically Euclidean end.** On a manifold with an
asymptotically Euclidean end of positive order, for every point `p` the ratio of the Riemannian
volume of the metric ball `B_r(p)` to the volume `ωₙ rⁿ` of a Euclidean ball of the same radius has
`liminf` at least `1` as `r → ∞`. -/
theorem one_le_liminf_riemannianVolume_ball_div_volume_ball
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) (p : M) :
    1 ≤ liminf (fun r ↦ riemannianVolume I M (ball p r) /
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) r)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [h.eventually_mul_volume_ball_le_riemannianVolume_ball ht p hc,
    eventually_gt_atTop 0] with r hr hr₀
  exact (ENNReal.le_div_iff_mul_le (Or.inl (measure_ball_pos volume 0 hr₀).ne')
    (Or.inl measure_ball_lt_top.ne)).2 hr

end Metric

end IsAsymptoticallyEuclideanEnd

end TauCeti
