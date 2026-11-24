/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Asymptotics
public import TauCeti.Geometry.Manifold.Riemannian.Distance
import TauCeti.Analysis.Normed.Module.Ball.Exterior
import TauCeti.Topology.MetricSpace.Annulus

/-!
# Riemannian distance estimates on asymptotically Euclidean ends

On an extended-metric Riemannian manifold `M`, the uniform order-`0` metric bound of an
asymptotically Euclidean end `φ` of order `t` on `(closedBall 0 R)ᶜ` gives a uniform operator
bound on `mfderiv φ` on every finite exterior annulus `{z | R < ‖z‖ ≤ R₁}`. Integrating this
bound along radial segments yields radial extended-distance estimates to spheres
(`edist_image_radial_le`), which imply that the image `φ '' ((closedBall 0 R)ᶜ ∩ closedBall 0 R')`
of every exterior collar is totally bounded
(`IsAsymptoticallyEuclideanEnd.totallyBounded_image_compl_inter_closedBall`).

This single-end total-boundedness result is the geometric ingredient used to show that larger-radius
truncations of a finite-ended asymptotically Euclidean manifold remain compact-complement on
complete Riemannian manifolds.

## Main results

* `TauCeti.IsAsymptoticallyEuclideanEnd.totallyBounded_image_compl_inter_closedBall`: on an
  extended-metric Riemannian manifold, the image of any exterior collar
  `(closedBall 0 R)ᶜ ∩ closedBall 0 R'` under an asymptotically Euclidean end is totally bounded.

## References

* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  661–693.
* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, Trans. Amer. Math. Soc. 377 (2024), 5271–5288, arXiv:2108.11972v2.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 8.
-/

public section

noncomputable section

open Bundle Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace TauCeti

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

namespace IsAsymptoticallyEuclideanEnd

variable {t : ℝ}

/-- Pointwise operator bound on `mfderiv` of an asymptotically Euclidean end on an annulus
`R < ‖z‖ ≤ R₁` from its order-0 diagonal metric bounds at `z`. -/
private theorem norm_mfderiv_le_of_compl_closedBall {R R₁ C : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}
    (hR : 0 < R)
    (hzC : ∀ i : Fin n,
      ‖iteratedFDeriv ℝ 0 (fun y ↦ (pullbackMetricCoeff I φ y - 1) i i) z‖ ≤ C * ‖z‖ ^ (-t))
    (hz_gt : R < ‖z‖) (hz_le : ‖z‖ ≤ R₁) (v : EuclideanSpace ℝ (Fin n)) :
    ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z ((NormedSpace.fromTangentSpace z).symm v)‖ ≤
      ‖v‖ * (n : ℝ) * Real.sqrt (1 + max C 0 * max (R ^ (-t)) (R₁ ^ (-t))) := by
  let M₀ : ℝ := Real.sqrt (1 + max C 0 * max (R ^ (-t)) (R₁ ^ (-t)))
  have hbasis_norm (i : Fin n) :
      ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z
        ((NormedSpace.fromTangentSpace z).symm (EuclideanSpace.basisFun (Fin n) ℝ i))‖ ≤ M₀ := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [NormedSpace.fromTangentSpace_symm_apply, ← real_inner_self_eq_norm_sq,
      ← pullbackMetricCoeff_apply]
    have hz0 := abs_pullbackMetricCoeff_sub_one_le (hzC i)
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at hz0
    have hrpow : ‖z‖ ^ (-t) ≤ max (R ^ (-t)) (R₁ ^ (-t)) := by
      rcases le_total 0 (-t) with ht0 | ht0
      · exact (Real.rpow_le_rpow (norm_nonneg z) hz_le ht0).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_nonpos hR hz_gt.le ht0).trans (le_max_left _ _)
    have hle1 : pullbackMetricCoeff I φ z i i - 1 ≤ max C 0 * max (R ^ (-t)) (R₁ ^ (-t)) :=
      (le_abs_self _).trans <| hz0.trans <|
        mul_le_mul (le_max_left C 0) hrpow (Real.rpow_nonneg (norm_nonneg z) _) (le_max_right C 0)
    linarith
  have hsum : v = ∑ i : Fin n,
      ((EuclideanSpace.basisFun (Fin n) ℝ).repr v i) • EuclideanSpace.basisFun (Fin n) ℝ i :=
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
  have hmf :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z ((NormedSpace.fromTangentSpace z).symm v) =
        ∑ i : Fin n, ((EuclideanSpace.basisFun (Fin n) ℝ).repr v i) •
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z
            ((NormedSpace.fromTangentSpace z).symm (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
    conv_lhs => rw [hsum]
    simp only [map_sum, map_smul]
  rw [hmf]
  calc ‖∑ i : Fin n, ((EuclideanSpace.basisFun (Fin n) ℝ).repr v i) •
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z
            ((NormedSpace.fromTangentSpace z).symm (EuclideanSpace.basisFun (Fin n) ℝ i))‖
      ≤ ∑ i : Fin n, ‖((EuclideanSpace.basisFun (Fin n) ℝ).repr v i) •
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I φ z
            ((NormedSpace.fromTangentSpace z).symm (EuclideanSpace.basisFun (Fin n) ℝ i))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖v‖ * M₀ := Finset.sum_le_sum fun i _ ↦ by
        rw [norm_smul, Real.norm_eq_abs]
        have hcoord : |(EuclideanSpace.basisFun (Fin n) ℝ).repr v i| ≤ ‖v‖ := by
          simpa using PiLp.norm_apply_le v i
        exact mul_le_mul hcoord (hbasis_norm i) (norm_nonneg _) (norm_nonneg v)
    _ = ‖v‖ * (n : ℝ) * M₀ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- Radial extended-distance estimate from `φ x` (`R < ‖x‖ < R₀ ≤ R₁`) to the outer sphere
`sphere 0 R₀`. -/
private theorem edist_image_radial_le {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    {R R₀ R₁ C : ℝ} (hR₀ : R₀ ≤ R₁)
    {φ : EuclideanSpace ℝ (Fin n) → M} (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (hC : ∀ z ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, ∀ i : Fin n,
      ‖iteratedFDeriv ℝ 0 (fun y ↦ (pullbackMetricCoeff I φ y - 1) i i) z‖ ≤ C * ‖z‖ ^ (-t))
    {x : EuclideanSpace ℝ (Fin n)} (hxR : R < ‖x‖) (hxR₀ : ‖x‖ < R₀) :
    edist (φ x) (φ ((R₀ / ‖x‖) • x)) ≤
      ENNReal.ofReal ((R₀ - ‖x‖) * (n : ℝ) *
        Real.sqrt (1 + max C 0 * max (R ^ (-t)) (R₁ ^ (-t)))) := by
  have hx_pos : 0 < ‖x‖ := h.radius_pos.trans hxR
  let y : EuclideanSpace ℝ (Fin n) := (R₀ / ‖x‖) • x
  have h1 : 1 ≤ R₀ / ‖x‖ := (one_le_div hx_pos).2 hxR₀.le
  have hseg (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ segment ℝ x y) :
      R < ‖z‖ ∧ ‖z‖ ≤ R₁ := by
    obtain ⟨hlo, hhi⟩ := norm_mem_segment_smul_bounds h1 hz
    refine ⟨hxR.trans_le hlo, hhi.trans ?_⟩
    rw [div_mul_cancel₀ _ hx_pos.ne']
    exact hR₀
  have hdiff : ∀ z ∈ segment ℝ x y, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I 1 φ z :=
    fun z hz ↦ (h.contMDiffOn.contMDiffAt
      (isClosed_closedBall.isOpen_compl.mem_nhds (by simpa using (hseg z hz).1))).of_le (by simp)
  have hyx : y - x = (R₀ / ‖x‖ - 1) • x := by
    simp only [y, sub_smul, one_smul]
  have hnorm_yx : ‖y - x‖ = R₀ - ‖x‖ := by
    rw [hyx, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 h1), sub_mul,
      div_mul_cancel₀ _ hx_pos.ne', one_mul]
  refine IsRiemannianManifold.edist_le_of_norm_mfderiv_le hdiff fun z hz ↦ ?_
  rw [← NormedSpace.fromTangentSpace_symm_apply z (y - x), ← hnorm_yx]
  exact norm_mfderiv_le_of_compl_closedBall h.radius_pos
    (hC z (by simpa using (hseg z hz).1)) (hseg z hz).1 (hseg z hz).2 (y - x)

/-- On an extended-metric Riemannian manifold, the image of the collar
`(closedBall 0 R)ᶜ ∩ closedBall 0 R'` under an asymptotically Euclidean end is totally bounded,
since it is approximated in `edist` by compact inner truncations using the uniform radial
derivative bound. -/
theorem totallyBounded_image_compl_inter_closedBall {M : Type*} [PseudoEMetricSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] {R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (R' : ℝ) :
    TotallyBounded (φ '' ((closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ ∩ closedBall 0 R')) := by
  rw [EMetric.totallyBounded_iff]
  intro ε hε
  -- Step 1: Choose a radial collar thickness `0 < η ≤ 1` so radial travel across `η` is `< ε / 2`.
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  set R₁ : ℝ := R + 1
  let M₁ : ℝ := (n : ℝ) * Real.sqrt (1 + max C 0 * max (R ^ (-t)) (R₁ ^ (-t)))
  have hM₁ : 0 ≤ M₁ := mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)
  obtain ⟨r, -, hr0, hr_lt⟩ := ENNReal.lt_iff_exists_real_btwn.1 (ENNReal.half_pos hε.ne')
  have hr0' : 0 < r := ENNReal.ofReal_pos.1 hr0
  obtain ⟨c, hc, hcM⟩ := exists_pos_mul_lt hr0' M₁
  let η : ℝ := min 1 c
  have hη_pos : 0 < η := lt_min zero_lt_one hc
  have hη_le1 : η ≤ 1 := min_le_left _ _
  have hη_mul : ENNReal.ofReal (η * M₁) < ε / 2 :=
    (ENNReal.ofReal_le_ofReal <| by
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hM₁).trans hcM.le).trans_lt hr_lt
  -- Step 2: Cover the compact annulus `{z | R + η ≤ ‖z‖ ≤ max R' (R + η)}` by `(ε / 2)`-balls.
  let A : Set (EuclideanSpace ℝ (Fin n)) := {z | R + η ≤ ‖z‖ ∧ ‖z‖ ≤ max R' (R + η)}
  have hA_comp : IsCompact A := by
    simpa only [sub_zero] using
      TauCeti.isCompact_setOf_le_norm_sub_le (0 : EuclideanSpace ℝ (Fin n)) (R + η)
        (max R' (R + η))
  have hA_sub : A ⊆ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := fun z hz ↦ by
    simp only [mem_compl_iff, mem_closedBall_zero_iff, not_le]
    linarith [hz.1]
  have hφA_tb : TotallyBounded (φ '' A) :=
    (hA_comp.image_of_continuousOn (h.contMDiffOn.continuousOn.mono hA_sub)).totallyBounded
  obtain ⟨t₀, ht₀_fin, ht₀_cov⟩ :=
    EMetric.totallyBounded_iff.1 hφA_tb (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨t₀, ht₀_fin, ?_⟩
  -- Step 3: Points with `R + η ≤ ‖x‖` lie directly in `A`; points with `R < ‖x‖ < R + η`
  -- lie within `ε / 2` of their radial projection onto `‖z‖ = R + η`.
  rintro _ ⟨x, ⟨hxR, hxR'⟩, rfl⟩
  have hxR_lt : R < ‖x‖ := by simpa using hxR
  rcases le_or_gt (R + η) ‖x‖ with hx_ge | hx_lt
  · have hxA : x ∈ A := ⟨hx_ge, (mem_closedBall_zero_iff.1 hxR').trans (le_max_left _ _)⟩
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (ht₀_cov ⟨x, hxA, rfl⟩)
    exact mem_iUnion₂.2 ⟨p, hp, Metric.eball_subset_eball ENNReal.half_le_self hxp⟩
  · have hx_pos : 0 < ‖x‖ := h.radius_pos.trans hxR_lt
    have hRη_pos : 0 < R + η := by linarith [h.radius_pos]
    let y : EuclideanSpace ℝ (Fin n) := ((R + η) / ‖x‖) • x
    have hy_norm : ‖y‖ = R + η := by
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg hRη_pos.le hx_pos.le),
        div_mul_cancel₀ _ hx_pos.ne']
    have hyA : y ∈ A := ⟨hy_norm.ge, hy_norm.le.trans (le_max_right _ _)⟩
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 (ht₀_cov ⟨y, hyA, rfl⟩)
    have hC0 : ∀ z ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, ∀ i : Fin n,
        ‖iteratedFDeriv ℝ 0 (fun w ↦ (pullbackMetricCoeff I φ w - 1) i i) z‖ ≤ C * ‖z‖ ^ (-t) :=
      fun z hz i ↦ by simpa only [Nat.cast_zero, sub_zero] using hC 0 (Nat.zero_le 2) i i z hz
    have hed : edist (φ x) (φ y) < ε / 2 := by
      have h1 : edist (φ x) (φ y) ≤ ENNReal.ofReal ((R + η - ‖x‖) * M₁) := by
        simpa only [mul_assoc] using
          edist_image_radial_le (R₁ := R₁) (by linarith) h hC0 hxR_lt hx_lt
      have h2 : (R + η - ‖x‖) * M₁ ≤ η * M₁ :=
        mul_le_mul_of_nonneg_right (by linarith) hM₁
      exact h1.trans_lt ((ENNReal.ofReal_le_ofReal h2).trans_lt hη_mul)
    refine mem_iUnion₂.2 ⟨p, hp, ?_⟩
    rw [Metric.mem_eball] at hyp ⊢
    exact (edist_triangle _ (φ y) _).trans_lt
      ((ENNReal.add_lt_add hed hyp).trans_eq (ENNReal.add_halves ε))

end IsAsymptoticallyEuclideanEnd

end TauCeti

end
