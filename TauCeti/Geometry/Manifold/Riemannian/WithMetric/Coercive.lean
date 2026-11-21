/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Coercive
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic

import TauCeti.Analysis.Normed.Operator.Coercive

/-!
# Local distance comparison with a constant metric

A continuous coercive Riemannian metric on a finite-dimensional model space is locally
arbitrarily close, in intrinsic distance, to the constant metric given by its value at a
chosen point. The comparison uses the same open submanifold for both metrics, so every path
stays in the region where the quadratic forms are uniformly comparable. The factor can be
any number greater than one, and the neighborhood works for all pairs of points at once.

## Main results

* `TauCeti.exists_open_riemannianEDist_coercive_comparison` constructs the neighborhood and
  bounds both intrinsic distances using the native `WithMetric` and restriction constructions.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, metric comparison arguments.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Bundle
open scoped ContDiff Manifold NNReal Topology

noncomputable section

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}

/-- Near any point, the intrinsic distances of a coercive metric and its constant value at
that point differ by at most any prescribed factor greater than one, in both directions.
Both distances are taken on the same open submanifold, so paths stay in the region where
the comparison holds. No connectedness or completeness is assumed. -/
theorem exists_open_riemannianEDist_coercive_comparison [FiniteDimensional ℝ F]
    (B : F → F →L[ℝ] F →L[ℝ] ℝ) (hB : ContDiff ℝ n B)
    (hsymm : ∀ x v w, B x v w = B x w v) (hcoercive : ∀ x, IsCoercive (B x))
    (x₀ : F) {r : ℝ≥0} (hr : 1 < r) :
    let g := coerciveRiemannianMetric B hB hsymm hcoercive
    let g₀ := coerciveRiemannianMetric (fun _ : F ↦ B x₀) (contDiff_const (n := n))
      (fun _ ↦ hsymm x₀) (fun _ ↦ hcoercive x₀)
    ∃ U : TopologicalSpace.Opens F, x₀ ∈ U ∧ ∀ x y : U,
      Manifold.riemannianEDist 𝓘(ℝ, F)
          (WithMetric.toWithMetric (g.restrictOpenTangentSpace U) x)
          (WithMetric.toWithMetric (g.restrictOpenTangentSpace U) y) ≤
        r * Manifold.riemannianEDist 𝓘(ℝ, F)
          (WithMetric.toWithMetric (g₀.restrictOpenTangentSpace U) x)
          (WithMetric.toWithMetric (g₀.restrictOpenTangentSpace U) y) ∧
      Manifold.riemannianEDist 𝓘(ℝ, F)
          (WithMetric.toWithMetric (g₀.restrictOpenTangentSpace U) x)
          (WithMetric.toWithMetric (g₀.restrictOpenTangentSpace U) y) ≤
        r * Manifold.riemannianEDist 𝓘(ℝ, F)
          (WithMetric.toWithMetric (g.restrictOpenTangentSpace U) x)
          (WithMetric.toWithMetric (g.restrictOpenTangentSpace U) y) := by
  dsimp only
  have hr' : (1 : ℝ) < r := hr
  have hr0 : 0 < (r : ℝ) := zero_lt_one.trans hr'
  have hnear := (hcoercive x₀).eventually_sqrt_apply_apply_bounds
    hB.continuous.continuousAt hr'
  obtain ⟨s, hs, hsopen, hx₀⟩ := mem_nhds_iff.mp hnear
  have hdiag (z v : F) : 0 ≤ B z v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((hcoercive z).apply_self_pos hv).le
  have hsq (z : F) (hz : z ∈ s) (v : F) :
      B z v v ≤ (r : ℝ) ^ 2 * B x₀ v v ∧
        B x₀ v v ≤ (r : ℝ) ^ 2 * B z v v := by
    obtain ⟨hl, hu⟩ := hs hz v
    constructor
    · simpa only [mul_pow, Real.sq_sqrt (hdiag x₀ v)] using (Real.sqrt_le_iff.mp hu).2
    · have hl' := (div_le_iff₀ hr0).mp hl
      simpa only [mul_pow, Real.sq_sqrt (hdiag z v), mul_comm] using
        (Real.sqrt_le_iff.mp hl').2
  let U : TopologicalSpace.Opens F := ⟨s, hsopen⟩
  refine ⟨U, hx₀, fun x y ↦ ⟨?_, ?_⟩⟩
  · apply WithMetric.riemannianEDist_toWithMetric_le_mul_toWithMetric
      (ne_of_gt (zero_lt_one.trans hr))
    intro z v
    simpa only [Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
      coerciveRiemannianMetric_inner] using
      (hsq z z.property (tangentSpaceCastModel 𝓘(ℝ, F) z.val
        (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, F)) z v))).1
  · apply WithMetric.riemannianEDist_toWithMetric_le_mul_toWithMetric
      (ne_of_gt (zero_lt_one.trans hr))
    intro z v
    simpa only [Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner,
      coerciveRiemannianMetric_inner] using
      (hsq z z.property (tangentSpaceCastModel 𝓘(ℝ, F) z.val
        (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, F)) z v))).2


end TauCeti
