/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Convexity.Basic
public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.Conformal
import TauCeti.Geometry.Manifold.Instances.ClosedBall.Boundary

/-!
# A family of conformal metrics on the closed unit ball crossing the convexity threshold

Let `B` be the closed unit ball of a real inner product space `E` of dimension `n + 1`, with its
Euclidean metric `g` (`TauCeti.closedBallEuclideanMetric`), and for `s : ℝ` let
`g_s = e^{-2s|x|²} g`. By the conformal law of the second fundamental form, at every point of the
unit sphere `∂B`,

    II^{g_s} = e^{-s} (1 - 2s) h

(`TauCeti.boundarySecondFundamentalForm_closedBall_rescale_exp_neg_two_mul_norm_sq_smul`), where
`h` is the induced metric of `g`. Hence, for `n ≥ 1`:

* `∂B` is strictly convex for `g_s` exactly when `s < 1/2`
  (`TauCeti.isStrictlyConvexBoundary_closedBall_rescale_exp_iff`), an open set of parameters
  (`TauCeti.isOpen_setOf_isStrictlyConvexBoundary_closedBall_rescale_exp`);
* `∂B` is convex for `g_s` at a point exactly when `s ≤ 1/2`
  (`TauCeti.isConvexAt_closedBall_rescale_exp_iff`), and strictly concave exactly when `s > 1/2`
  (`TauCeti.isStrictlyConcaveAt_closedBall_rescale_exp_iff`);
* at the threshold `s = 1/2` the second fundamental form vanishes
  (`TauCeti.boundarySecondFundamentalForm_closedBall_rescale_exp_neg_norm_sq`).

This is the family Check of RiemannianManifoldsWithConvexBoundary §2.3 (stated there for the closed
unit disc, `n = 1`): strict convexity of a compact boundary persists under small changes of the
metric, but not under large ones.
-/

public section

open Bundle Metric Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n + 1)]

/-- **The second fundamental form of the sphere for `g_s = e^{-2s|x|²} g`.** For `s : ℝ`, at every
point `q` of the unit sphere bounding the closed unit ball, `II^{g_s}_q = e^{-s} (1 - 2s) h_q`. -/
theorem boundarySecondFundamentalForm_closedBall_rescale_exp_neg_two_mul_norm_sq_smul (s : ℝ)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (-2 * s * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq (-2 * s)).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      boundarySecondFundamentalForm q u w) =
    Real.exp (-s) * (1 - 2 * s) * boundaryInducedForm q u w := by
  refine (boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq (-2 * s) q u w).trans ?_
  congr 2
  · congr 1
    ring
  · ring

/-- **The threshold metric `e^{-|x|²} g`.** For `s = 1/2`, that is `g_s = e^{-|x|²} g`, the second
fundamental form of the unit sphere vanishes. -/
theorem boundarySecondFundamentalForm_closedBall_rescale_exp_neg_norm_sq
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (-2 * (1 / 2) * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq (-2 * (1 / 2))).contMDiff.comp
            contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      boundarySecondFundamentalForm q u w) = 0 := by
  refine (boundarySecondFundamentalForm_closedBall_rescale_exp_neg_two_mul_norm_sq_smul
    (1 / 2) q u w).trans ?_
  norm_num

/-- **Strict convexity in the family `g_s = e^{-2s|x|²} g`.** For `n ≥ 1`, the unit sphere is
strictly convex at a point `q` for `g_s` exactly when `s < 1/2`. -/
theorem isStrictlyConvexAt_closedBall_rescale_exp_iff [NeZero n] (s : ℝ)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (-2 * s * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq (-2 * s)).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      IsStrictlyConvexAt q) ↔ s < 1 / 2 := by
  have h := boundarySecondFundamentalForm_closedBall_rescale_exp_neg_two_mul_norm_sq_smul s q
  simp only [isStrictlyConvexAt_iff, h]
  obtain ⟨u, hu⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  constructor
  · intro H
    have := H u hu
    have hpos := boundaryInducedForm_self_pos q hu
    have : 0 < 1 - 2 * s := by
      by_contra hle
      exact this.not_ge (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (not_lt.1 hle)) hpos.le)
    linarith
  · intro hs v hv
    exact mul_pos (mul_pos (Real.exp_pos _) (by linarith)) (boundaryInducedForm_self_pos q hv)

/-- **The threshold `s = 1/2`.** For `n ≥ 1`, the unit sphere is strictly convex for
`g_s = e^{-2s|x|²} g` exactly when `s < 1/2`. -/
theorem isStrictlyConvexBoundary_closedBall_rescale_exp_iff [NeZero n] (s : ℝ) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (-2 * s * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq (-2 * s)).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      IsStrictlyConvexBoundary n (closedBall (0 : E) 1)) ↔ s < 1 / 2 := by
  obtain ⟨q⟩ : Nonempty ((𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) := inferInstance
  simp only [isStrictlyConvexBoundary_iff]
  exact ⟨fun H ↦ (isStrictlyConvexAt_closedBall_rescale_exp_iff s q).1 (H q),
    fun hs q ↦ (isStrictlyConvexAt_closedBall_rescale_exp_iff s q).2 hs⟩

/-- **The strictly convex parameters form an open set.** For `n ≥ 1`, the set of `s : ℝ` for which
the unit sphere is strictly convex for `g_s = e^{-2s|x|²} g` is the open half-line `s < 1/2`. -/
theorem isOpen_setOf_isStrictlyConvexBoundary_closedBall_rescale_exp [NeZero n] :
    IsOpen {s : ℝ |
      letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (-2 * s * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq (-2 * s)).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      IsStrictlyConvexBoundary n (closedBall (0 : E) 1)} := by
  have : {s : ℝ | _} = Set.Iio (1 / 2) :=
    Set.ext fun s ↦ isStrictlyConvexBoundary_closedBall_rescale_exp_iff (n := n) (E := E) s
  exact this ▸ isOpen_Iio

/-- **Convexity in the family `g_s = e^{-2s|x|²} g`.** For `n ≥ 1`, the unit sphere is convex at a
point `q` for `g_s` exactly when `s ≤ 1/2`. -/
theorem isConvexAt_closedBall_rescale_exp_iff [NeZero n] (s : ℝ)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (-2 * s * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq (-2 * s)).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      IsConvexAt q) ↔ s ≤ 1 / 2 := by
  have h := boundarySecondFundamentalForm_closedBall_rescale_exp_neg_two_mul_norm_sq_smul s q
  simp only [isConvexAt_iff, h]
  obtain ⟨u, hu⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  constructor
  · intro H
    have := H u
    have hpos := boundaryInducedForm_self_pos q hu
    have : 0 ≤ 1 - 2 * s := by
      by_contra hlt
      exact this.not_gt (mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (Real.exp_pos _) (not_le.1 hlt)) hpos)
    linarith
  · intro hs v
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith))
      (boundaryInducedForm_self_nonneg q v)

/-- **Strict concavity in the family `g_s = e^{-2s|x|²} g`.** For `n ≥ 1`, the unit sphere is
strictly concave at a point `q` for `g_s` exactly when `1/2 < s`. -/
theorem isStrictlyConcaveAt_closedBall_rescale_exp_iff [NeZero n] (s : ℝ)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (-2 * s * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq (-2 * s)).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      IsStrictlyConcaveAt q) ↔ 1 / 2 < s := by
  have h := boundarySecondFundamentalForm_closedBall_rescale_exp_neg_two_mul_norm_sq_smul s q
  simp only [isStrictlyConcaveAt_iff, h]
  obtain ⟨u, hu⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  constructor
  · intro H
    have := H u hu
    have hpos := boundaryInducedForm_self_pos q hu
    have : 1 - 2 * s < 0 := by
      by_contra hle
      exact this.not_ge (mul_nonneg (mul_nonneg (Real.exp_pos _).le (not_lt.1 hle)) hpos.le)
    linarith
  · intro hs v hv
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith))
      (boundaryInducedForm_self_pos q hv)

end TauCeti
