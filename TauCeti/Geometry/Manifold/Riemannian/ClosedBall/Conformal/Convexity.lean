/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Convexity.Basic
public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.Conformal.Basic
import TauCeti.Geometry.Manifold.Instances.ClosedBall.Boundary

/-!
# Convexity of the unit sphere for the conformal metrics `e^{α|x|²} g`

Let `B` be the closed unit ball of a real inner product space `E` of dimension `n + 1`, with its
Euclidean metric `g` (`TauCeti.closedBallEuclideanMetric`), and for `α : ℝ` let
`ĝ = e^{α|x|²} g`. At every point of the unit sphere `∂B`, `II^ĝ = e^{α/2} (1 + α) h`
(`TauCeti.boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq`), where `h` is the
induced metric of `g`, so `∂B` is umbilic and the sign of `1 + α` decides its convexity. For
`n ≥ 1`:

* `∂B` is strictly convex for `ĝ` exactly when `-1 < α`
  (`TauCeti.isStrictlyConvexAt_closedBall_rescale_exp_mul_norm_sq_iff`,
  `TauCeti.isStrictlyConvexBoundary_closedBall_rescale_exp_mul_norm_sq_iff`), an open set of
  parameters (`TauCeti.isOpen_setOf_isStrictlyConvexBoundary_closedBall_rescale_exp_mul_norm_sq`);
* `∂B` is convex for `ĝ` at a point exactly when `-1 ≤ α`
  (`TauCeti.isConvexAt_closedBall_rescale_exp_mul_norm_sq_iff`), and strictly concave exactly when
  `α < -1` (`TauCeti.isStrictlyConcaveAt_closedBall_rescale_exp_mul_norm_sq_iff`); at the
  threshold `α = -1` the second fundamental form vanishes
  (`TauCeti.boundarySecondFundamentalForm_closedBall_rescale_exp_neg_one_mul_norm_sq_eq_zero`).

In the parametrization `g_s = e^{-2s|x|²} g`, that is `α = -2s`, the family `g_s` has
`II^{g_s} = e^{-s} (1 - 2s) h`, and `∂B` is strictly convex for `g_s` exactly for the open set of
parameters `s < 1/2`
(`TauCeti.isStrictlyConvexBoundary_closedBall_rescale_exp_neg_two_mul_mul_norm_sq_iff`); by the
statements for `α`, it is strictly concave for `s > 1/2`.
-/

public section

open Bundle Metric Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n + 1)]

/-- **Strict convexity for `e^{α|x|²} g`.** For `n ≥ 1`, the unit sphere is strictly convex at a
point `q` for `ĝ = e^{α|x|²} g` exactly when `-1 < α`. -/
theorem isStrictlyConvexAt_closedBall_rescale_exp_mul_norm_sq_iff [NeZero n] (α : ℝ)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (α * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq α).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      IsStrictlyConvexAt q) ↔ -1 < α := by
  -- `rw` would synthesize the Euclidean instance for the lemma instead of the rescaled one in
  -- the goal; `simp only` takes it from the goal.
  simp only [isStrictlyConvexAt_iff_of_eq_mul (fun _ ↦ boundaryInducedForm_self_pos _)
    fun u ↦ boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq α _ u u,
    mul_pos_iff_of_pos_left (Real.exp_pos _)]
  constructor <;> intro h <;> linarith

/-- **Convexity for `e^{α|x|²} g`.** For `n ≥ 1`, the unit sphere is convex at a point `q` for
`ĝ = e^{α|x|²} g` exactly when `-1 ≤ α`. -/
theorem isConvexAt_closedBall_rescale_exp_mul_norm_sq_iff [NeZero n] (α : ℝ)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (α * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq α).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      IsConvexAt q) ↔ -1 ≤ α := by
  simp only [isConvexAt_iff_of_eq_mul (fun _ ↦ boundaryInducedForm_self_pos _)
    fun u ↦ boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq α _ u u,
    mul_nonneg_iff_of_pos_left (Real.exp_pos _)]
  constructor <;> intro h <;> linarith

/-- **Strict concavity for `e^{α|x|²} g`.** For `n ≥ 1`, the unit sphere is strictly concave at a
point `q` for `ĝ = e^{α|x|²} g` exactly when `α < -1`. -/
theorem isStrictlyConcaveAt_closedBall_rescale_exp_mul_norm_sq_iff [NeZero n] (α : ℝ)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (α * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq α).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      IsStrictlyConcaveAt q) ↔ α < -1 := by
  simp only [isStrictlyConcaveAt_iff_of_eq_mul (fun _ ↦ boundaryInducedForm_self_pos _)
    fun u ↦ boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq α _ u u,
    ← neg_pos, ← mul_neg, mul_pos_iff_of_pos_left (Real.exp_pos _)]
  constructor <;> intro h <;> linarith

/-- **The threshold `α = -1`.** For `n ≥ 1`, the unit sphere is strictly convex for
`ĝ = e^{α|x|²} g` exactly when `-1 < α`. -/
theorem isStrictlyConvexBoundary_closedBall_rescale_exp_mul_norm_sq_iff [NeZero n] (α : ℝ) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (α * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq α).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      IsStrictlyConvexBoundary n (closedBall (0 : E) 1)) ↔ -1 < α := by
  obtain ⟨q⟩ : Nonempty ((𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) := inferInstance
  simp only [isStrictlyConvexBoundary_iff]
  exact ⟨fun H ↦ (isStrictlyConvexAt_closedBall_rescale_exp_mul_norm_sq_iff α q).1 (H q),
    fun hα q ↦ (isStrictlyConvexAt_closedBall_rescale_exp_mul_norm_sq_iff α q).2 hα⟩

/-- **The strictly convex parameters form an open set.** For `n ≥ 1`, the set of `α : ℝ` for which
the unit sphere is strictly convex for `ĝ = e^{α|x|²} g` is the open half-line `-1 < α`. -/
theorem isOpen_setOf_isStrictlyConvexBoundary_closedBall_rescale_exp_mul_norm_sq [NeZero n] :
    IsOpen {α : ℝ |
      letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (α * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq α).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      IsStrictlyConvexBoundary n (closedBall (0 : E) 1)} := by
  have : {α : ℝ | _} = Set.Ioi (-1) :=
    Set.ext fun α ↦
      isStrictlyConvexBoundary_closedBall_rescale_exp_mul_norm_sq_iff (n := n) (E := E) α
  exact this ▸ isOpen_Ioi

/-- **The threshold `s = 1/2` for `g_s = e^{-2s|x|²} g`.** For `n ≥ 1`, the unit sphere is strictly
convex for `g_s` exactly when `s < 1/2`; this is the case `α = -2s` of
`isStrictlyConvexBoundary_closedBall_rescale_exp_mul_norm_sq_iff`. -/
theorem isStrictlyConvexBoundary_closedBall_rescale_exp_neg_two_mul_mul_norm_sq_iff [NeZero n]
    (s : ℝ) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (-2 * s * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq (-2 * s)).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      IsStrictlyConvexBoundary n (closedBall (0 : E) 1)) ↔ s < 1 / 2 := by
  rw [isStrictlyConvexBoundary_closedBall_rescale_exp_mul_norm_sq_iff]
  constructor <;> intro h <;> linarith

end TauCeti
