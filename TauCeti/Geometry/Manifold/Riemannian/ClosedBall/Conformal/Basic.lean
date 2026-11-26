/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SquaredDistance
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Conformal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.OutwardUnitNormal
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Conformal.Weingarten
public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.SecondFundamentalForm
public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.Weingarten

/-!
# Conformal changes of the Euclidean metric on the closed unit ball

Let `B` be the closed unit ball of a real inner product space `E` of dimension `n + 1`, with its
Euclidean metric `g` (`TauCeti.closedBallEuclideanMetric`), whose boundary sphere has `II = h`.
For an analytic function `Φ : E → ℝ` positive on `B`, the conformal law of the second
fundamental form (`Bundle.ContMDiffRiemannianMetric.boundarySecondFundamentalForm_rescale`) for
`ĝ = Φ g` reads, at `q ∈ ∂B`, where the inward unit normal is `-q`,

    II^ĝ_q = √(Φ q) (1 + (2 Φ q)⁻¹ DΦ(q) q) h_q

(`TauCeti.boundarySecondFundamentalForm_closedBall_rescale`). In particular, with
`ĝ = e^{2φ} g`:

* `φ = log c` for a constant `c > 0`, that is `ĝ = c² g`: `II^ĝ = c h`, so for instance
  `ĝ = 4 g` gives `II^ĝ = 2h` (`TauCeti.boundarySecondFundamentalForm_closedBall_rescale_const`);
* `ĝ = e^{α|x|²} g` for `α : ℝ`: `II^ĝ = e^{α/2} (1 + α) h`
  (`TauCeti.boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq`). For `α = -2`,
  that is `φ = -|x|²`, `dφ(ν_in) = 2` on the sphere and `II^ĝ = e^{-1} (1 - 2) h = -e^{-1} h`
  (`TauCeti.boundarySecondFundamentalForm_closedBall_rescale_exp_neg_two_mul_norm_sq`). The wrong
  sign `e^{φ} (II + dφ(ν_in) h)` would give `3 e^{-1} h`. For `α = -1` the sphere is totally
  geodesic, `II^ĝ = 0`
  (`TauCeti.boundarySecondFundamentalForm_closedBall_rescale_exp_neg_one_mul_norm_sq_eq_zero`);
* `ĝ = e^{α(|x|² - 1)²} g` for `α : ℝ`, which for `α = 2` is `φ = (|x|² - 1)²`: `φ = 0` and
  `dφ = 0` on the sphere, so `II^ĝ = II = h`
  (`TauCeti.boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq_sub_one_sq`).

For `n ≥ 1` the mean curvature of the sphere, `1` for `g`, becomes
`H^ĝ_q = (√(Φ q))⁻¹ (1 + (2 Φ q)⁻¹ DΦ(q) q)` (`TauCeti.boundaryMeanCurvature_closedBall_rescale`),
so `H^ĝ = e^{-α/2} (1 + α)` for `ĝ = e^{α|x|²} g`
(`TauCeti.boundaryMeanCurvature_closedBall_rescale_exp_mul_norm_sq`). For the closed unit disc
with `φ = -|x|²` this is `H^ĝ = e (1 - 2) = -e`
(`TauCeti.boundaryMeanCurvature_closedBall_rescale_exp_neg_two_mul_norm_sq`).
-/

public section

open Bundle Metric Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n + 1)]

/-- A boundary point of the closed unit ball lies on the unit sphere. -/
private theorem norm_boundary_closedBall (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    ‖((q : closedBall (0 : E) 1) : E)‖ = 1 :=
  (isBoundaryPoint_closedBall_iff (n := n + 1)).mp q.property

/-- For a differentiable `Φ : E → ℝ`, the derivative of `Φ` along the inward unit normal `-q` of
the sphere at `q ∈ ∂B` is `-DΦ(q) q`. -/
private theorem mvfderiv_comp_subtypeVal_inwardUnitNormal_closedBall {Φ : E → ℝ}
    (hΦ : Differentiable ℝ Φ) (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    mvfderiv (𝓡∂ (n + 1)) (Φ ∘ Subtype.val) (q : closedBall (0 : E) 1) (inwardUnitNormal q) =
      -fderiv ℝ Φ q q := by
  rw [mvfderiv_comp_apply_of_differentiableAt (hΦ _)
      ((contMDiff_subtypeVal_closedBall (k := 1)).mdifferentiableAt one_ne_zero),
    inwardUnitNormal_def, map_neg, mvfderiv_outwardUnitNormal_closedBall, map_neg]

/-- **The second fundamental form of the sphere under a conformal change of the Euclidean metric
of the ball.** For an analytic `Φ : E → ℝ` positive on the ball and `ĝ = Φ g`, at `q ∈ ∂B`,
`II^ĝ_q(u, w) = √(Φ q) (1 + (2 Φ q)⁻¹ DΦ(q) q) h_q(u, w)`, where `h_q(u, w) = ⟨dι u, dι w⟩` is
the induced metric of `g`. -/
theorem boundarySecondFundamentalForm_closedBall_rescale {Φ : E → ℝ} (hΦ : ContDiff ℝ ω Φ)
    (hΦ_pos : ∀ x ∈ closedBall (0 : E) 1, 0 < Φ x)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale (Φ ∘ Subtype.val)
          (hΦ.contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun x ↦ hΦ_pos x x.property).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      boundarySecondFundamentalForm q u w) =
    √(Φ q) * (1 + (2 * Φ q)⁻¹ * fderiv ℝ Φ q q) * boundaryInducedForm q u w := by
  set x : closedBall (0 : E) 1 := (q : closedBall (0 : E) 1)
  set ι := (Subtype.val : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) → closedBall (0 : E) 1)
  have hd := mvfderiv_comp_subtypeVal_inwardUnitNormal_closedBall (hΦ.differentiable (by simp)) q
  refine (Bundle.ContMDiffRiemannianMetric.boundarySecondFundamentalForm_rescale
    closedBallEuclideanMetric _ _ le_top q u w).trans ?_
  -- The `letI` around the unscaled metric is definitionally the instance of the closed ball,
  -- `closedBallEuclideanMetric.inner` is definitionally its inner product and
  -- `(Φ ∘ Subtype.val) x` is `Φ x`; `rw` cannot see through the `letI`-bound instances, so the
  -- right side of the conformal law is restated in terms of the global instances.
  change √(Φ x) * (boundarySecondFundamentalForm q u w -
    (2 * Φ x)⁻¹ * mvfderiv (𝓡∂ (n + 1)) (Φ ∘ Subtype.val) x (inwardUnitNormal q) *
      ⟪mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) ι q u,
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) ι q w⟫) = _
  rw [boundarySecondFundamentalForm_closedBall, hd, boundaryInducedForm_apply]
  ring

/-- **Constant rescaling.** For a constant `c > 0` and `ĝ = c² g = e^{2 log c} g` on the closed
unit ball, `II^ĝ = c h`; for instance `ĝ = 4 g` gives `II^ĝ = 2 h`. -/
theorem boundarySecondFundamentalForm_closedBall_rescale_const {c : ℝ} (hc : 0 < c)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale (fun _ ↦ c ^ 2) contMDiff_const
          fun _ ↦ pow_pos hc 2).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      boundarySecondFundamentalForm q u w) =
    c * boundaryInducedForm q u w := by
  refine (Bundle.ContMDiffRiemannianMetric.boundarySecondFundamentalForm_rescale_const
    closedBallEuclideanMetric le_top hc q u w).trans ?_
  -- The `letI` around the unscaled metric is definitionally the instance of the closed ball;
  -- restate the goal with the global instance so that `rw` can reach it.
  change c * boundarySecondFundamentalForm q u w = _
  rw [boundarySecondFundamentalForm_closedBall, boundaryInducedForm_apply]

/-- On the unit sphere, `x ↦ e^{α|x|²}` has derivative `2 α e^α` in the radial direction. -/
private theorem fderiv_exp_mul_norm_sq_apply_self (α : ℝ) {x : E} (hx : ‖x‖ = 1) :
    fderiv ℝ (fun y : E ↦ Real.exp (α * ‖y‖ ^ 2)) x x = 2 * α * Real.exp α := by
  rw [(by simpa using hasFDerivAt_exp_neg_mul_norm_sub_sq (-α) (0 : E) x :
    HasFDerivAt _ ((2 * α * Real.exp (α * ‖x‖ ^ 2)) • innerSL ℝ x) x).fderiv]
  simp [hx]

/-- **The conformal factor `e^{α|x|²}`.** For `α : ℝ` and `ĝ = e^{α|x|²} g` on the closed unit
ball, `II^ĝ = e^{α/2} (1 + α) h`. -/
theorem boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq (α : ℝ)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (α * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq α).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      boundarySecondFundamentalForm q u w) =
    Real.exp (α / 2) * (1 + α) * boundaryInducedForm q u w := by
  have hq := norm_boundary_closedBall q
  refine (boundarySecondFundamentalForm_closedBall_rescale
    (contDiff_exp_mul_norm_sq α) (fun _ _ ↦ Real.exp_pos _) q u w).trans ?_
  rw [fderiv_exp_mul_norm_sq_apply_self α hq, hq, one_pow, mul_one, ← Real.exp_half]
  field_simp

/-- **The conformal factor `e^{-2|x|²}`.** For `ĝ = e^{-2|x|²} g` on the closed unit ball,
`dφ(ν_in) = 2` on the sphere and `II^ĝ = e^{-1} (1 - 2) h = -e^{-1} h`; this is the case
`α = -2` of `boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq`. -/
theorem boundarySecondFundamentalForm_closedBall_rescale_exp_neg_two_mul_norm_sq
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (-2 * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq (-2)).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      boundarySecondFundamentalForm q u w) =
    -Real.exp (-1) * boundaryInducedForm q u w := by
  refine (boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq (-2) q u w).trans ?_
  norm_num

/-- **The conformal factor `e^{-|x|²}`.** For `ĝ = e^{-|x|²} g` on the closed unit ball,
`II^ĝ = e^{-1/2} (1 - 1) h = 0`: the unit sphere is totally geodesic. This is the case `α = -1` of
`boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq`. -/
theorem boundarySecondFundamentalForm_closedBall_rescale_exp_neg_one_mul_norm_sq_eq_zero
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (-1 * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq (-1)).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      boundarySecondFundamentalForm q u w) = 0 := by
  refine (boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq (-1) q u w).trans ?_
  norm_num

/-- On the unit sphere, `x ↦ e^{α(|x|² - 1)²}` has derivative `0` in the radial direction. -/
private theorem fderiv_exp_mul_norm_sq_sub_one_sq_apply_self (α : ℝ) {x : E} (hx : ‖x‖ = 1) :
    fderiv ℝ (fun y : E ↦ Real.exp (α * (‖y‖ ^ 2 - 1) ^ 2)) x x = 0 := by
  rw [(hasFDerivAt_exp_mul_norm_sq_sub_sq α 1 x).fderiv]
  simp [hx]

/-- **The conformal factor `e^{α(|x|² - 1)²}`.** For `α : ℝ` and `ĝ = e^{α(|x|² - 1)²} g` on the
closed unit ball, `φ` and `dφ` vanish on the sphere, so `II^ĝ = II = h`. The case `α = 2` is
`ĝ = e^{2φ} g` with `φ = (|x|² - 1)²`. -/
theorem boundarySecondFundamentalForm_closedBall_rescale_exp_mul_norm_sq_sub_one_sq (α : ℝ)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (α * (‖y‖ ^ 2 - 1) ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq_sub_sq α 1).contMDiff.comp
            contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      boundarySecondFundamentalForm q u w) =
    boundaryInducedForm q u w := by
  have hq := norm_boundary_closedBall q
  refine (boundarySecondFundamentalForm_closedBall_rescale
    (contDiff_exp_mul_norm_sq_sub_sq α 1) (fun _ _ ↦ Real.exp_pos _) q u w).trans ?_
  simp [fderiv_exp_mul_norm_sq_sub_one_sq_apply_self α hq, hq]

/-- **The mean curvature of the sphere under a conformal change of the Euclidean metric of the
ball.** For `n ≥ 1`, an analytic `Φ : E → ℝ` positive on the ball and `ĝ = Φ g`, at `q ∈ ∂B`,
`H^ĝ_q = (√(Φ q))⁻¹ (1 + (2 Φ q)⁻¹ DΦ(q) q)`. -/
theorem boundaryMeanCurvature_closedBall_rescale [NeZero n] {Φ : E → ℝ} (hΦ : ContDiff ℝ ω Φ)
    (hΦ_pos : ∀ x ∈ closedBall (0 : E) 1, 0 < Φ x)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale (Φ ∘ Subtype.val)
          (hΦ.contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun x ↦ hΦ_pos x x.property).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      boundaryMeanCurvature q) =
    (√(Φ q))⁻¹ * (1 + (2 * Φ q)⁻¹ * fderiv ℝ Φ q q) := by
  set x : closedBall (0 : E) 1 := (q : closedBall (0 : E) 1)
  have hd := mvfderiv_comp_subtypeVal_inwardUnitNormal_closedBall (hΦ.differentiable (by simp)) q
  refine (Bundle.ContMDiffRiemannianMetric.boundaryMeanCurvature_rescale
    closedBallEuclideanMetric _ _ le_top (NeZero.ne n) q).trans ?_
  -- As in `boundarySecondFundamentalForm_closedBall_rescale`, the `letI` around the unscaled
  -- metric is definitionally the instance of the closed ball; restate the right side with the
  -- global instances so that `rw` can reach it.
  change (√(Φ x))⁻¹ * (boundaryMeanCurvature q -
    (2 * Φ x)⁻¹ * mvfderiv (𝓡∂ (n + 1)) (Φ ∘ Subtype.val) x (inwardUnitNormal q)) = _
  rw [boundaryMeanCurvature_closedBall, hd]
  ring

/-- **Mean curvature for the conformal factor `e^{α|x|²}`.** For `n ≥ 1`, `α : ℝ` and
`ĝ = e^{α|x|²} g` on the closed unit ball, `H^ĝ = e^{-α/2} (1 + α)`. -/
theorem boundaryMeanCurvature_closedBall_rescale_exp_mul_norm_sq [NeZero n] (α : ℝ)
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (α * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq α).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      boundaryMeanCurvature q) =
    Real.exp (-(α / 2)) * (1 + α) := by
  have hq := norm_boundary_closedBall q
  refine (boundaryMeanCurvature_closedBall_rescale
    (contDiff_exp_mul_norm_sq α) (fun _ _ ↦ Real.exp_pos _) q).trans ?_
  rw [fderiv_exp_mul_norm_sq_apply_self α hq, hq, one_pow, mul_one, ← Real.exp_half,
    Real.exp_neg]
  field_simp

/-- **The mean curvature of the conformal disc.** For `n ≥ 1` and `ĝ = e^{-2|x|²} g` on the
closed unit ball, that is `φ = -|x|²`, `H^ĝ = e (1 - 2) = -e`; in particular this holds for the
closed unit disc (`n = 1`). -/
theorem boundaryMeanCurvature_closedBall_rescale_exp_neg_two_mul_norm_sq [NeZero n]
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    (letI : RiemannianBundle (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        ⟨(closedBallEuclideanMetric.rescale
          ((fun y : E ↦ Real.exp (-2 * ‖y‖ ^ 2)) ∘ Subtype.val)
          ((contDiff_exp_mul_norm_sq (-2)).contMDiff.comp contMDiff_subtypeVal_closedBall)
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
        IsContMDiffRiemannianBundle.of_le (n := ω) le_top;
      boundaryMeanCurvature q) =
    -Real.exp 1 := by
  refine (boundaryMeanCurvature_closedBall_rescale_exp_mul_norm_sq (-2) q).trans ?_
  norm_num

end TauCeti
