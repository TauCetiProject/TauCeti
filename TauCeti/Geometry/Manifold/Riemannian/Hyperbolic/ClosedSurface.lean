/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.CurvatureEquation
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization

/-!
# Hyperbolic metrics in a conformal class of a closed surface

Let `g` be a smooth Riemannian metric on a closed connected surface `M`. A hyperbolic metric
conformal to `g` is a `TauCeti.HyperbolicMetric` whose metric is `f g` for a smooth positive
function `f`. This file identifies these hyperbolic metrics with the smooth solutions of the
curvature equation

`Δ⁺φ + K + e^(2φ) = 0`,

where `Δ⁺ = -div grad` is the nonnegative Laplacian of `g` and `K = Scal^g / 2` its Gaussian
curvature, the hyperbolic metric being `e^(2φ) g`. The two properties of a hyperbolic metric
beyond its curvature hold automatically on a closed surface: the Riemannian distance of a compact
manifold is complete (`TauCeti.HyperbolicMetric.ofCompactSpace`), and its Riemannian volume is
finite (`TauCeti.HyperbolicMetric.hasFiniteVolume_of_compactSpace`). So the existence of a
hyperbolic metric in the conformal class of `g` is equivalent to the solvability of the curvature
equation, and by the maximum principle there is at most one such metric.

## Main results

* `Bundle.ContMDiffRiemannianMetric.exists_hyperbolicMetric_metric_eq_rescale_iff`: a closed
  surface carries a hyperbolic metric conformal to `g` exactly when the curvature equation has a
  smooth solution.
* `TauCeti.HyperbolicMetric.eq_of_metric_eq_rescale`: two hyperbolic metrics conformal to `g`
  are equal.

## References

* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47.
* M. S. Berger, *Riemannian structures of prescribed Gaussian curvature for compact
  2-manifolds*, J. Differential Geom. 5 (1971), 325–332.
-/

public section

open Bundle Module TauCeti TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

namespace Bundle.ContMDiffRiemannianMetric

variable (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- **Hyperbolic metrics in a conformal class and the curvature equation.** A closed surface
carries a hyperbolic metric conformal to `g`, that is of the form `f g` for a smooth positive
function `f`, exactly when the curvature equation `Δ⁺φ + K + e^(2φ) = 0` has a smooth solution
`φ`; here `Δ⁺ = -div grad` is the nonnegative Laplacian of `g` and `K = Scal^g / 2` its Gaussian
curvature. The hyperbolic metric is then `e^(2φ) g`. -/
theorem exists_hyperbolicMetric_metric_eq_rescale_iff (hE : finrank ℝ E = 2) :
    (∃ (G : HyperbolicMetric (I := I) (M := M)) (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
        (hf_pos : ∀ x, 0 < f x), G.metric = g.rescale f hf hf_pos) ↔
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧
        ∀ x, -laplaceBeltrami I φ x + g.scalarCurvature x / 2 + Real.exp (2 * φ x) = 0 := by
  constructor
  · -- The exponent of the conformal factor `f = e^(2φ)` is `φ = log f / 2`.
    rintro ⟨G, f, hf, hf_pos, hG⟩
    have hfφ (x : M) : f x = Real.exp (2 * (Real.log (f x) / 2)) := by
      rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log (hf_pos x)]
    refine ⟨fun x ↦ Real.log (f x) / 2, (hf.log fun x ↦ (hf_pos x).ne').div_const 2, ?_⟩
    exact (g.isConstantCurvatureTensor_rescale_iff_of_finrank_eq_two hE hf hf_pos hfφ).1
      (hG ▸ G.curvature)
  · -- The metric `e^(2φ) g` has curvature `-1`, and completeness is automatic on a closed surface.
    rintro ⟨φ, hφ, h⟩
    have hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ Real.exp (2 * φ x) :=
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contMDiff.comp hφ
    have hf_pos (x : M) : 0 < Real.exp (2 * φ x) := Real.exp_pos _
    exact ⟨HyperbolicMetric.ofCompactSpace
      ((g.isConstantCurvatureTensor_rescale_iff_of_finrank_eq_two hE hf hf_pos
        fun _ ↦ rfl).2 h), _, hf, hf_pos, HyperbolicMetric.metric_ofCompactSpace _⟩

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.HyperbolicMetric

/-- **Uniqueness of the hyperbolic metric in a conformal class.** On a closed surface two
hyperbolic metrics conformal to the same metric `g` are equal. -/
theorem eq_of_metric_eq_rescale [I.Boundaryless] (hE : finrank ℝ E = 2)
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (G₁ G₂ : HyperbolicMetric (I := I) (M := M)) {f₁ f₂ : M → ℝ}
    {hf₁ : ContMDiff I 𝓘(ℝ) ∞ f₁} {hf₁_pos : ∀ x, 0 < f₁ x}
    {hf₂ : ContMDiff I 𝓘(ℝ) ∞ f₂} {hf₂_pos : ∀ x, 0 < f₂ x}
    (h₁ : G₁.metric = g.rescale f₁ hf₁ hf₁_pos) (h₂ : G₂.metric = g.rescale f₂ hf₂ hf₂_pos) :
    G₁ = G₂ := by
  -- Both conformal metrics have scalar curvature `-2`, so the maximum principle identifies the
  -- conformal factors.
  have hscal {G : HyperbolicMetric (I := I) (M := M)} {f : M → ℝ}
      {hf : ContMDiff I 𝓘(ℝ) ∞ f} {hf_pos : ∀ x, 0 < f x}
      (h : G.metric = g.rescale f hf hf_pos) (x : M) :
      (g.rescale f hf hf_pos).scalarCurvature x = -2 := by
    have hc : (g.rescale f hf hf_pos).IsConstantCurvatureTensor (-1) := h ▸ G.curvature
    rw [ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff_scalarCurvature_eq_of_finrank_eq_two
      _ hE] at hc
    linarith [hc x]
  obtain rfl := g.eq_of_scalarCurvature_rescale_eq hE hf₁ hf₁_pos hf₂ hf₂_pos (by norm_num)
    (hscal h₁) (hscal h₂)
  exact HyperbolicMetric.ext (h₁.trans h₂.symm)

end TauCeti.HyperbolicMetric
