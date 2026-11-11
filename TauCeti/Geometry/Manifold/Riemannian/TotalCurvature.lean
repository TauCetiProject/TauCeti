/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Conformal.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.WithMetric

/-!
# Total curvature of a closed surface under conformal change

Let `g` be a smooth Riemannian metric on a closed surface `M` and `ĝ = f g` a conformal metric,
with `f = e^(2φ)`. In dimension two the volume of `ĝ` has density `f` against that of `g`, and the
conformal change of scalar curvature reads `f Scal^ĝ = Scal^g - 2 Δφ`, with `Δ = div grad` the
Laplace–Beltrami operator of `g`. Since `∫ Δφ dV_g = 0` on a closed manifold, the total curvature
is a conformal invariant:

`∫ Scal^ĝ dV_ĝ = ∫ Scal^g dV_g`.

When `ĝ` has constant scalar curvature `c`, the left side is `c Vol(ĝ)`, which gives the area
normalization `c Vol(ĝ) = ∫ Scal^g dV_g`. For a metric of Gaussian curvature `-1`, that is `c = -2`,
this says that its area is `-∫ K dV_g` with `K = Scal^g / 2`, and that a closed surface whose
conformal class contains a metric of constant negative curvature has negative total curvature.

As in `TauCeti.WithMetric.integral_riemannianVolume_rescale`, the volumes of `g` and `ĝ` are those
of the metric-indexed copies `TauCeti.WithMetric g` and `TauCeti.WithMetric ĝ` of `M`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.integral_scalarCurvature_rescale_of_finrank_eq_two`: the
  total curvature of a closed surface is invariant under conformal change.
* `Bundle.ContMDiffRiemannianMetric.mul_riemannianTotalVolume_rescale_of_finrank_eq_two`: a
  conformal metric of constant scalar curvature `c` has area `Vol(ĝ)` with
  `c Vol(ĝ) = ∫ Scal^g dV_g`.
* `Bundle.ContMDiffRiemannianMetric.integral_scalarCurvature_neg_of_scalarCurvature_rescale_eq`:
  a nonempty closed surface conformal to a metric of constant negative curvature has negative
  total curvature.

## References

* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47.
* M. S. Berger, *Riemannian structures of prescribed Gaussian curvature for compact
  2-manifolds*, J. Differential Geom. 5 (1971), 325–332.
-/

public section

open Bundle MeasureTheory Module TauCeti TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- **Total curvature is a conformal invariant of a closed surface.** For a smooth positive
function `f` on a closed surface, `∫ Scal^(f g) dV_(f g) = ∫ Scal^g dV_g`. -/
theorem integral_scalarCurvature_rescale_of_finrank_eq_two (hE : finrank ℝ E = 2)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) :
    ∫ x, (g.rescale f hf hf_pos).scalarCurvature x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g.rescale f hf hf_pos)) =
      ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) := by
  borelize M
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  -- Write `f = e^(2φ)` with `φ = log f / 2`.
  set φ : M → ℝ := fun y ↦ Real.log (f y) / 2
  have hφ : ContMDiff I 𝓘(ℝ) 2 φ :=
    ((hf.of_le (by simp)).log fun y ↦ (hf_pos y).ne').div_const 2
  have hfφ (y : M) : f y = Real.exp (2 * φ y) := by
    rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log (hf_pos y)]
  -- In dimension two the volume density of `f g` is `f`, and `f Scal^(f g) = Scal^g - 2 Δφ`.
  have hpt (y : M) : f y ^ ((finrank ℝ E : ℝ) / 2) • (g.rescale f hf hf_pos).scalarCurvature y =
      g.scalarCurvature y - 2 * laplaceBeltrami I φ y := by
    rw [hE, Nat.cast_ofNat, div_self two_ne_zero, Real.rpow_one, smul_eq_mul,
      scalarCurvature_rescale_of_finrank_eq_two g hE hf hf_pos hfφ y,
      mul_inv_cancel_left₀ (hf_pos y).ne']
  rw [WithMetric.integral_riemannianVolume_rescale (g.rescale f hf hf_pos).scalarCurvature]
  simp only [hpt]
  rw [WithMetric.integral_comp_ofWithMetric g fun y ↦
      g.scalarCurvature y - 2 * laplaceBeltrami I φ y,
    WithMetric.integral_comp_ofWithMetric g g.scalarCurvature]
  -- The Laplacian term integrates to zero on the closed surface.
  have hK : Integrable g.scalarCurvature (riemannianVolume I M) :=
    g.continuous_scalarCurvature.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hΔ : Integrable (laplaceBeltrami I φ) (riemannianVolume I M) :=
    (contMDiff_laplaceBeltrami (n := 0) (m := 2) (k := 1) (by norm_num) (by norm_num)
      (by simpa using hφ)).continuous.integrable_of_hasCompactSupport (.of_compactSpace _)
  rw [integral_sub hK (hΔ.const_mul 2), integral_const_mul,
    integral_laplaceBeltrami_eq_zero hφ (.of_compactSpace _), mul_zero, sub_zero]

/-- **Area normalization.** On a closed surface, a conformal metric `f g` of constant scalar
curvature `c` satisfies `c Vol(f g) = ∫ Scal^g dV_g`. For a metric of Gaussian curvature `-1`,
`c = -2`, its area is `-∫ K dV_g` with `K = Scal^g / 2`. -/
theorem mul_riemannianTotalVolume_rescale_of_finrank_eq_two (hE : finrank ℝ E = 2)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {c : ℝ}
    (h : ∀ x, (g.rescale f hf hf_pos).scalarCurvature x = c) :
    c * riemannianTotalVolume I (WithMetric (g.rescale f hf hf_pos)) =
      ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) := by
  rw [← g.integral_scalarCurvature_rescale_of_finrank_eq_two hE hf hf_pos]
  simp only [h, integral_const, smul_eq_mul, riemannianTotalVolume_def, mul_comm]

/-- **Sign of the total curvature.** If a metric `g` on a nonempty closed surface is conformal to
a metric of constant negative scalar curvature, then the total curvature of `g` is negative. -/
theorem integral_scalarCurvature_neg_of_scalarCurvature_rescale_eq [Nonempty M]
    (hE : finrank ℝ E = 2) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x)
    {c : ℝ} (hc : c < 0) (h : ∀ x, (g.rescale f hf hf_pos).scalarCurvature x = c) :
    ∫ x, g.scalarCurvature x.ofWithMetric ∂riemannianVolume I (WithMetric g) < 0 := by
  have := (WithMetric.equiv (g.rescale f hf hf_pos)).nonempty
  rw [← g.mul_riemannianTotalVolume_rescale_of_finrank_eq_two hE hf hf_pos h]
  exact mul_neg_of_neg_of_pos hc riemannianTotalVolume_pos

end Bundle.ContMDiffRiemannianMetric
