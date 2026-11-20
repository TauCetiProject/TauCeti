/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Lengths and distances under constant rescaling of a metric

Let `g` be a Riemannian metric on a vector bundle and `c` a positive constant, and let `c g` be the
rescaled metric `Bundle.ContMDiffRiemannianMetric.rescale` by the constant function `c`. Its norms
are `√c` times those of `g` (`Bundle.ContMDiffRiemannianMetric.norm_rescale_const`). On the tangent
bundle of a manifold, the length of a path is the integral of the norm of its velocity, so every
length, and the Riemannian distance, which is the infimum of the lengths of the `C¹` paths between
two points, is multiplied by `√c` as well:

`L_{c g}(γ) = √c L_g(γ)` and `d_{c g}(x, y) = √c d_g(x, y)`.

Both metrics are installed in turn as the `RiemannianBundle` instance of the bundle, as in
`TauCeti.Geometry.Manifold.Riemannian.Scaling`, which compares the gradients, the curvature and the
Laplacian of `g` and `c g`. Together with the gradient law
`Bundle.ContMDiffRiemannianMetric.mgradient_rescale_const`, these laws say how the rate of
convergence of a gradient flow, measured in the distance of the metric, changes when the metric is
rescaled.

## Main results

* `Bundle.ContMDiffRiemannianMetric.norm_rescale_const` and
  `Bundle.ContMDiffRiemannianMetric.eNorm_rescale_const`: the norm for `c g` is `√c` times the norm
  for `g`.
* `Bundle.ContMDiffRiemannianMetric.pathELength_rescale_const`: the length of a path for `c g` is
  `√c` times its length for `g`.
* `Bundle.ContMDiffRiemannianMetric.riemannianEDist_rescale_const`: the Riemannian extended
  distance for `c g` is `√c` times the distance for `g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (lengths of curves and the Riemannian distance).
-/

public section

open Bundle Manifold
open scoped ContDiff ENNReal Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

section Norm

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, TopologicalSpace (V b)] [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousConstSMul ℝ (V b)] [FiberBundle F V]
  [VectorBundle ℝ F V]

/-- Multiplying a metric by a positive constant `c` multiplies the norm of every vector by
`√c`. -/
theorem norm_rescale_const (g : ContMDiffRiemannianMetric IB n F V) {c : ℝ} (hc : 0 < c) {b : B}
    (v : V b) :
    (letI : RiemannianBundle V :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ‖v‖) =
    √c * (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩; ‖v‖) := by
  have hg : (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩; ‖v‖) = √(g.inner b v v) := by
    let _ : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    rw [norm_eq_sqrt_real_inner, inner_riemannianBundle]
  let _ : RiemannianBundle V :=
    ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
  rw [hg, norm_eq_sqrt_real_inner, inner_riemannianBundle, rescale_inner,
    Real.sqrt_mul hc.le]

/-- Multiplying a metric by a positive constant `c` multiplies the extended norm of every vector
by `√c`. -/
theorem eNorm_rescale_const (g : ContMDiffRiemannianMetric IB n F V) {c : ℝ} (hc : 0 < c) {b : B}
    (v : V b) :
    (letI : RiemannianBundle V :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ‖v‖ₑ) =
    ENNReal.ofReal √c * (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩; ‖v‖ₑ) := by
  have h₁ : (letI : RiemannianBundle V :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩; ‖v‖ₑ) =
      ENNReal.ofReal (letI : RiemannianBundle V :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩; ‖v‖) := by
    let _ : RiemannianBundle V :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    exact (ofReal_norm v).symm
  have h₂ : (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩; ‖v‖ₑ) =
      ENNReal.ofReal (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩; ‖v‖) := by
    let _ : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    exact (ofReal_norm v).symm
  rw [h₁, h₂, ← ENNReal.ofReal_mul (Real.sqrt_nonneg c), g.norm_rescale_const hc v]

end Norm

section Distance

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- **Lengths under constant rescaling.** Multiplying a metric by a positive constant `c`
multiplies the length of every path by `√c`. -/
theorem pathELength_rescale_const
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) {c : ℝ} (hc : 0 < c)
    (γ : ℝ → M) (a b : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      pathELength I γ a b) =
    ENNReal.ofReal √c * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩; pathELength I γ a b) := by
  simp only [pathELength_eq_lintegral_mfderiv_Icc, eNorm_rescale_const g hc]
  exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Distances under constant rescaling.** Multiplying a metric by a positive constant `c`
multiplies the Riemannian extended distance between any two points by `√c`. -/
theorem riemannianEDist_rescale_const
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) {c : ℝ} (hc : 0 < c)
    (x y : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      riemannianEDist I x y) =
    ENNReal.ofReal √c * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩; riemannianEDist I x y) := by
  have hc₀ : ENNReal.ofReal √c ≠ 0 := by simpa using hc
  simp only [riemannianEDist_def, eNorm_rescale_const g hc,
    ENNReal.mul_iInf_of_ne hc₀ ENNReal.ofReal_ne_top]
  refine iInf_congr fun γ ↦ iInf_congr fun _ ↦ ?_
  exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Distance

end Bundle.ContMDiffRiemannianMetric
