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

Let `g` be a Riemannian metric on a vector bundle and `c > 0` a constant. For the rescaled metric
`c g` (`Bundle.ContMDiffRiemannianMetric.rescale` by the constant function `c`) the norm of every
vector is `√c` times its norm for `g`. On the tangent bundle of a manifold, the length of every
path, and hence the Riemannian distance, the infimum of the lengths of the `C¹` paths between two
points, are multiplied by `√c`.

With `c = λ²`, intrinsic lengths and distances are multiplied by `λ`. Together with the scaling
`|A|² ↦ λ⁻² |A|²` of the second fundamental form
(`TauCeti.Manifold.IsIsometricImmersion.secondFundamentalFormNormSq_rescale_const`), this gives the
invariance of the hypothesis `r sup_(B_r(p)) |A| ≤ c₀` under `(g, r) ↦ (λ² g, λ r)`.

## Main statements

* `Bundle.ContMDiffRiemannianMetric.norm_rescale_const`: `‖v‖_(c g) = √c ‖v‖_g`.
* `Bundle.ContMDiffRiemannianMetric.enorm_rescale_const`: the same for extended norms.
* `Bundle.ContMDiffRiemannianMetric.pathELength_rescale_const`: the length of a path is multiplied
  by `√c`.
* `Bundle.ContMDiffRiemannianMetric.riemannianEDist_rescale_const`: the Riemannian distance is
  multiplied by `√c`.
* `Bundle.ContMDiffRiemannianMetric.riemannianEDist_rescale_const_lt_iff`,
  `Bundle.ContMDiffRiemannianMetric.riemannianEDist_rescale_const_le_iff`: the open and closed
  intrinsic balls of radius `√c r` for `c g` are those of radius `r` for `g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2.
-/

public noncomputable section

open Bundle Manifold MeasureTheory
open scoped ENNReal ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

section Norm

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, TopologicalSpace (V b)] [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousConstSMul ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (g : ContMDiffRiemannianMetric IB n F V) {c : ℝ} (hc : 0 < c)

/-- Multiplying a metric by a positive constant `c` multiplies the norm of every vector by
`√c`. -/
theorem norm_rescale_const (b : B) (v : V b) :
    (letI : RiemannianBundle V :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩; ‖v‖) =
      √c * (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩; ‖v‖) := by
  have k₁ := (letI : RiemannianBundle V :=
    ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
    real_inner_self_eq_norm_sq v)
  have k₂ := (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩; real_inner_self_eq_norm_sq v)
  have n₁ := (letI : RiemannianBundle V :=
    ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩; norm_nonneg v)
  have n₂ := (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩; norm_nonneg v)
  have hsq : (letI : RiemannianBundle V :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩; ‖v‖) ^ 2 =
      c * (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩; ‖v‖) ^ 2 :=
    calc _ = _ := k₁.symm
      _ = c * g.inner b v v :=
        (inner_riemannianBundle _ b v v).trans (rescale_inner _ _ _ _ b v v)
      _ = _ := congrArg (c * ·) ((inner_riemannianBundle g b v v).symm.trans k₂)
  rw [← Real.sqrt_sq n₁, hsq, Real.sqrt_mul hc.le, Real.sqrt_sq n₂]

/-- Multiplying a metric by a positive constant `c` multiplies the extended norm of every vector
by `√c`. -/
theorem enorm_rescale_const (b : B) (v : V b) :
    (letI : RiemannianBundle V :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩; ‖v‖ₑ) =
      ENNReal.ofReal √c * (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩; ‖v‖ₑ) := by
  have e₁ := (letI : RiemannianBundle V :=
    ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩; ofReal_norm v)
  have e₂ := (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩; ofReal_norm v)
  rw [← e₁, ← e₂, norm_rescale_const g hc b v, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]

end Norm

section Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) {c : ℝ} (hc : 0 < c)

/-- Multiplying a metric by a positive constant `c` multiplies the length of every path by
`√c`. -/
theorem pathELength_rescale_const (γ : ℝ → M) (a b : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      pathELength I γ a b) =
      ENNReal.ofReal √c *
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          pathELength I γ a b) := by
  have h₁ := (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
    pathELength_eq_lintegral_mfderiv_Icc (I := I) (γ := γ) (a := a) (b := b))
  have h₂ := (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
    pathELength_eq_lintegral_mfderiv_Icc (I := I) (γ := γ) (a := a) (b := b))
  rw [h₁, h₂, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr fun t ↦ enorm_rescale_const g hc _ _

/-- Multiplying a metric by a positive constant `c` multiplies the Riemannian distance between
any two points by `√c`. -/
theorem riemannianEDist_rescale_const (x y : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      riemannianEDist I x y) =
      ENNReal.ofReal √c *
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          riemannianEDist I x y) := by
  have h₁ := (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
    riemannianEDist_def I x y)
  have h₂ := (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
    riemannianEDist_def I x y)
  have hc₀ : ENNReal.ofReal √c ≠ 0 := (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hc)).ne'
  rw [h₁, h₂, ENNReal.mul_iInf_of_ne hc₀ ENNReal.ofReal_ne_top]
  refine iInf_congr fun γ ↦ ?_
  rw [ENNReal.mul_iInf_of_ne hc₀ ENNReal.ofReal_ne_top]
  refine iInf_congr fun _ ↦ ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_congr fun t ↦ enorm_rescale_const g hc _ _

/-- **Intrinsic open balls under rescaling.** A point is at `c g`-distance less than `√c r` from
`x` exactly when it is at `g`-distance less than `r`. -/
theorem riemannianEDist_rescale_const_lt_iff (x y : M) (r : ℝ≥0∞) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      riemannianEDist I x y) < ENNReal.ofReal √c * r ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      riemannianEDist I x y) < r := by
  rw [riemannianEDist_rescale_const g hc]
  exact ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hc)).ne'
    ENNReal.ofReal_ne_top

/-- **Intrinsic closed balls under rescaling.** A point is at `c g`-distance at most `√c r` from
`x` exactly when it is at `g`-distance at most `r`. -/
theorem riemannianEDist_rescale_const_le_iff (x y : M) (r : ℝ≥0∞) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      riemannianEDist I x y) ≤ ENNReal.ofReal √c * r ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      riemannianEDist I x y) ≤ r := by
  rw [riemannianEDist_rescale_const g hc]
  exact ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hc)).ne'
    ENNReal.ofReal_ne_top

end Manifold

end Bundle.ContMDiffRiemannianMetric
