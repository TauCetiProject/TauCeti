/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal

/-!
# Vector norms and path lengths under constant rescaling

Multiplying a Riemannian metric by a positive constant `c` multiplies the norm of each
vector and the extended length of each path by `√c`.

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

end Manifold

end Bundle.ContMDiffRiemannianMetric
