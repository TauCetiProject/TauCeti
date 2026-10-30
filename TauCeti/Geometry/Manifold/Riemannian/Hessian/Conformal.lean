/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Conformal

/-!
# Hessians under conformal changes of metric

For a positive factor `f`, the scalar Hessian for `f g` differs from that for `g` by
`-(2 f)⁻¹ (df ⊗ du + du ⊗ df - ⟪grad f, grad u⟫ g)`. This is a tensor identity,
not just its trace: it controls second directional derivatives in a conformally changed metric.
We also give the real-power version, which applies to the factor `u ^ (4 / (n - 2))`.
The metric needs only one continuous derivative, and the differentiated function needs two
continuous derivatives at the point in question.

The two metric instances in each statement have disjoint scopes. All derivatives and tangent
vectors use the native manifold carriers. The calculation combines
`TauCeti.Manifold.hessian_apply_eq_mvfderiv_sub` with
`Bundle.ContMDiffRiemannianMetric.leviCivitaConnection_rescale_apply`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2.
* A. L. Besse, *Einstein Manifolds*, §1.J, for the conformal connection formula.
-/

public section

open Bundle TauCeti.Manifold
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] {n : ℕ∞ω}

/-- The Hessian for `f g` is the Hessian for `g` minus the differential of the function
applied to the conformal connection correction. Only `C¹` regularity of the metric and factor
and pointwise `C²` regularity of the function are required. -/
private theorem hessian_rescale_sub_conformalConnectionTensor
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    {u : M → ℝ} {x : M} (hu : ContMDiffAt I 𝓘(ℝ) 2 u x) (v w : TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I u x v w) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I u x v w - mvfderiv I u x (conformalConnectionTensor I f x w v)) := by
  let V : (y : M) → TangentSpace I y := FiberBundle.extend E v
  let W : (y : M) → TangentSpace I y := FiberBundle.extend E w
  have hW : MDiffAt (T% W) x := FiberBundle.mdifferentiableAt_extend I E w
  have hH (g' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) :=
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    hessian_apply_eq_mvfderiv_sub x hu V W hW
  have hc := g.leviCivitaConnection_rescale_apply hn hf hf_pos hW v
  dsimp only [V, W] at hH hc
  simp only [FiberBundle.extend_apply_self] at hH hc
  rw [hH (g.rescale f hf hf_pos), hH g, hc, map_add]
  ring

/-- **Conformal Hessian formula.** For `ĝ = f g`,
`Hess_ĝ u = Hess_g u - (2 f)⁻¹ (df ⊗ du + du ⊗ df - ⟪grad f, grad u⟫_g g)`. -/
theorem hessian_rescale
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    {u : M → ℝ} {x : M} (hu : ContMDiffAt I 𝓘(ℝ) 2 u x) (v w : TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I u x v w) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I u x v w - (2 * f x)⁻¹ *
        (mvfderiv I f x v * mvfderiv I u x w +
          mvfderiv I f x w * mvfderiv I u x v -
          ⟪mgradient I f x, mgradient I u x⟫_ℝ * ⟪v, w⟫_ℝ)) := by
  rw [g.hessian_rescale_sub_conformalConnectionTensor hn hf hf_pos hu]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  rw [conformalConnectionTensor_apply]
  simp only [map_smul, map_sub, map_add, smul_eq_mul]
  rw [← inner_mgradient (f := u) (mgradient I f x),
    real_inner_comm (mgradient I u x), real_inner_comm w v]
  ring

/-- **Hessian under a power rescaling.** For `ĝ = a ^ p g` with `a > 0`, the Hessian
correction has coefficient `p / (2 a)`. In particular `p = 4 / (dim M - 2)` gives the
Yamabe rescaling coefficient `2 / ((dim M - 2) a)`. -/
theorem hessian_rescale_rpow
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {a : M → ℝ} (ha : ContMDiff I 𝓘(ℝ) n a) (ha_pos : ∀ x, 0 < a x) (p : ℝ)
    {hf : ContMDiff I 𝓘(ℝ) n fun x ↦ a x ^ p} {hf_pos : ∀ x, 0 < a x ^ p}
    {u : M → ℝ} {x : M} (hu : ContMDiffAt I 𝓘(ℝ) 2 u x) (v w : TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun x ↦ a x ^ p) hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I u x v w) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      hessian I u x v w - p / (2 * a x) *
        (mvfderiv I a x v * mvfderiv I u x w +
          mvfderiv I a x w * mvfderiv I u x v -
          ⟪mgradient I a x, mgradient I u x⟫_ℝ * ⟪v, w⟫_ℝ)) := by
  rw [g.hessian_rescale_sub_conformalConnectionTensor hn hf hf_pos hu]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  rw [conformalConnectionTensor_rpow (ha.mdifferentiableAt (one_pos.trans_le hn).ne') (ha_pos x)]
  simp only [smul_apply, conformalConnectionTensor_apply, map_smul, map_sub, map_add, smul_eq_mul]
  rw [← inner_mgradient (f := u) (mgradient I a x),
    real_inner_comm (mgradient I u x), real_inner_comm w v]
  ring

end Bundle.ContMDiffRiemannianMetric
