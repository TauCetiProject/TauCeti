/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Conformal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Conformal
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule

/-!
# The divergence and the Laplacian under a conformal change of metric

Let `g` be a `C¹` Riemannian metric on a manifold `M` of real dimension `N`, let `f` be a positive
function, and let `ĝ = f g` be the conformally rescaled metric
`Bundle.ContMDiffRiemannianMetric.rescale`. The Levi-Civita connection of `ĝ` is that of `g` plus
the conformal connection tensor of `f`
(`Bundle.ContMDiffRiemannianMetric.leviCivitaConnection_rescale_apply`), whose trace is
`(N / 2) f⁻¹ df` (`TauCeti.Manifold.trace_conformalConnectionTensor`). Together with
`grad_ĝ u = f⁻¹ grad_g u` (`Bundle.ContMDiffRiemannianMetric.mgradient_rescale`) this gives

* `div_ĝ X = div_g X + (N / 2) f⁻¹ df(X)`;
* `Δ_ĝ u = f⁻¹ (Δ_g u + ((N - 2) / 2) f⁻¹ ⟪grad_g f, grad_g u⟫_g)`,

for the Laplace–Beltrami operator `Δ = div ∘ grad` (`TauCeti.Manifold.laplaceBeltrami`). For a
power `f = u ^ p` of a positive function the second formula reads
`Δ_ĝ v = u ^ (-p) (Δ_g v + ((N - 2) p / 2) u⁻¹ ⟪grad_g u, grad_g v⟫_g)`; for the Yamabe factor
`p = 4 / (N - 2)` the coefficient is `2`, which is how the Laplacian part of the conformal
Laplacian transforms.

As in `TauCeti.Geometry.Manifold.Riemannian.Scaling`, each metric is installed in turn as the
`RiemannianBundle` instance of the tangent bundle of `M`. The tangent bundle and differentials do
not depend on the metric, so the two metric-dependent Levi-Civita connections, divergences and
Laplacians are compared directly on the same bundle over `M`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.divergence_rescale`: the divergence of `f g`.
* `Bundle.ContMDiffRiemannianMetric.laplaceBeltrami_rescale`: the Laplacian of `f g`.
* `Bundle.ContMDiffRiemannianMetric.laplaceBeltrami_rescale_rpow`: the Laplacian of `u ^ p g`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.J.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

variable [IsManifold I 2 M]

/-- **Divergence under conformal change.** In real dimension `N`, the divergence of a vector
field `X` for the rescaled metric `f g` is `div_g X + (N / 2) f⁻¹ df(X)`, at every point where
`X` is differentiable. -/
theorem divergence_rescale
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    {X : Π x : M, TangentSpace I x} {x : M} (hX : MDiffAt (T% X) x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      divergence I X x) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      divergence I X x) +
      (Module.finrank ℝ E / 2) * (f x)⁻¹ * mvfderiv I f x (X x) := by
  have h : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.leviCivitaConnection I M X x) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.leviCivitaConnection I M X x + conformalConnectionTensor I f x (X x)) :=
    ContinuousLinearMap.ext fun v ↦ leviCivitaConnection_rescale_apply g hn hf hf_pos hX v
  simp only [divergence_def]
  rw [h]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [ContinuousLinearMap.toLinearMap_add, map_add, trace_conformalConnectionTensor]

/-- **Laplacian under conformal change.** In real dimension `N`, the Laplace–Beltrami operator of
the rescaled metric `f g` on a `C²` function `u` is
`Δ_{f g} u = f⁻¹ (Δ_g u + ((N - 2) / 2) f⁻¹ ⟪grad_g f, grad_g u⟫_g)`. -/
theorem laplaceBeltrami_rescale
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      laplaceBeltrami I u x) =
    (f x)⁻¹ * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      laplaceBeltrami I u x + (((Module.finrank ℝ E : ℝ) - 2) / 2) * (f x)⁻¹ *
        ⟪mgradient I f x, mgradient I u x⟫) := by
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have hfinv : MDiffAt (fun y ↦ (f y)⁻¹) x :=
    (hf.inv₀ fun y ↦ (hf_pos y).ne').mdifferentiableAt hn₀
  have hY : MDiffAt (T% (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩; mgradient I u)) x := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact mdifferentiable_mgradient (I := I) hu x
  have hgrad : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      mgradient I u) =
      (fun y ↦ (f y)⁻¹) • (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩; mgradient I u) :=
    funext fun y ↦ mgradient_rescale g hf hf_pos u y
  simp only [laplaceBeltrami_def]
  rw [hgrad, divergence_rescale g hn hf hf_pos (hfinv.smul_section hY)]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  -- The derivative of `f⁻¹` is `-f⁻²` times that of `f`, read through the gradient of `g`.
  have hinv : mgradient I (fun y ↦ (f y)⁻¹) x = (-(f x ^ 2)⁻¹) • mgradient I f x :=
    mgradient_comp_hasDerivAt (g := fun t ↦ t⁻¹) (hasDerivAt_inv (hf_pos x).ne')
      (hf.mdifferentiableAt hn₀)
  rw [divergence_smul_function I _ _ x hfinv hY, ← inner_mgradient, hinv, Pi.smul_apply', map_smul,
    ← inner_mgradient, real_inner_smul_left, smul_eq_mul]
  field_simp [(hf_pos x).ne']
  ring

/-- **Laplacian under a conformal power.** For a positive function `u` differentiable at `x`, the
Laplace–Beltrami operator of the rescaled metric `u ^ p g` on a `C²` function `v` is
`Δ_{u ^ p g} v = u ^ (-p) (Δ_g v + ((N - 2) p / 2) u⁻¹ ⟪grad_g u, grad_g v⟫_g)` in real
dimension `N`. -/
theorem laplaceBeltrami_rescale_rpow
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {u : M → ℝ} (hu_pos : ∀ x, 0 < u x) {p : ℝ} {hf : ContMDiff I 𝓘(ℝ) n fun x ↦ u x ^ p}
    {x : M} (hu : MDiffAt u x) {v : M → ℝ} (hv : ContMDiff I 𝓘(ℝ) 2 v) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale _ hf fun x ↦ Real.rpow_pos_of_pos (hu_pos x) p).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      laplaceBeltrami I v x) =
    u x ^ (-p) * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      laplaceBeltrami I v x + (((Module.finrank ℝ E : ℝ) - 2) * p / 2) * (u x)⁻¹ *
        ⟪mgradient I u x, mgradient I v x⟫) := by
  rw [laplaceBeltrami_rescale g hn hf _ hv x]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hux := hu_pos x
  have hgrad : mgradient I (fun y ↦ u y ^ p) x = (p * u x ^ (p - 1)) • mgradient I u x :=
    mgradient_comp_hasDerivAt (f := u) (Real.hasDerivAt_rpow_const (Or.inl hux.ne')) hu
  rw [hgrad, real_inner_smul_left, Real.rpow_neg hux.le, Real.rpow_sub_one hux.ne']
  field_simp

end Bundle.ContMDiffRiemannianMetric
