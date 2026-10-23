/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

/-!
# Curvature and the Laplacian under constant rescaling of a metric

Let `g` be a Riemannian metric on `M` and `c` a positive constant, and let `c g` be the rescaled
metric `Bundle.ContMDiffRiemannianMetric.rescale` by the constant function `c`. The Koszul formula
is homogeneous of degree one in the metric when `c` is constant, so `g` and `c g` have the same
Levi-Civita connection, and hence the same `(1,3)` curvature tensor and the same Ricci tensor.
Scalar curvature is the metric trace of the Ricci tensor, and the trace for `c g` is `c⁻¹` times
the trace for `g`, so

`Scal(c g) = c⁻¹ Scal(g)`.

The gradient of a function is the dual of its differential through the metric, so
`grad_{c g} f = c⁻¹ grad_g f`; since the Levi-Civita connections agree, the Laplace–Beltrami
operator `Δ = div ∘ grad` scales in the same way, `Δ_{c g} = c⁻¹ Δ_g`.

Both metrics are installed in turn as the `RiemannianBundle` instance of the tangent bundle of
`M`. Connections and curvature tensors do not depend on the metric, so they are compared directly
on `M`. Mathlib's `CovariantDerivative.leviCivitaConnection` is unconstrained on vector fields which
are not differentiable at the point, so the two Levi-Civita connections are compared on
differentiable fields; this determines the curvature tensor.

## Main results

* `Bundle.ContMDiffRiemannianMetric.isMetricCompatible_rescale_const_iff`: a connection is
  compatible with `c g` exactly when it is compatible with `g`.
* `Bundle.ContMDiffRiemannianMetric.isLeviCivitaConnection_rescale_const_iff`: a connection is
  Levi-Civita for `c g` exactly when it is Levi-Civita for `g`.
* `Bundle.ContMDiffRiemannianMetric.leviCivitaConnection_rescale_const_apply`: the Levi-Civita
  connections of `c g` and `g` agree on differentiable vector fields.
* `Bundle.ContMDiffRiemannianMetric.curvatureTensor_leviCivitaConnection_rescale_const` and
  `Bundle.ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_rescale_const`: the curvature
  and Ricci tensors of `c g` and `g` coincide.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_rescale_const`: `Scal(c g) = c⁻¹ Scal(g)`.
* `Bundle.ContMDiffRiemannianMetric.mgradient_rescale_const` and
  `Bundle.ContMDiffRiemannianMetric.laplaceBeltrami_rescale_const`: `grad_{c g} = c⁻¹ grad_g`
  and `Δ_{c g} = c⁻¹ Δ_g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 5 (the Koszul formula) and Chapter 7 (curvature conventions).
* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section MetricCompatible

variable [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] {n : ℕ∞ω}

omit [FiniteDimensional ℝ E] in
/-- Multiplying a `C¹` bundle metric by a positive constant does not change which connections are
compatible with it. -/
theorem isMetricCompatible_rescale_const_iff (g : ContMDiffRiemannianMetric I n F V)
    (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c) (cov : CovariantDerivative I F V) :
    (letI : RiemannianBundle V :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn;
      cov.IsMetricCompatible) ↔
    (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn;
      cov.IsMetricCompatible) := by
  -- The derivative of `c g(σ, τ)` is `c` times the derivative of `g(σ, τ)`.
  have key : ∀ ⦃x : M⦄ ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      mvfderiv I (fun y ↦ c * g.inner y (σ y) (τ y)) x =
        c • mvfderiv I (fun y ↦ g.inner y (σ y) (τ y)) x := by
    intro x σ τ hσ hτ
    let _ : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
    have hg : MDiffAt (fun y ↦ g.inner y (σ y) (τ y)) x := by
      simpa only [inner_riemannianBundle] using hσ.inner_bundle hτ
    rw [mvfderiv_fun_mul mdifferentiableAt_const hg, mvfderiv_const, smul_zero, add_zero]
  rw [isMetricCompatible_iff_inner _ hn, isMetricCompatible_iff_inner g hn]
  refine ⟨fun h x X σ τ hX hσ hτ ↦ ?_, fun h x X σ τ hX hσ hτ ↦ ?_⟩
  · have h := h hX hσ hτ
    simp only [rescale_inner, key hσ hτ, smul_apply, smul_eq_mul] at h
    exact mul_left_cancel₀ hc.ne' (by linear_combination h)
  · simp only [rescale_inner, key hσ hτ, smul_apply, smul_eq_mul, h hX hσ hτ]
    ring

end MetricCompatible

section LeviCivita

variable [IsManifold I 2 M] {n : ℕ∞ω}

/-- Multiplying a `C¹` metric by a positive constant does not change which connections are
Levi-Civita connections. -/
theorem isLeviCivitaConnection_rescale_const_iff
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      cov.IsLeviCivitaConnection) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      cov.IsLeviCivitaConnection) := by
  have hm := isMetricCompatible_rescale_const_iff g hn hc cov
  -- Torsion does not involve the metric.
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> obtain ⟨h₁, h₂⟩ := h
  · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact ⟨hm.1 h₁, h₂⟩
  · let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact ⟨hm.2 h₁, h₂⟩

/-- The Levi-Civita connections of a `C¹` metric and of a positive constant multiple of it agree
on every vector field differentiable at the point. -/
theorem leviCivitaConnection_rescale_const_apply
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.leviCivitaConnection I M Y x) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.leviCivitaConnection I M Y x) := by
  have h := (isLeviCivitaConnection_rescale_const_iff g hn hc
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.leviCivitaConnection I M)).2 (by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  exact ContinuousLinearMap.ext fun X₀ ↦
    (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I).uniqueness I h hY X₀

end LeviCivita

section Laplacian

variable {n : ℕ∞ω}

/-- Multiplying a metric by a positive constant `c` multiplies the gradient of every function by
`c⁻¹`. -/
theorem mgradient_rescale_const [IsManifold I 1 M]
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {c : ℝ} (hc : 0 < c) (f : M → ℝ) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      TauCeti.Manifold.mgradient I f x) =
    c⁻¹ • (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      TauCeti.Manifold.mgradient I f x) := by
  have hg (v : TangentSpace I x) :
      g.inner x (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩; TauCeti.Manifold.mgradient I f x) v = mvfderiv I f x v := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    exact TauCeti.Manifold.inner_mgradient v
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
  refine (TauCeti.Manifold.eq_mgradient_iff.2 fun v ↦ ?_).symm
  rw [inner_riemannianBundle, rescale_inner, map_smul, smul_apply, hg, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- **Scaling of the Laplacian.** Multiplying a `C¹` metric by a positive constant `c` multiplies
the Laplace–Beltrami operator of every `C²` function by `c⁻¹`. -/
theorem laplaceBeltrami_rescale_const [IsManifold I 2 M]
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {c : ℝ} (hc : 0 < c) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      TauCeti.Manifold.laplaceBeltrami I f x) =
    c⁻¹ * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      TauCeti.Manifold.laplaceBeltrami I f x) := by
  -- The gradient field of `f` for `g` is differentiable, so the Levi-Civita connections of `g`
  -- and `c g` agree on its multiples.
  have hY : MDiffAt (T% (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩; TauCeti.Manifold.mgradient I f)) x := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact TauCeti.Manifold.mdifferentiable_mgradient (I := I) hf x
  have hY' : MDiffAt (T% (c⁻¹ • (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩; TauCeti.Manifold.mgradient I f))) x :=
    mdifferentiableAt_const.smul_section hY
  have hgrad : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      TauCeti.Manifold.mgradient I f) =
      c⁻¹ • (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        TauCeti.Manifold.mgradient I f) :=
    funext fun y ↦ mgradient_rescale_const g hc f y
  simp only [TauCeti.Manifold.laplaceBeltrami_def, TauCeti.Manifold.divergence_def]
  rw [hgrad, leviCivitaConnection_rescale_const_apply g hn hc hY']
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  rw [(CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.smul_const
    c⁻¹ hY]
  simp

end Laplacian

section Curvature

variable [T2Space M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {c : ℝ} (hc : 0 < c)

/-- Multiplying a smooth metric by a positive constant does not change the `(1,3)` curvature
tensor of its Levi-Civita connection. -/
theorem curvatureTensor_leviCivitaConnection_rescale_const (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x) :=
  CovariantDerivative.curvatureTensor_congr _ (fun _ hσ y ↦
    leviCivitaConnection_rescale_const_apply g (by simp) hc (hσ.mdifferentiable (by simp) y)) x

/-- Multiplying a smooth metric by a positive constant does not change the Ricci tensor of its
Levi-Civita connection. -/
theorem ricciTensor_leviCivitaConnection_rescale_const (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x) := by
  ext u v
  simp only [CovariantDerivative.ricciTensor_apply,
    curvatureTensor_leviCivitaConnection_rescale_const g hc x]

/-- **Scaling of scalar curvature.** Multiplying a smooth metric by a positive constant `c`
multiplies its scalar curvature by `c⁻¹`. -/
@[simp]
theorem scalarCurvature_rescale_const (x : M) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).scalarCurvature x =
      c⁻¹ * g.scalarCurvature x := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [scalarCurvature_rescale_eq_sum g _ _ b, ricciTensor_leviCivitaConnection_rescale_const g hc x,
    scalarCurvature_def, CovariantDerivative.scalarCurvature_eq_sum _ x b]

end Curvature

end Bundle.ContMDiffRiemannianMetric
