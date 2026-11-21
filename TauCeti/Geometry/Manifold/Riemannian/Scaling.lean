/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic

/-!
# Curvature and the Laplacian under constant rescaling of a metric

Let `g` be a Riemannian metric on `M` and `c` a positive constant, and let `c g` be the rescaled
metric `Bundle.ContMDiffRiemannianMetric.rescale` by the constant function `c`. The Koszul formula
is homogeneous of degree one in the metric when `c` is constant, so `g` and `c g` have the same
Levi-Civita connection, and hence the same `(1,3)` curvature tensor and the same Ricci tensor.
Scalar curvature is the metric trace of the Ricci tensor, and the trace for `c g` is `c⁻¹` times
the trace for `g`, so

`Scal(c g) = c⁻¹ Scal(g)`.

Sectional curvature is the quotient `⟪R(u, v) v, u⟫ / (|u|²|v|² - ⟪u, v⟫²)`, whose numerator
scales by `c` and whose denominator scales by `c²`, so `K(c g) = c⁻¹ K(g)`. Hence `c g` has
constant sectional curvature `k` exactly when `g` has constant sectional curvature `c k`; for
example the round sphere of radius `r` has sectional curvature `1 / r²`.

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
* `Bundle.ContMDiffRiemannianMetric.subsingleton_of_inner_eq_smul_of_nonpos` and
  `Bundle.ContMDiffRiemannianMetric.finrank_eq_zero_of_inner_eq_smul_of_nonpos`: bundle metrics
  with `g' = a g` on the fibre over a point `x` for some `a ≤ 0` exist only when that fibre, and
  the model fibre, are zero.
* `Bundle.ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_eq_of_inner_eq_smul` and
  `Bundle.ContMDiffRiemannianMetric.scalarCurvature_eq_inv_mul_of_inner_eq_smul`:
  `Ric(g') = Ric(g)` and `Scal(g') = a⁻¹ Scal(g)` for a metric `g'` known only to satisfy
  `g' = a g` for a constant `a`, with no sign condition.
* `scalarCurvature_eq_of_inner_eq_smul_of_ricciTensor_eq_smul_inner` and
  `ricciTensor_leviCivitaConnection_eq_smul_inner_of_inner_eq_smul`, in the namespace
  `Bundle.ContMDiffRiemannianMetric`: `Scal(a g) = n c / a` and `Ric(a g) = (c / a) (a g)` when
  `Ric(g) = c g`.
* `ricciTensor_leviCivitaConnection_rescale_const_eq_smul_inner_iff`, in the same namespace: `c g`
  is Einstein with constant `k` exactly when `g` is Einstein with constant `c k`.
* `Bundle.ContMDiffRiemannianMetric.sectionalCurvature_leviCivitaConnection_rescale_const`:
  `K(c g) = c⁻¹ K(g)`.
* `Bundle.ContMDiffRiemannianMetric.isConstantCurvatureTensor_rescale_const_iff` and its
  sectional-curvature form
  `hasConstantSectionalCurvature_leviCivitaConnection_rescale_const_iff`: `c g` has constant
  curvature `k` exactly when `g` has constant curvature `c k`.
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

section Nonpos

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n n' : ℕ∞ω}

omit [FiniteDimensional ℝ E] in
/-- If two bundle metrics satisfy `g' = a g` on the fibre over a point `x` for some `a ≤ 0`, then
that fibre is zero. -/
theorem subsingleton_of_inner_eq_smul_of_nonpos
    {g' : ContMDiffRiemannianMetric I n' F V} {g : ContMDiffRiemannianMetric I n F V} {a : ℝ}
    {x : M} (h : g'.inner x = a • g.inner x) (ha : a ≤ 0) : Subsingleton (V x) := by
  have hzero (u : V x) : u = 0 := by
    by_contra hu
    have h' := g'.pos x u hu
    rw [h, smul_apply, smul_apply, smul_eq_mul] at h'
    nlinarith [g.pos x u hu]
  exact subsingleton_iff.2 fun v w ↦ (hzero v).trans (hzero w).symm

omit [FiniteDimensional ℝ E] in
/-- If two bundle metrics satisfy `g' = a g` on the fibre over a point `x` for some `a ≤ 0`, then
the model fibre `F` is zero-dimensional. -/
theorem finrank_eq_zero_of_inner_eq_smul_of_nonpos
    {g' : ContMDiffRiemannianMetric I n' F V} {g : ContMDiffRiemannianMetric I n F V} {a : ℝ}
    {x : M} (h : g'.inner x = a • g.inner x) (ha : a ≤ 0) : Module.finrank ℝ F = 0 := by
  have := subsingleton_of_inner_eq_smul_of_nonpos h ha
  rw [← ((trivializationAt F V x).linearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)).finrank_eq]
  exact Module.finrank_zero_of_subsingleton

end Nonpos

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

/-- Multiplying a metric by `c > 0` multiplies its lowered Riemann tensor by `c`. -/
theorem riemannCurvatureTensor_leviCivitaConnection_rescale_const (x : M)
    (u v w z : TangentSpace I x) :
    (letI : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).riemannCurvatureTensor x u v w z) =
    c * (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).riemannCurvatureTensor x u v w z) := by
  simp only [CovariantDerivative.riemannCurvatureTensor_apply, inner_riemannianBundle,
    rescale_inner, curvatureTensor_leviCivitaConnection_rescale_const g hc x]

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

/-- Metrics which are constant multiples of each other, `g' = a g`, have the same Ricci tensor.
No sign condition on `a` is needed: positivity of both metrics forces `0 < a` unless the tangent
spaces are zero, and then both Ricci tensors vanish. This is the form used for a family of metrics
known only through its inner products, such as `τ ↦ (1 - 2 λ τ) g` on a time interval. -/
theorem ricciTensor_leviCivitaConnection_eq_of_inner_eq_smul
    {g' g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {a : ℝ}
    (h : ∀ y, g'.inner y = a • g.inner y) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x) := by
  by_cases ha : 0 < a
  · obtain rfl : g' = g.rescale (fun _ ↦ a) contMDiff_const fun _ ↦ ha := by
      ext y v w
      simp [h]
    exact ricciTensor_leviCivitaConnection_rescale_const g ha x
  · have hE := (finrank_eq_zero_of_inner_eq_smul_of_nonpos (h x) (not_lt.1 ha)).trans_le zero_le_one
    simp [CovariantDerivative.ricciTensor_eq_zero_of_finrank_le_one _ x hE]

/-- Metrics which are constant multiples of each other, `g' = a g`, have scalar curvatures related
by `Scal(g') = a⁻¹ Scal(g)`. No sign condition on `a` is needed, as in
`Bundle.ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_eq_of_inner_eq_smul`. -/
theorem scalarCurvature_eq_inv_mul_of_inner_eq_smul
    {g' g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {a : ℝ}
    (h : ∀ y, g'.inner y = a • g.inner y) (x : M) :
    g'.scalarCurvature x = a⁻¹ * g.scalarCurvature x := by
  by_cases ha : 0 < a
  · obtain rfl : g' = g.rescale (fun _ ↦ a) contMDiff_const fun _ ↦ ha := by
      ext y v w
      simp [h]
    exact scalarCurvature_rescale_const g ha x
  · have hE := (finrank_eq_zero_of_inner_eq_smul_of_nonpos (h x) (not_lt.1 ha)).trans_le zero_le_one
    simp only [scalarCurvature_def]
    simp [CovariantDerivative.scalarCurvature_eq_zero_of_ricciTensor_eq_zero,
      CovariantDerivative.ricciTensor_eq_zero_of_finrank_le_one _ x hE]

/-- A constant multiple `g' = a g` of a metric with `Ric(g) = c g` at `x` has scalar curvature
`Scal(g') = n c / a` at `x`, where `n` is the dimension. -/
theorem scalarCurvature_eq_of_inner_eq_smul_of_ricciTensor_eq_smul_inner
    {g' g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {a : ℝ} {x : M}
    (h : ∀ y, g'.inner y = a • g.inner y)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x =
        c • innerₗ (TangentSpace I x)) :
    g'.scalarCurvature x = Module.finrank ℝ E * c / a := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [scalarCurvature_eq_inv_mul_of_inner_eq_smul h x, scalarCurvature_def,
    (CovariantDerivative.leviCivitaConnection I M).scalarCurvature_eq_of_ricciTensor_eq_smul_inner
      x c hRic,
    TauCeti.finrank_tangentSpace, inv_mul_eq_div]

/-- A constant multiple `g' = a g` of a metric with `Ric(g) = c g` at `x` has `Ric(g') = (c / a) g'`
at `x`. No sign condition on `a` is needed: for `a ≤ 0` the tangent spaces are zero. -/
theorem ricciTensor_leviCivitaConnection_eq_smul_inner_of_inner_eq_smul
    {g' g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {a : ℝ} {x : M}
    (h : ∀ y, g'.inner y = a • g.inner y)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x =
        c • innerₗ (TangentSpace I x)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
    (CovariantDerivative.leviCivitaConnection I M).ricciTensor x =
      (c / a) • innerₗ (TangentSpace I x) := by
  rw [ricciTensor_leviCivitaConnection_eq_of_inner_eq_smul h x, hRic]
  ext u v
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul, inner_riemannianBundle, h,
    smul_apply]
  rcases eq_or_ne a 0 with rfl | ha
  · have := subsingleton_of_inner_eq_smul_of_nonpos (h x) le_rfl
    simp [Subsingleton.elim u 0]
  · field_simp

/-- **Einstein metrics under constant scaling.** For a constant `c > 0`, the metric `c g` has
`Ric(c g) = k (c g)` at `x` exactly when `Ric(g) = (c k) g` at `x`. -/
theorem ricciTensor_leviCivitaConnection_rescale_const_eq_smul_inner_iff (x : M) (k : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x =
        k • innerₗ (TangentSpace I x)) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x =
        (c * k) • innerₗ (TangentSpace I x)) := by
  constructor
  · intro hRic
    have := ricciTensor_leviCivitaConnection_eq_smul_inner_of_inner_eq_smul (g' := g) (a := c⁻¹)
      (fun y ↦ by ext v w; simp [hc.ne']) hRic
    rwa [div_inv_eq_mul, mul_comm] at this
  · intro hRic
    have := ricciTensor_leviCivitaConnection_eq_smul_inner_of_inner_eq_smul
      (g' := g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) (a := c)
      (fun y ↦ by ext v w; simp) hRic
    rwa [mul_div_cancel_left₀ _ hc.ne'] at this

/-- **Scaling of sectional curvature.** Multiplying a smooth metric by a positive constant `c`
multiplies the sectional curvature of every pair of tangent vectors by `c⁻¹`. -/
theorem sectionalCurvature_leviCivitaConnection_rescale_const (x : M) (u v : TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v) =
    c⁻¹ * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v) := by
  -- The curvature tensor is unchanged, while the numerator `⟪R(u, v) v, u⟫` scales by `c` and the
  -- Gram determinant by `c²`.
  simp only [CovariantDerivative.sectionalCurvature_apply, Matrix.real_det_gram_fin_two,
    inner_riemannianBundle, rescale_inner,
    curvatureTensor_leviCivitaConnection_rescale_const g hc x]
  rw [show ∀ a b d : ℝ, c * a * (c * b) - (c * d) ^ 2 = c ^ 2 * (a * b - d ^ 2) by
      intros; ring]
  field_simp

/-- Multiplying a smooth metric by a positive constant `c` turns sectional curvature `c * k` at a
point into sectional curvature `k`. -/
@[simp]
theorem hasSectionalCurvatureAt_leviCivitaConnection_rescale_const_iff (x : M) (k : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).HasSectionalCurvatureAt
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x k) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).HasSectionalCurvatureAt
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x (c * k)) := by
  simp only [CovariantDerivative.hasSectionalCurvatureAt_iff,
    sectionalCurvature_leviCivitaConnection_rescale_const g hc, inv_mul_eq_iff_eq_mul₀ hc.ne']

/-- **Scaling of constant sectional curvature.** Multiplying a smooth metric by a positive
constant `c` turns constant sectional curvature `c * k` into constant sectional curvature `k`. -/
@[simp]
theorem hasConstantSectionalCurvature_leviCivitaConnection_rescale_const_iff (k : ℝ) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).HasConstantSectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) k) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).HasConstantSectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) (c * k)) := by
  simp only [CovariantDerivative.hasConstantSectionalCurvature_iff,
    hasSectionalCurvatureAt_leviCivitaConnection_rescale_const_iff g hc]

/-- Multiplying a smooth metric by a positive constant `c` turns the constant-curvature tensor
with parameter `c * κ` into the one with parameter `κ`. -/
@[simp]
theorem isConstantCurvatureTensor_rescale_const_iff (κ : ℝ) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).IsConstantCurvatureTensor κ ↔
      g.IsConstantCurvatureTensor (c * κ) := by
  simp only [isConstantCurvatureTensor_iff, inner_riemannianBundle, rescale_inner,
    curvatureTensor_leviCivitaConnection_rescale_const g hc]
  exact forall₄_congr fun x w u v ↦ Eq.congr_right (by module)

end Curvature

end Bundle.ContMDiffRiemannianMetric
