/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

-- Only the characterization lemma below accesses the unexposed defining tensor equality.
import all Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# Metric compatibility and higher metric product rules

This module characterizes metric compatibility as the vanishing of `derivMetricTensor`, without
assuming manifold regularity
(`CovariantDerivative.isMetricCompatible_iff_derivMetricTensor_eq_zero`).

For differentiable sections with locally constant inner product, metric compatibility gives
the skew-symmetry identity for their covariant derivatives, including orthogonality to a
section of locally constant length.

For sections whose covariant derivatives vanish, metric compatibility implies that their inner
product has vanishing differential (`IsMetricCompatible.hasMFDerivAt_inner_of_eq_zero`,
`IsMetricCompatible.mvfderiv_inner_eq_zero_of_cov_eq_zero`), is locally constant on open sets
(`IsMetricCompatible.eventuallyEq_inner_const_of_cov_eq_zero`), and is constant on preconnected open
sets (`IsMetricCompatible.inner_eq_of_isPreconnected_of_cov_eq_zero`).

It also records the twice-differentiated product rule for a metric-compatible covariant
derivative. It supplies the second-derivative calculation used to establish curvature
skew-adjointness and can be reused in other calculations with metric-compatible connections.

It also restates metric compatibility with a bundled metric `g`, installed as the
`RiemannianBundle` instance, in terms of the inner products of `g`
(`Bundle.ContMDiffRiemannianMetric.isMetricCompatible_iff_inner`). This is the form in which
connections are compared across different metrics on the same bundle.

For a metric-compatible torsion-free connection `∇` on the tangent bundle, it expresses the Lie
derivative of the metric through `∇`:
`(𝓛_X g)(Y, Z) = ⟪∇_Y X, Z⟫ + ⟪Y, ∇_Z X⟫`
(`CovariantDerivative.IsMetricCompatible.mvfderiv_inner_sub_inner_mlieBracket`).
-/

public section

open Bundle FiberBundle Filter VectorField
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V]
  {cov : CovariantDerivative I F V}

/-- Metric compatibility is precisely the vanishing of the covariant derivative of the metric
as a tensor. Unlike the section-based characterization, this needs no manifold regularity. -/
theorem isMetricCompatible_iff_derivMetricTensor_eq_zero :
    cov.IsMetricCompatible ↔ cov.derivMetricTensor = fun _ ↦ 0 := (Iff.rfl)

/-- The inner product of two sections parallel at a point has zero derivative there. -/
theorem IsMetricCompatible.hasMFDerivAt_inner_of_eq_zero (hcov : cov.IsMetricCompatible)
    {σ τ : Π x : M, V x} {x : M} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x)
    (hσ₀ : cov σ x = 0) (hτ₀ : cov τ x = 0) :
    HasMFDerivAt I 𝓘(ℝ) (fun y ↦ inner ℝ (σ y) (τ y)) x 0 := by
  have hd : mfderiv I 𝓘(ℝ) (fun y ↦ inner ℝ (σ y) (τ y)) x = 0 := by
    ext w
    apply (NormedSpace.fromTangentSpace (inner ℝ (σ x) (τ x))).injective
    simpa only [mvfderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, hσ₀, hτ₀, zero_apply,
      inner_zero_left, inner_zero_right, add_zero, map_zero] using
      hcov.mvfderiv_inner_eq (fun _ ↦ w) hσ hτ
  simpa only [hd] using (hσ.inner_bundle hτ).hasMFDerivAt

/-- For a metric-compatible connection, two differentiable sections with locally constant
inner product have skew-symmetric covariant derivatives at the point. -/
theorem IsMetricCompatible.inner_apply_add_inner_apply_eq_zero_of_eventuallyEq_const
    (hcov : cov.IsMetricCompatible) {σ τ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) {c : ℝ}
    (hc : (fun y ↦ inner ℝ (σ y) (τ y)) =ᶠ[𝓝 x] fun _ ↦ c)
    (v : TangentSpace I x) :
    inner ℝ (cov σ x v) (τ x) + inner ℝ (σ x) (cov τ x v) = 0 := by
  classical
  simpa only [Pi.single_eq_same, hc.mvfderiv_eq, mvfderiv_const, zero_apply] using
    (hcov.mvfderiv_inner_eq (Pi.single x v) hσ hτ).symm

/-- The covariant derivative of a section of locally constant length is orthogonal to that
section for a metric-compatible connection. -/
theorem IsMetricCompatible.inner_apply_self_eq_zero_of_eventuallyEq_const
    (hcov : cov.IsMetricCompatible) {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) {c : ℝ}
    (hc : (fun y ↦ inner ℝ (σ y) (σ y)) =ᶠ[𝓝 x] fun _ ↦ c)
    (v : TangentSpace I x) : inner ℝ (cov σ x v) (σ x) = 0 := by
  have h := hcov.inner_apply_add_inner_apply_eq_zero_of_eventuallyEq_const hσ hσ hc v
  rw [real_inner_comm (cov σ x v) (σ x)] at h
  linarith

/-- For a metric-compatible connection, the inner product of two sections that are differentiable
and parallel at `x` has vanishing differential at `x`. -/
theorem IsMetricCompatible.mvfderiv_inner_eq_zero_of_cov_eq_zero
    (hcov : cov.IsMetricCompatible) {σ τ : Π y : M, V y} {x : M}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x)
    (hσ0 : cov σ x = 0) (hτ0 : cov τ x = 0) :
    mvfderiv I (fun y ↦ inner ℝ (σ y) (τ y)) x = 0 :=
  TauCeti.mvfderiv_eq_zero_iff.mpr (hcov.hasMFDerivAt_inner_of_eq_zero hσ hτ hσ0 hτ0).mfderiv

variable [IsManifold I 1 M]

/-- For a metric-compatible connection, the inner product of two sections that are differentiable
and parallel on an open set `U` is locally constant on `U`. -/
theorem IsMetricCompatible.eventuallyEq_inner_const_of_cov_eq_zero
    (hcov : cov.IsMetricCompatible) {σ τ : Π y : M, V y} {U : Set M} (hU : IsOpen U)
    (hσ : MDiff[U] (T% σ)) (hτ : MDiff[U] (T% τ))
    (hσ0 : ∀ y ∈ U, cov σ y = 0) (hτ0 : ∀ y ∈ U, cov τ y = 0) {x : M} (hx : x ∈ U) :
    (fun y ↦ inner ℝ (σ y) (τ y)) =ᶠ[𝓝 x] fun _ ↦ inner ℝ (σ x) (τ x) := by
  have hdiff : MDifferentiableOn I 𝓘(ℝ) (fun y ↦ inner ℝ (σ y) (τ y)) U := fun y hy ↦
    (((hσ y hy).mdifferentiableAt (hU.mem_nhds hy)).inner_bundle
      ((hτ y hy).mdifferentiableAt (hU.mem_nhds hy))).mdifferentiableWithinAt
  refine hdiff.eventuallyEq_const_of_mfderiv_eq_zero hU (fun y hy ↦ ?_) hx
  exact (hcov.hasMFDerivAt_inner_of_eq_zero
    ((hσ y hy).mdifferentiableAt (hU.mem_nhds hy))
    ((hτ y hy).mdifferentiableAt (hU.mem_nhds hy))
    (hσ0 y hy) (hτ0 y hy)).mfderiv

/-- **Parallel sections of a metric-compatible connection have constant inner products** on any
preconnected open set. Neither boundarylessness nor finite dimensionality of `M` is required. -/
theorem IsMetricCompatible.inner_eq_of_isPreconnected_of_cov_eq_zero
    (hcov : cov.IsMetricCompatible) {σ τ : Π y : M, V y} {U : Set M}
    (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hσ : MDiff[U] (T% σ)) (hτ : MDiff[U] (T% τ))
    (hσ0 : ∀ y ∈ U, cov σ y = 0) (hτ0 : ∀ y ∈ U, cov τ y = 0)
    {x y : M} (hx : x ∈ U) (hy : y ∈ U) :
    inner ℝ (σ x) (τ x) = inner ℝ (σ y) (τ y) := by
  let Uo : TopologicalSpace.Opens M := ⟨U, hU⟩
  have : PreconnectedSpace Uo := isPreconnected_iff_preconnectedSpace.mp hUconn
  let φ : Uo → ℝ := fun z ↦ inner ℝ (σ z.1) (τ z.1)
  have hloc : IsLocallyConstant φ :=
    (IsLocallyConstant.iff_eventually_eq φ).mpr fun z ↦ by
      have hev := hcov.eventuallyEq_inner_const_of_cov_eq_zero hU hσ hτ hσ0 hτ0 z.2
      exact continuous_subtype_val.continuousAt.eventually hev
  exact hloc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

variable {n : ℕ∞ω} [ContMDiffCovariantDerivative cov n]

/-- The twice-differentiated metric product rule for a `C^n` metric-compatible connection. -/
theorem IsMetricCompatible.mvfderiv_mvfderiv_inner
    (hcov : cov.IsMetricCompatible)
    {X Y : Π x : M, TangentSpace I x} {σ τ : Π x : M, V x}
    (hn : 1 ≤ n) (hY : CMDiff n (T% Y))
    (hσ : CMDiff (n + 1) (T% σ)) (hτ : CMDiff (n + 1) (T% τ))
    (x : M) :
    mvfderiv I (fun y ↦ mvfderiv I (fun z ↦ inner ℝ (σ z) (τ z)) y (Y y)) x (X x) =
      inner ℝ (cov (fun y ↦ cov σ y (Y y)) x (X x)) (τ x) +
      inner ℝ (cov σ x (Y x)) (cov τ x (X x)) +
      (inner ℝ (cov σ x (X x)) (cov τ x (Y x)) +
      inner ℝ (σ x) (cov (fun y ↦ cov τ y (Y y)) x (X x))) := by
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) hn)
  have hYσ := cov.contMDiff_apply hY hσ
  have hYτ := cov.contMDiff_apply hY hτ
  have hmetric : (fun y ↦ mvfderiv I (fun z ↦ inner ℝ (σ z) (τ z)) y (Y y)) =
      fun y ↦ inner ℝ (cov σ y (Y y)) (τ y) + inner ℝ (σ y) (cov τ y (Y y)) := by
    funext y
    exact hcov.mvfderiv_inner_eq Y (hσ.mdifferentiable (by simp) y)
      (hτ.mdifferentiable (by simp) y)
  rw [hmetric, mvfderiv_fun_add
    (((hYσ.mdifferentiable hn0).inner_bundle (hτ.mdifferentiable (by simp))) x)
    (((hσ.mdifferentiable (by simp)).inner_bundle (hYτ.mdifferentiable hn0)) x)]
  simp only [add_apply]
  rw [hcov.mvfderiv_inner_eq X (hYσ.mdifferentiable hn0 x)
      (hτ.mdifferentiable (by simp) x),
    hcov.mvfderiv_inner_eq X (hσ.mdifferentiable (by simp) x)
      (hYτ.mdifferentiable hn0 x)]

section Torsion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

/-- For a metric-compatible torsion-free connection, the Lie derivative of the metric along `X`
is `(𝓛_X g)(Y, Z) = ⟪∇_Y X, Z⟫ + ⟪Y, ∇_Z X⟫`. -/
theorem IsMetricCompatible.mvfderiv_inner_sub_inner_mlieBracket
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    mvfderiv I (fun y ↦ inner ℝ (Y y) (Z y)) x (X x) -
        inner ℝ (mlieBracket I X Y x) (Z x) - inner ℝ (Y x) (mlieBracket I X Z x) =
      inner ℝ (cov X x (Y x)) (Z x) + inner ℝ (Y x) (cov X x (Z x)) := by
  have hmetric := hcov.mvfderiv_inner_eq X hY hZ
  beta_reduce at hmetric
  rw [hmetric, ← (torsion_eq_zero_iff cov).1 ht hX hY, ← (torsion_eq_zero_iff cov).1 ht hX hZ,
    inner_sub_left, inner_sub_right]
  ring

end Torsion

end CovariantDerivative

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] {n : ℕ∞ω}

/-- Metric compatibility with a `C¹` bundled metric `g`, installed as the `RiemannianBundle`
instance, written with the inner products of `g`. -/
theorem isMetricCompatible_iff_inner (g : ContMDiffRiemannianMetric I n F V) (hn : 1 ≤ n)
    (cov : CovariantDerivative I F V) :
    (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn;
      cov.IsMetricCompatible) ↔
      ∀ ⦃x : M⦄ ⦃X : Π x : M, TangentSpace I x⦄ ⦃σ τ : Π x : M, V x⦄,
        MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        mvfderiv I (fun y ↦ g.inner y (σ y) (τ y)) x (X x) =
          g.inner x (cov σ x (X x)) (τ x) + g.inner x (σ x) (cov τ x (X x)) := by
  let _ : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 F V := IsContMDiffRiemannianBundle.of_le hn
  simp only [CovariantDerivative.isMetricCompatible_iff, inner_riemannianBundle]

end Bundle.ContMDiffRiemannianMetric
