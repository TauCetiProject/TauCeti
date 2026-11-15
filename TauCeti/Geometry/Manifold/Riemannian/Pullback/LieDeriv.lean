/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Flow
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Killing.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Lie derivatives of Riemannian metrics, Killing fields, and the gradient–Hessian identity

This file connects the general pullback `TauCeti.mpullbackBilin` and chart-defined Lie derivative
`TauCeti.mlieDerivBilin` on covariant two-tensors with Riemannian metrics, metric-compatible
torsion-free connections, Killing vector fields, and the scalar Hessian:

* **Pullback bridge** (`Bundle.ContMDiffRiemannianMetric.pullback_inner_eq_mpullbackBilin`): the
  inner product of the pullback Riemannian metric `g.pullback f hf hinj` along an immersion is
  `TauCeti.mpullbackBilin I J f g.inner`, making all isotopy and flow pullback-variation theorems in
  `TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Flow` apply directly to evolving Riemannian
  metrics.
* **Connection and Levi-Civita formulas**
  (`CovariantDerivative.IsMetricCompatible.mlieDerivBilin_inner_apply`,
  `TauCeti.Manifold.mlieDerivBilin_inner_eq_leviCivitaConnection`): for a metric-compatible
  torsion-free connection `∇` (in particular the Levi-Civita connection) and a vector field `X`
  differentiable at `x`,
  `mlieDerivBilin I X RiemannianBundle.g.inner x u v = ⟪∇_u X, v⟫ + ⟪u, ∇_v X⟫`.
* **Killing vector fields and local-flow isometry**
  (`TauCeti.Manifold.isKillingField_iff_mlieDerivBilin_eq_zero`,
  `TauCeti.Manifold.IsKillingField.mpullbackBilin_flowOf_inner_eq`): a smooth vector field is
  Killing if and only if `mlieDerivBilin I X RiemannianBundle.g.inner = 0`, and its maximal flow
  preserves the Riemannian metric wherever defined.
* **Gradient–Hessian identity** (`TauCeti.Manifold.mlieDerivBilin_mgradient_inner_apply`): for a
  function `f` that is `C²` at `x`, `L_{grad f} g = 2 Hess f` at `x`.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), Proposition 2.1.3 and
  Chapter 8 (Lie derivative of the metric, gradient–Hessian formula, and Killing fields).
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS Mathematical Surveys and Monographs
  110 (2004), Lemma 1.10 (diffeomorphism-modified metric evolution and gradient solitons).
-/

public section

noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N] {n : ℕ∞ω}

/-- The inner-product field of the pullback Riemannian metric `g.pullback f hf hinj` agrees with
`TauCeti.mpullbackBilin I J f g.inner`. -/
theorem pullback_inner_eq_mpullbackBilin
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) (f : M → N)
    (hf : ContMDiff I J (n + 1) f) (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    (g.pullback f hf hinj).inner = TauCeti.mpullbackBilin I J f g.inner := by
  funext x; ext v w; rw [pullback_inner, TauCeti.mpullbackBilin_apply]

end Bundle.ContMDiffRiemannianMetric

private theorem mdifferentiable_riemannianBundle_inner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] :
    MDifferentiable I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ)
        y (RiemannianBundle.g.inner y)) := by
  have heq : (fun y : M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ)
        y (RiemannianBundle.g.inner y)) =
      fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) y
        ((Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
          (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)).inner y) := by
    funext y
    refine congrArg (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) y) ?_
    ext u v
    exact (Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner y u v).symm
  rw [heq]
  exact (Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)).contMDiff.mdifferentiable
    one_ne_zero

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

/-- **Covariant-derivative formula for the Lie derivative of a Riemannian metric.** For a
metric-compatible torsion-free connection `∇` and a vector field `X` differentiable at `x`,
`(L_X g)_x (u, v) = ⟪∇_u X, v⟫ + ⟪u, ∇_v X⟫`. -/
theorem IsMetricCompatible.mlieDerivBilin_inner_apply
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) {X : (x : M) → TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (u v : TangentSpace I x) :
    TauCeti.mlieDerivBilin I X RiemannianBundle.g.inner x u v =
      inner ℝ (cov X x u) v + inner ℝ u (cov X x v) := by
  let _ : IsManifold I 1 M := IsManifold.of_le one_le_two
  let Y : (y : M) → TangentSpace I y := FiberBundle.extend E u
  let Z : (y : M) → TangentSpace I y := FiberBundle.extend E v
  have hY : MDiffAt (T% Y) x := FiberBundle.mdifferentiableAt_extend I E u
  have hZ : MDiffAt (T% Z) x := FiberBundle.mdifferentiableAt_extend I E v
  have hLie := TauCeti.mlieDerivBilin_apply_vectorField (V := X)
    (mdifferentiable_riemannianBundle_inner x) hY hZ
  have hcovLie := hcov.mvfderiv_inner_sub_inner_mlieBracket ht hX hY hZ
  dsimp only [Y, Z] at hLie hcovLie
  rw [FiberBundle.extend_apply_self, FiberBundle.extend_apply_self] at hLie hcovLie
  exact hLie.trans hcovLie

end CovariantDerivative

namespace TauCeti.Manifold

section LeviCivita

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **Levi-Civita formula for the Lie derivative of the metric:**
`(L_X g)_x (u, v) = ⟪∇_u X, v⟫ + ⟪u, ∇_v X⟫`, where `∇` is the Levi-Civita connection. -/
theorem mlieDerivBilin_inner_eq_leviCivitaConnection
    {X : (x : M) → TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (u v : TangentSpace I x) :
    mlieDerivBilin I X RiemannianBundle.g.inner x u v =
      inner ℝ (CovariantDerivative.leviCivitaConnection I M X x u) v +
        inner ℝ u (CovariantDerivative.leviCivitaConnection I M X x v) :=
  (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).mlieDerivBilin_inner_apply
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) hX u v

/-- **Gradient–Hessian identity:** for a function `f : M → ℝ` that is `C²` at `x`, the Lie
derivative of the Riemannian metric along `mgradient I f` is twice the Hessian:
`(L_{grad f} g)_x (u, v) = 2 Hess f_x (u, v)`. -/
theorem mlieDerivBilin_mgradient_inner_apply
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (u v : TangentSpace I x) :
    mlieDerivBilin I (mgradient I f) RiemannianBundle.g.inner x u v =
      2 * hessian I f x u v := by
  let _ : IsManifold I (1 + 1) M := by simpa only [one_add_one_eq_two] using ‹IsManifold I 2 M›
  have hgrad : MDiffAt (T% (mgradient I f)) x :=
    (contMDiffAt_mgradient (I := I) (f := f) (x := x) (n := 1)
      (by simpa only [one_add_one_eq_two] using hf)).mdifferentiableAt one_ne_zero
  rw [mlieDerivBilin_inner_eq_leviCivitaConnection hgrad, real_inner_comm _ u,
    ← hessian_def, ← hessian_def, hessian_symm x hf v u, two_mul]

end LeviCivita

section Killing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {X : (x : M) → TangentSpace I x}

/-- **Characterization of Killing fields via `mlieDerivBilin`:** a vector field `X` is Killing if
and only if it is smooth and `mlieDerivBilin I X RiemannianBundle.g.inner = 0`. -/
theorem isKillingField_iff_mlieDerivBilin_eq_zero :
    IsKillingField I X ↔ CMDiff ∞ (T% X) ∧ mlieDerivBilin I X RiemannianBundle.g.inner = 0 := by
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  rw [(CovariantDerivative.isMetricCompatible_leviCivitaConnection I).isKillingField_iff
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)]
  refine and_congr_right fun hX ↦ ⟨fun h ↦ ?_, fun h x u v ↦ ?_⟩
  · funext x
    ext u v
    rw [Pi.zero_apply, zero_apply, zero_apply,
      mlieDerivBilin_inner_eq_leviCivitaConnection (hX.mdifferentiable (by simp) x), h x u v,
      neg_add_cancel]
  · have h0 : mlieDerivBilin I X RiemannianBundle.g.inner x u v = 0 := by rw [h]; rfl
    rw [mlieDerivBilin_inner_eq_leviCivitaConnection (hX.mdifferentiable (by simp) x)] at h0
    exact eq_neg_of_add_eq_zero_left h0

/-- The Lie derivative `mlieDerivBilin` of the Riemannian metric along a Killing field vanishes. -/
theorem IsKillingField.mlieDerivBilin_inner_eq_zero (h : IsKillingField I X) :
    mlieDerivBilin I X RiemannianBundle.g.inner = 0 :=
  (isKillingField_iff_mlieDerivBilin_eq_zero.1 h).2

/-- **Local flows of Killing fields act by local isometries:** on a boundaryless manifold, wherever
`(t, x) ∈ flowDomain X`, the maximal flow `flowOf X t` pulls the Riemannian metric at `flowOf X t x`
back to the Riemannian metric at `x`. -/
theorem IsKillingField.mpullbackBilin_flowOf_inner_eq [I.Boundaryless]
    (h : IsKillingField I X) {t : ℝ} {x : M} (hx : (t, x) ∈ flowDomain X) :
    mpullbackBilin I I (flowOf X t) RiemannianBundle.g.inner x = RiemannianBundle.g.inner x := by
  let _ : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  let _ : IsManifold I 1 M := IsManifold.of_le one_le_two
  exact mpullbackBilin_flowOf_apply_eq_of_mlieDerivBilin_eq_zero
    (h.contMDiff.of_le (by simp)) mdifferentiable_riemannianBundle_inner
    h.mlieDerivBilin_inner_eq_zero hx

end Killing

end TauCeti.Manifold
