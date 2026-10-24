/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Schouten
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The Cotton tensor of a smooth connection

On a Riemannian manifold, the Cotton tensor is the antisymmetrized covariant derivative of the
Schouten tensor `P`:

`C(X, Y, Z) = (∇_Z P)(X, Y) - (∇_Y P)(X, Z)`.

It measures the failure of `P` to satisfy the Codazzi equation. Classically, in dimension `3`,
where the Weyl tensor vanishes identically, the Cotton tensor is the obstruction to local conformal
flatness, and in higher dimensions it is a multiple of the divergence of the Weyl tensor; this file
develops the definition and its first properties, not these characterizations.

The covariant derivative `∇P` is the covariant derivative of a field of bilinear forms,
`CovariantDerivative.derivBilinearTensor`, applied to the Schouten tensor. As for
`CovariantDerivative.schoutenTensor`, the definitions are made for any smooth connection on a
Riemannian tangent bundle, and the same connection differentiates `P`. For a smooth metric, `P`
pairs differentiable vector fields to differentiable functions, so `∇P` and `C` are given on
vector fields by the usual formulas (`CovariantDerivative.derivSchoutenTensor_apply` and
`CovariantDerivative.cottonTensor_apply_of_mdifferentiableAt`).

The Cotton tensor is antisymmetric in its last two arguments by definition. For a
metric-compatible torsion-free connection, `P` is symmetric, hence so is `∇P` in its first two
arguments, and the cyclic sum of the Cotton tensor vanishes. If `P` is a constant multiple of the
metric, metric compatibility gives `∇P = 0`, so the Cotton tensor vanishes; in particular it
vanishes on every space of constant sectional curvature of dimension at least `3`.

## Main declarations

* `CovariantDerivative.derivSchoutenTensor`: the covariant derivative `∇P` of the Schouten tensor,
  with `CovariantDerivative.derivSchoutenTensor_apply` its value on differentiable vector fields.
* `CovariantDerivative.cottonTensor`: the Cotton tensor, with
  `CovariantDerivative.cottonTensor_apply_of_mdifferentiableAt` its value on differentiable
  vector fields.
* `CovariantDerivative.cottonTensor_antisymm_last`: `C(X, Y, Z) = -C(X, Z, Y)`.
* `CovariantDerivative.IsMetricCompatible.cottonTensor_cyclic_eq_zero`: the cyclic sum
  `C(X, Y, Z) + C(Y, Z, X) + C(Z, X, Y)` vanishes for a metric-compatible torsion-free
  connection.
* `CovariantDerivative.IsMetricCompatible.cottonTensor_eq_zero_of_schoutenTensor_eq_smul_inner`:
  the Cotton tensor vanishes when `P` is a constant multiple of the metric.
* `IsMetricCompatible.cottonTensor_eq_zero_of_curvatureTensor_eq_smul_inner_sub`, in the
  `CovariantDerivative` namespace: the Cotton tensor vanishes in constant curvature, in dimension
  at least `3`.

## References

* É. Cotton, *Sur les variétés à trois dimensions*, Ann. Fac. Sci. Toulouse (2) 1 (1899),
  385–438.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7
  (the Schouten, Weyl and Cotton tensors).
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- The covariant derivative `∇P` of the Schouten tensor `P` of a smooth connection, evaluated as
`cov.derivSchoutenTensor x u v w = (∇_w P)(u, v)`. This formula holds for a smooth metric
(`IsContMDiffRiemannianBundle I ∞`, see `CovariantDerivative.derivSchoutenTensor_apply`); as for
`CovariantDerivative.derivBilinearTensor`, the value is `0` when `P` does not pair differentiable
vector fields to differentiable functions. -/
def derivSchoutenTensor (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  cov.derivBilinearTensor (fun y ↦ (cov.schoutenTensor y).toContinuousBilinearMap) x

/-- `∇P` is the covariant derivative of the Schouten tensor as a field of bilinear forms, so the
`CovariantDerivative.derivBilinearTensor` API applies to it. -/
theorem derivSchoutenTensor_def (x : M) :
    cov.derivSchoutenTensor x =
      cov.derivBilinearTensor (fun y ↦ (cov.schoutenTensor y).toContinuousBilinearMap) x :=
  (rfl)

/-- The Cotton tensor `C(u, v, w) = (∇_w P)(u, v) - (∇_v P)(u, w)` of a smooth connection, where
`P` is the Schouten tensor and `∇P` is `CovariantDerivative.derivSchoutenTensor`. The usual
formula on vector fields holds for a smooth metric (see
`CovariantDerivative.cottonTensor_apply_of_mdifferentiableAt`); otherwise `∇P`, and hence the
Cotton tensor, may be `0`. -/
def cottonTensor (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ (cov.derivSchoutenTensor x u v).toLinearMap -
      (ContinuousLinearMap.toLinearMap₁₂ (cov.derivSchoutenTensor x u)).flip v)
    (fun u u' v ↦ by ext w; simp; ring)
    (fun c u v ↦ by ext w; simp; ring)
    (fun u v v' ↦ by ext w; simp; ring)
    (fun c u v ↦ by ext w; simp; ring)

/-- Evaluation of the Cotton tensor: `C(u, v, w) = (∇_w P)(u, v) - (∇_v P)(u, w)`. -/
@[simp]
theorem cottonTensor_apply (x : M) (u v w : TangentSpace I x) :
    cov.cottonTensor x u v w =
      cov.derivSchoutenTensor x u v w - cov.derivSchoutenTensor x u w v :=
  (rfl)

/-- The Cotton tensor is antisymmetric in its last two arguments. -/
theorem cottonTensor_antisymm_last (x : M) (u v w : TangentSpace I x) :
    cov.cottonTensor x u v w = -cov.cottonTensor x u w v := by
  simp only [cottonTensor_apply, neg_sub]

section Smooth

variable [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

/-- The covariant derivative of the Schouten tensor on vector fields differentiable at `x`:
`(∇_v P)(σ, τ) = v (P(σ, τ)) - P(∇_v σ, τ) - P(σ, ∇_v τ)`. -/
theorem derivSchoutenTensor_apply {σ τ : Π x : M, TangentSpace I x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) (v : TangentSpace I x) :
    cov.derivSchoutenTensor x (σ x) (τ x) v =
      mvfderiv I (fun y ↦ cov.schoutenTensor y (σ y) (τ y)) x v -
        cov.schoutenTensor x (cov σ x v) (τ x) - cov.schoutenTensor x (σ x) (cov τ x v) := by
  have hb : ∀ ⦃σ τ : Π x : M, TangentSpace I x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ (cov.schoutenTensor y).toContinuousBilinearMap (σ y) (τ y)) x :=
    fun σ τ hσ hτ ↦ by
      simpa only [LinearMap.toContinuousBilinearMap_apply] using
        cov.mdifferentiableAt_schoutenTensor_apply hσ hτ
  rw [derivSchoutenTensor, cov.derivBilinearTensor_apply hb hσ hτ]
  simp only [LinearMap.toContinuousBilinearMap_apply]

/-- The Cotton tensor on vector fields differentiable at `x`:
`C(σ, τ, ρ) = ρ (P(σ, τ)) - τ (P(σ, ρ)) - P(∇_ρ σ, τ) - P(σ, ∇_ρ τ) + P(∇_τ σ, ρ) + P(σ, ∇_τ ρ)`.
-/
theorem cottonTensor_apply_of_mdifferentiableAt {σ τ ρ : Π x : M, TangentSpace I x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) (hρ : MDiffAt (T% ρ) x) :
    cov.cottonTensor x (σ x) (τ x) (ρ x) =
      mvfderiv I (fun y ↦ cov.schoutenTensor y (σ y) (τ y)) x (ρ x) -
        mvfderiv I (fun y ↦ cov.schoutenTensor y (σ y) (ρ y)) x (τ x) -
        cov.schoutenTensor x (cov σ x (ρ x)) (τ x) - cov.schoutenTensor x (σ x) (cov τ x (ρ x)) +
        cov.schoutenTensor x (cov σ x (τ x)) (ρ x) +
        cov.schoutenTensor x (σ x) (cov ρ x (τ x)) := by
  rw [cottonTensor_apply, cov.derivSchoutenTensor_apply hσ hτ,
    cov.derivSchoutenTensor_apply hσ hρ]
  ring

end Smooth

section MetricCompatible

variable [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

/-- For a metric-compatible torsion-free connection, `∇P` is symmetric in its first two
arguments: `(∇_w P)(u, v) = (∇_w P)(v, u)`. -/
theorem IsMetricCompatible.derivSchoutenTensor_comm
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (u v : TangentSpace I x) :
    cov.derivSchoutenTensor x u v = cov.derivSchoutenTensor x v u :=
  cov.derivBilinearTensor_apply_comm (fun y a b ↦ by
    simpa only [LinearMap.toContinuousBilinearMap_apply, RingHom.id_apply] using
      (IsMetricCompatible.schoutenTensor_isSymm (cov := cov) hcov ht y).eq a b) u v

/-- For a metric-compatible torsion-free connection, the cyclic sum of the Cotton tensor
vanishes: `C(u, v, w) + C(v, w, u) + C(w, u, v) = 0`. -/
theorem IsMetricCompatible.cottonTensor_cyclic_eq_zero
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (u v w : TangentSpace I x) :
    cov.cottonTensor x u v w + cov.cottonTensor x v w u + cov.cottonTensor x w u v = 0 := by
  have h (a b c : TangentSpace I x) :
      cov.derivSchoutenTensor x a b c = cov.derivSchoutenTensor x b a c := by
    rw [IsMetricCompatible.derivSchoutenTensor_comm (cov := cov) hcov ht x a b]
  simp only [cottonTensor_apply, h v u, h w v, h u w]
  ring

/-- For a metric-compatible connection whose Schouten tensor is a constant multiple `c g` of the
metric, the covariant derivative of the Schouten tensor vanishes. -/
theorem IsMetricCompatible.derivSchoutenTensor_eq_zero_of_schoutenTensor_eq_smul_inner
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (c : ℝ)
    (h : ∀ y, cov.schoutenTensor y = c • innerₗ (TangentSpace I y)) (x : M) :
    cov.derivSchoutenTensor x = 0 :=
  hcov.derivBilinearTensor_eq_zero_of_eq_mul_inner c (fun y v w ↦ by simp [h y]) x

/-- For a metric-compatible connection whose Schouten tensor is a constant multiple `c g` of the
metric, the Cotton tensor vanishes. -/
theorem IsMetricCompatible.cottonTensor_eq_zero_of_schoutenTensor_eq_smul_inner
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (c : ℝ)
    (h : ∀ y, cov.schoutenTensor y = c • innerₗ (TangentSpace I y)) (x : M) :
    cov.cottonTensor x = 0 := by
  ext u v w
  simp [IsMetricCompatible.derivSchoutenTensor_eq_zero_of_schoutenTensor_eq_smul_inner
    (cov := cov) hcov c h x]

/-- A metric-compatible connection of constant curvature `R(w,u)v = κ (⟨u,v⟩ w - ⟨w,v⟩ u)`, with
`κ` the same at every point, has vanishing Cotton tensor in dimension at least `3`. -/
theorem IsMetricCompatible.cottonTensor_eq_zero_of_curvatureTensor_eq_smul_inner_sub
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (k : ℝ) (hn : 3 ≤ Module.finrank ℝ E)
    (h : ∀ y w u v, curvature y w u v = k • (inner ℝ u v • w - inner ℝ w v • u)) (x : M) :
    cov.cottonTensor x = 0 :=
  IsMetricCompatible.cottonTensor_eq_zero_of_schoutenTensor_eq_smul_inner (cov := cov) hcov
    (k / 2) (fun y ↦ cov.schoutenTensor_eq_of_curvatureTensor_eq_smul_inner_sub y k
      (by rwa [TauCeti.finrank_tangentSpace]) (h y)) x

end MetricCompatible

end CovariantDerivative
