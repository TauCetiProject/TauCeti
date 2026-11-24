/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.LieDeriv
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Lie derivatives of Riemannian metrics and the gradient–Hessian identity

Connects `TauCeti.mpullbackBilin` and `TauCeti.mlieDerivBilin` with Riemannian metrics,
metric-compatible torsion-free connections, and the scalar Hessian
(`pullback_inner_eq_mpullbackBilin`, `IsMetricCompatible.mlieDerivBilin_inner_apply`,
`mlieDerivBilin_inner_eq_leviCivitaConnection`, `mlieDerivBilin_mgradient_inner_apply`).

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed. (2016), Proposition 2.1.3.
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS (2004), Lemma 1.10.
-/

public section

noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace Bundle.ContMDiffRiemannianMetric

variable [FiniteDimensional ℝ E] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N] {n : ℕ∞ω}

/-- The inner-product field of `g.pullback f hf hinj` agrees with `mpullbackBilin I J f g.inner`. -/
theorem pullback_inner_eq_mpullbackBilin
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) (f : M → N)
    (hf : ContMDiff I J (n + 1) f) (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    (g.pullback f hf hinj).inner = TauCeti.mpullbackBilin I J f g.inner := by
  funext x; ext v w; rw [pullback_inner, TauCeti.mpullbackBilin_apply]

end Bundle.ContMDiffRiemannianMetric

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ E]

namespace CovariantDerivative

variable [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

/-- **Covariant-derivative formula for the Lie derivative of a Riemannian metric:** for a
metric-compatible torsion-free connection `∇`, `(L_X g)_x (u, v) = ⟪∇_u X, v⟫ + ⟪u, ∇_v X⟫`. -/
theorem IsMetricCompatible.mlieDerivBilin_inner_apply
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) {X : (x : M) → TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (u v : TangentSpace I x) :
    TauCeti.mlieDerivBilin I X RiemannianBundle.g.inner x u v =
      inner ℝ (cov X x u) v + inner ℝ u (cov X x v) := by
  let _ : IsManifold I 1 M := IsManifold.of_le one_le_two
  have hY : MDiffAt (T% (FiberBundle.extend E u)) x := FiberBundle.mdifferentiableAt_extend I E u
  have hZ : MDiffAt (T% (FiberBundle.extend E v)) x := FiberBundle.mdifferentiableAt_extend I E v
  have hLie := TauCeti.mlieDerivBilin_apply_vectorField (V := X)
    (Bundle.mdifferentiable_riemannianBundle_inner
      (IB := I) (F := E) (V := fun y : M ↦ TangentSpace I y) x) hY hZ
  have hcovLie := hcov.mvfderiv_inner_sub_inner_mlieBracket ht hX hY hZ
  rw [FiberBundle.extend_apply_self, FiberBundle.extend_apply_self] at hLie hcovLie
  exact hLie.trans hcovLie

end CovariantDerivative

namespace TauCeti.Manifold

section LeviCivita

variable [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **Levi-Civita formula for the Lie derivative of the metric:**
`(L_X g)_x (u, v) = ⟪∇_u X, v⟫ + ⟪u, ∇_v X⟫`, where `∇` is the Levi-Civita connection. -/
theorem mlieDerivBilin_inner_eq_leviCivitaConnection {X : (x : M) → TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (u v : TangentSpace I x) :
    mlieDerivBilin I X RiemannianBundle.g.inner x u v =
      inner ℝ (CovariantDerivative.leviCivitaConnection I M X x u) v +
        inner ℝ u (CovariantDerivative.leviCivitaConnection I M X x v) :=
  (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).mlieDerivBilin_inner_apply
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) hX u v

/-- **Gradient–Hessian identity:** `(L_{grad f} g)_x (u, v) = 2 Hess f_x (u, v)`. -/
theorem mlieDerivBilin_mgradient_inner_apply
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (u v : TangentSpace I x) :
    mlieDerivBilin I (mgradient I f) RiemannianBundle.g.inner x u v =
      2 * hessian I f x u v := by
  let _ : IsManifold I (1 + 1) M := by simpa only [one_add_one_eq_two] using ‹IsManifold I 2 M›
  have hgrad : MDiffAt (T% (mgradient I f)) x :=
    (contMDiffAt_mgradient (I := I) (f := f) (x := x) (n := 1)
      (by simpa only [one_add_one_eq_two] using hf)).mdifferentiableAt one_ne_zero
  rw [mlieDerivBilin_inner_eq_leviCivitaConnection hgrad, real_inner_comm _ u,
    ← I.hessian_eq_inner_leviCivitaConnection_mgradient,
    ← I.hessian_eq_inner_leviCivitaConnection_mgradient, hessian_symm x hf v u, two_mul]

/-- **Bundled gradient–Hessian identity:** `L_{grad f} g = 2 • Hess f` as continuous bilinear forms
on `T_x M`. -/
theorem mlieDerivBilin_mgradient_inner {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    mlieDerivBilin I (mgradient I f) RiemannianBundle.g.inner x = 2 • I.hessianForm f x := by
  ext u v
  simp [mlieDerivBilin_mgradient_inner_apply hf]

end LeviCivita

end TauCeti.Manifold
