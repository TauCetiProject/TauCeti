/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Schur
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Parallel curvature and local symmetry

In this file a connection `∇` on the tangent bundle *has parallel curvature* when its curvature
tensor is parallel, `∇R = 0`, where `∇R` is `CovariantDerivative.derivCurvatureTensor` taken with
`∇` itself. No condition on the torsion is imposed. The classical notion of an affine locally
symmetric connection is a torsion-free connection with parallel curvature (Kobayashi–Nomizu,
Vol. II, Chapter XI). For the Levi-Civita connection, `∇R = 0` is equivalent to the Riemannian
manifold being locally symmetric (Cartan's characterization); it is not the geodesic-symmetry
definition itself.

Flat connections have parallel curvature. For a metric-compatible connection whose curvature has the
pointwise constant-curvature form `R(w, u)v = κ(y) (⟨u, v⟩ w - ⟨w, v⟩ u)`, the covariant derivative
of the curvature is `(∇_v R)(u, w)s = dκ(v) (⟨w, s⟩ u - ⟨u, s⟩ w)`. In particular a
metric-compatible torsion-free connection of constant sectional curvature, such as the Levi-Civita
connection of a round sphere or of hyperbolic space, has parallel curvature, so it is locally
symmetric.

## Main definitions and results

* `CovariantDerivative.HasParallelCurvature`: the curvature tensor of a connection on the tangent
  bundle is parallel.
* `CovariantDerivative.hasParallelCurvature_iff_curvatureOperator`: parallel curvature as the
  product rule `∇_X (R(Y, Z) W) = R(∇_X Y, Z) W + R(Y, ∇_X Z) W + R(Y, Z) (∇_X W)` on smooth
  fields.
* `CovariantDerivative.hasParallelCurvature_of_curvatureTensor_eq_zero`: flat connections have
  parallel curvature.
* `CovariantDerivative.IsMetricCompatible.derivCurvatureTensor_eq_mvfderiv_smul`: the covariant
  derivative of a curvature tensor of pointwise constant-curvature form.
* `CovariantDerivative.HasConstantSectionalCurvature.hasParallelCurvature`: constant sectional
  curvature implies parallel curvature.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7
  (locally symmetric spaces, as manifolds with parallel curvature tensor).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience
  (1963), Chapter V, Section 2 (sectional curvature and spaces of constant curvature).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Interscience
  (1969), Chapter XI (affine locally symmetric spaces, as torsion-free connections with parallel
  curvature tensor).
-/

public section

open Bundle FiberBundle
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

section Affine

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

/-- A smooth connection on the tangent bundle **has parallel curvature** when the covariant
derivative `∇R` of its curvature tensor, taken with the connection itself, vanishes at every
point. The torsion is unrestricted; a torsion-free connection with parallel curvature is an affine
locally symmetric connection. For the Levi-Civita connection the condition is equivalent to local
symmetry of the Riemannian manifold. -/
def HasParallelCurvature : Prop :=
  ∀ x : M, cov.derivCurvatureTensor cov x = 0

/-- The pointwise characterization of parallel curvature. -/
theorem hasParallelCurvature_iff :
    cov.HasParallelCurvature ↔ ∀ x : M, cov.derivCurvatureTensor cov x = 0 :=
  Iff.rfl

/-- A connection on the tangent bundle has parallel curvature exactly when its curvature operator
satisfies the product rule
`∇_X (R(Y, Z) W) = R(∇_X Y, Z) W + R(Y, ∇_X Z) W + R(Y, Z) (∇_X W)` on smooth vector fields. -/
theorem hasParallelCurvature_iff_curvatureOperator :
    cov.HasParallelCurvature ↔
      ∀ ⦃X Y Z W : Π x : M, TangentSpace I x⦄, CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) →
        CMDiff ∞ (T% Z) → CMDiff ∞ (T% W) → ∀ x : M,
          cov (curvatureOperator cov Y Z W) x (X x) =
            curvatureOperator cov (fun y ↦ cov Y y (X y)) Z W x +
              curvatureOperator cov Y (fun y ↦ cov Z y (X y)) W x +
                curvatureOperator cov Y Z (fun y ↦ cov W y (X y)) x := by
  refine ⟨fun h X Y Z W hX hY hZ hW x ↦ ?_, fun h x ↦ ?_⟩
  · have hx := congr($(h x) (X x) (Y x) (Z x) (W x))
    rw [derivCurvatureTensor_apply_eq_curvatureOperator cov cov x hX hY hZ hW] at hx
    simp only [LinearMap.zero_apply] at hx
    rw [← sub_eq_zero, ← hx]
    abel
  · ext v u w s
    obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E v
    obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E u
    obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
    obtain ⟨W, hW, rfl⟩ := exists_contMDiff_section_eq I E s
    rw [derivCurvatureTensor_apply_eq_curvatureOperator cov cov x hX hY hZ hW,
      h hX hY hZ hW x]
    simp only [LinearMap.zero_apply, sub_sub, sub_self]

/-- A flat connection on the tangent bundle has parallel curvature. -/
theorem hasParallelCurvature_of_curvatureTensor_eq_zero (h : ∀ x : M, cov.curvatureTensor x = 0) :
    cov.HasParallelCurvature :=
  derivCurvatureTensor_eq_zero_of_curvatureTensor_eq_zero cov cov h

end Affine

section Riemannian

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

/-- Let the curvature tensor of a metric-compatible connection have the pointwise
constant-curvature form `R(w, u)v = κ(y) (⟨u, v⟩ w - ⟨w, v⟩ u)` at every point `y`. At a point
where `κ` is differentiable, the covariant derivative of the curvature is
`(∇_v R)(u, w)s = dκ(v) (⟨w, s⟩ u - ⟨u, s⟩ w)`. -/
theorem IsMetricCompatible.derivCurvatureTensor_eq_mvfderiv_smul
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {κ : M → ℝ} (hκ : ∀ (y : M) (w u v : TangentSpace I y),
      cov.curvatureTensor y w u v = κ y • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u))
    {x : M} (hκx : MDifferentiableAt I 𝓘(ℝ) κ x) (v u w s : TangentSpace I x) :
    cov.derivCurvatureTensor cov x v u w s = mvfderiv I κ x v • (⟪w, s⟫_ℝ • u - ⟪u, s⟫_ℝ • w) := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
  obtain ⟨W, hW, rfl⟩ := exists_contMDiff_section_eq I E s
  rw [derivCurvatureTensor_apply_eq_curvatureOperator cov cov x hX hY hZ hW]
  exact hcov.covariantDerivative_curvatureOperator_eq_mvfderiv_smul hκ hX hY hZ hW hκx

/-- A metric-compatible torsion-free connection of constant sectional curvature, such as the
Levi-Civita connection of a space form, has parallel curvature. -/
theorem HasConstantSectionalCurvature.hasParallelCurvature
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov}
    {κ : ℝ} (h : cov.HasConstantSectionalCurvature hcov κ) (ht : cov.torsion = 0) :
    cov.HasParallelCurvature := by
  intro x
  ext v u w s
  rw [hcov.derivCurvatureTensor_eq_mvfderiv_smul (κ := fun _ ↦ κ)
    (fun y ↦ (h.hasSectionalCurvatureAt y).curvatureTensor_eq_smul_inner_sub ht)
    mdifferentiableAt_const]
  simp [mvfderiv_const]

end Riemannian

end CovariantDerivative
