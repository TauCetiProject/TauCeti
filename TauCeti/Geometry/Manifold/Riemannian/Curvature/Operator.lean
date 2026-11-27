/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ExteriorSquare
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Nonnegative curvature operator of a Riemannian metric

A smooth metric has nonnegative curvature operator at a point when its native Levi-Civita
curvature endomorphism has nonnegative quadratic form on all bivectors. The endomorphism is
symmetric, so this condition is equivalent to `LinearMap.IsPositive`. This pointwise predicate
lets geometric hypotheses be shared across arbitrary metric families.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Chapter 4.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle CovariantDerivative
open scoped ContDiff Manifold RealInnerProductSpace

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))

/-- A metric has nonnegative curvature operator at `x` if its Levi-Civita curvature endomorphism
has nonnegative quadratic form on every bivector at `x`. -/
def HasNonnegativeCurvatureOperatorAt (x : M) : Prop :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
  ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
    0 ≤ ⟪(leviCivitaConnection I M).curvatureEndomorphism
      (isMetricCompatible_leviCivitaConnection I) x z, z⟫

/-- Unfolding the metric-level nonnegative curvature-operator predicate exposes its quadratic
form condition on every bivector. -/
theorem hasNonnegativeCurvatureOperatorAt_iff (x : M) :
    g.HasNonnegativeCurvatureOperatorAt x ↔
      (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
        ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
          0 ≤ ⟪(leviCivitaConnection I M).curvatureEndomorphism
            (isMetricCompatible_leviCivitaConnection I) x z, z⟫) := by
  rfl

/-- The metric curvature condition is equivalent to positivity of its native Levi-Civita
curvature endomorphism, since that endomorphism is symmetric. -/
theorem hasNonnegativeCurvatureOperatorAt_iff_isPositive (x : M) :
    g.HasNonnegativeCurvatureOperatorAt x ↔
      (letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
        ((leviCivitaConnection I M).curvatureEndomorphism
          (isMetricCompatible_leviCivitaConnection I) x).IsPositive) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [LinearMap.isPositive_iff]
  exact ⟨fun h ↦ ⟨(leviCivitaConnection I M).isSymmetric_curvatureEndomorphism
      (isMetricCompatible_leviCivitaConnection I) (torsion_leviCivitaConnection_eq_zero I) x, h⟩,
    fun h ↦ h.2⟩

end Bundle.ContMDiffRiemannianMetric
