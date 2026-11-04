/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Immersion
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorField.Regularity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Gauss formula along a curve

For an isometric immersion into a real inner product space, covariant differentiation of a
tangent field along a curve is the tangential part of its ambient derivative. This extends the
vector-field Gauss formula to fields defined only along the curve, including its velocity.
It allows geodesic equations on submanifolds to be checked in ambient coordinates.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 8,
  the Gauss formula and induced covariant differentiation along curves.
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative.IsLeviCivitaConnection

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The Gauss formula for a tangent field along a curve: the covariant derivative pairs
with each tangent vector as does the ordinary derivative of the field's ambient image.
The ambient derivative is supplied as a `HasDerivAt` statement. -/
theorem inner_alongCurve_eq_inner (hcov : cov.IsLeviCivitaConnection)
    {f : M → F} {γ : ℝ → M} {V : ∀ r, TangentSpace I (γ r)} {t : ℝ} {a : F}
    (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f (γ t))
    (hg : ∀ x (v w : TangentSpace I x),
      inner ℝ v w = inner ℝ (mvfderiv I f x v) (mvfderiv I f x w))
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (ha : HasDerivAt (fun r ↦ mvfderiv I f (γ r) (V r)) a t)
    (w : TangentSpace I (γ t)) :
    inner ℝ (alongCurve cov γ V t) w = inner ℝ a (mvfderiv I f (γ t) w) := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  let Z := extend E w
  have hZ : MDiffAt (T% Z) (γ t) := mdifferentiableAt_extend I E w
  have hZcoord : DifferentiableAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ Z (γ r)) (γ t)) t :=
    differentiableAt_sectionCoord γ _ (hZ.comp t hγ)
      (mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hsource := hcov.isMetricCompatible.hasDerivAt_inner_alongCurve hγ hV hZcoord
  have htarget := ha.inner ℝ (hasDerivAt_comp_curve
    (TauCeti.mdifferentiableAt_mvfderiv_apply hf (by simp) hZ)
    (hasMFDerivAt_curveVelocity hγ))
  have hpair : (fun r ↦ inner ℝ (V r) (Z (γ r))) =
      fun r ↦ inner ℝ (mvfderiv I f (γ r) (V r)) (mvfderiv I f (γ r) (Z (γ r))) :=
    funext fun r ↦ hg _ _ _
  have hderiv := hsource.unique (hpair ▸ htarget)
  let X := extend E (curveVelocity I γ t)
  have hX : MDiffAt (T% X) (γ t) := mdifferentiableAt_extend I E _
  have hXv : X (γ t) = curveVelocity I γ t := by simp [X]
  have hgauss := hcov.inner_apply_eq_inner_mvfderiv hf hg
    hX hZ (V t)
  rw [hXv, real_inner_comm (V t),
    real_inner_comm (mvfderiv I f (γ t) (V t))] at hgauss
  rw [alongCurve_pullback cov γ _ (hasMFDerivAt_curveVelocity hγ) hZ] at hderiv
  simp only [Function.comp_apply] at hderiv
  have hw : Z (γ t) = w := by simp [Z]
  rw [hw] at hderiv
  linarith [hgauss]

end CovariantDerivative.IsLeviCivitaConnection
