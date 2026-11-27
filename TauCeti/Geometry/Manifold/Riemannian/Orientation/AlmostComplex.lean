/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Orientation.Rotation
public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic

/-!
# The almost complex structure of an oriented Riemannian surface

The positive right-angle rotation in each tangent plane defines a smooth almost complex
structure. This construction needs only smoothness of the metric and orientation.

Ported from Riccardo Brasca's `ForTauCeti` formalization.
-/

public section

noncomputable section

open Bundle TauCeti
open scoped Bundle ContDiff InnerProductSpace Manifold RealInnerProductSpace

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The smooth almost complex structure given by positive right-angle rotation. -/
def rightAngleAlmostComplexStructure (o : Manifold.Orientation I M (Fin 2)) :
    SmoothAlmostComplexStructure I M := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let A : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x := fun x ↦
    letI := o.fact_finrank_tangentSpace x
    (o.orientationAt x).rightAngleRotation.toContinuousLinearMap
  have hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) x (A x)) :=
    (Manifold.contMDiff_hom_iff A).2 fun s hs ↦ by
      convert o.contMDiff_rightAngleRotation hs using 1
      funext x
      rfl
  refine ⟨⟨A, hA⟩, fun x ↦ ?_⟩
  ext v
  let := o.fact_finrank_tangentSpace x
  exact (o.orientationAt x).rightAngleRotation_rightAngleRotation v

/-- The metric-induced complex structure acts by positive right-angle rotation. -/
@[simp]
theorem rightAngleAlmostComplexStructure_apply
    (o : Manifold.Orientation I M (Fin 2)) (x : M) (v : TangentSpace I x) :
    o.rightAngleAlmostComplexStructure x v =
      (letI := o.fact_finrank_tangentSpace x
       (o.orientationAt x).rightAngleRotation v) :=
  (rfl)

/-- The metric-induced complex structure is orthogonal in each tangent plane. -/
theorem inner_rightAngleAlmostComplexStructure
    (o : Manifold.Orientation I M (Fin 2)) (x : M) (v w : TangentSpace I x) :
    ⟪o.rightAngleAlmostComplexStructure x v,
      o.rightAngleAlmostComplexStructure x w⟫_ℝ = ⟪v, w⟫_ℝ := by
  let := o.fact_finrank_tangentSpace x
  simp only [rightAngleAlmostComplexStructure_apply]
  exact (o.orientationAt x).inner_comp_rightAngleRotation v w

end TauCeti.Manifold.Orientation
