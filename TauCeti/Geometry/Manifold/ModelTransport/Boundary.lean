/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Changes of model keep the interior and the boundary

Let `Φ : H ≃ₜ H'` be a homeomorphism between two model spaces, with models with corners `I` on `H`
and `I'` on `H'`. A charted space `M` over `H` becomes a charted space over `H'` for the composite
charts `ChartedSpace.comp H' H M`, where `H` carries the single chart `Φ`. This is how a manifold
is moved from one model to an equivalent one, for instance by
`Diffeomorph.isManifold_chartedSpaceComp` in the smooth case.

When `Φ` preserves the interior points of the models, `Φ ⁻¹' I'.interior H' = I.interior H`, the
change of model keeps the interior points and the boundary points of `M`
(`Homeomorph.isInteriorPoint_chartedSpaceComp_iff`,
`Homeomorph.isBoundaryPoint_chartedSpaceComp_iff`), hence the manifold interior, the manifold
boundary and boundarylessness (`Homeomorph.interior_chartedSpaceComp`,
`Homeomorph.boundary_chartedSpaceComp`, `Homeomorph.boundarylessManifold_chartedSpaceComp_iff`).
This holds in particular when `Φ` is read in the model vector spaces as a homeomorphism
`L : E ≃ₜ E'`, that is `I' ∘ Φ = L ∘ I` (`Homeomorph.preimage_interior_of_comp_eq`): `L` carries
the range of `I` onto the range of `I'`, and so its interior onto the interior.
-/

public section

open Set Function ChartedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'}

namespace Homeomorph

variable (Φ : H ≃ₜ H')

/-- A homeomorphism of models which is read in the model vector spaces as a homeomorphism `L`,
`I' ∘ Φ = L ∘ I`, preserves the interior points of the models. -/
theorem preimage_interior_of_comp_eq (L : E ≃ₜ E') (hL : ∀ x, I' (Φ x) = L (I x)) :
    Φ ⁻¹' I'.interior H' = I.interior H := by
  have hrange : range I' = L '' range I := by
    rw [← range_comp, ← Φ.surjective.range_comp]
    exact congrArg range (funext hL)
  ext y
  simp only [mem_preimage, ModelWithCorners.interior, mem_ofPred_eq,
    ModelWithCorners.IsInteriorPoint, extChartAt_self_eq, hL, hrange, ← L.image_interior,
    L.injective.mem_set_image]

/-- A change of model which preserves the interior points of the models,
`Φ ⁻¹' I'.interior H' = I.interior H`, keeps the interior points: a point is interior for the
composite charts exactly when it is interior for the original ones. -/
theorem isInteriorPoint_chartedSpaceComp_iff (hΦ : Φ ⁻¹' I'.interior H' = I.interior H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    I'.IsInteriorPoint x ↔ I.IsInteriorPoint x := by
  let := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp H' H M
  have key := Set.ext_iff.1 hΦ (chartAt H x x)
  simp only [mem_preimage, ModelWithCorners.interior, mem_ofPred_eq,
    ModelWithCorners.IsInteriorPoint, extChartAt_self_eq] at key
  simpa only [ModelWithCorners.IsInteriorPoint, extChartAt_coe, chartAt_comp,
    OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq, OpenPartialHomeomorph.coe_trans,
    comp_apply, Homeomorph.toOpenPartialHomeomorph_apply] using key

/-- A change of model which preserves the interior points of the models keeps the boundary points:
a point is a boundary point for the composite charts exactly when it is one for the original
charts. -/
theorem isBoundaryPoint_chartedSpaceComp_iff (hΦ : Φ ⁻¹' I'.interior H' = I.interior H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    I'.IsBoundaryPoint x ↔ I.IsBoundaryPoint x := by
  let := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp H' H M
  rw [I'.isBoundaryPoint_iff_not_isInteriorPoint, I.isBoundaryPoint_iff_not_isInteriorPoint,
    Φ.isInteriorPoint_chartedSpaceComp_iff hΦ x]

/-- A change of model which preserves the interior points of the models keeps the manifold
interior. -/
theorem interior_chartedSpaceComp (hΦ : Φ ⁻¹' I'.interior H' = I.interior H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    I'.interior M = I.interior M :=
  Set.ext fun x => Φ.isInteriorPoint_chartedSpaceComp_iff hΦ x

/-- A change of model which preserves the interior points of the models keeps the manifold
boundary. -/
theorem boundary_chartedSpaceComp (hΦ : Φ ⁻¹' I'.interior H' = I.interior H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    I'.boundary M = I.boundary M :=
  Set.ext fun x => Φ.isBoundaryPoint_chartedSpaceComp_iff hΦ x

/-- A change of model which preserves the interior points of the models keeps boundarylessness. -/
theorem boundarylessManifold_chartedSpaceComp_iff (hΦ : Φ ⁻¹' I'.interior H' = I.interior H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    BoundarylessManifold I' M ↔ BoundarylessManifold I M := by
  let := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp H' H M
  exact ⟨fun h => ⟨fun x => (Φ.isInteriorPoint_chartedSpaceComp_iff hΦ x).1 (h.isInteriorPoint' x)⟩,
    fun h => ⟨fun x => (Φ.isInteriorPoint_chartedSpaceComp_iff hΦ x).2 (h.isInteriorPoint' x)⟩⟩

end Homeomorph
