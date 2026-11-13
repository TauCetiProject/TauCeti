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

When `Φ` is read in the model vector spaces as a homeomorphism `L : E ≃ₜ E'`, that is
`I' ∘ Φ = L ∘ I`, the change of model keeps the manifold interior and the manifold boundary of `M`
(`Homeomorph.interior_chartedSpaceComp`, `Homeomorph.boundary_chartedSpaceComp`): `L` carries the
range of `I` onto the range of `I'`, and so its interior onto the interior.
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

/-- A change of model which is a homeomorphism `L` of the model vector spaces, `I' ∘ Φ = L ∘ I`,
keeps the interior points: a point is interior for the composite charts exactly when it is
interior for the original ones. -/
theorem isInteriorPoint_chartedSpaceComp_iff (L : E ≃ₜ E') (hL : ∀ x, I' (Φ x) = L (I x))
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    I'.IsInteriorPoint x ↔ I.IsInteriorPoint x := by
  let := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp H' H M
  have hrange : range I' = L '' range I := by
    rw [← range_comp, ← Φ.surjective.range_comp]
    exact congrArg range (funext hL)
  simp only [ModelWithCorners.IsInteriorPoint, extChartAt_coe, chartAt_comp,
    OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq, OpenPartialHomeomorph.coe_trans,
    comp_apply, Homeomorph.toOpenPartialHomeomorph_apply, hL, hrange, ← L.image_interior,
    L.injective.mem_set_image]

/-- A change of model which is a homeomorphism of the model vector spaces keeps the manifold
interior. -/
theorem interior_chartedSpaceComp (L : E ≃ₜ E') (hL : ∀ x, I' (Φ x) = L (I x))
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    I'.interior M = I.interior M :=
  Set.ext fun x => Φ.isInteriorPoint_chartedSpaceComp_iff L hL x

/-- A change of model which is a homeomorphism of the model vector spaces keeps the manifold
boundary. -/
theorem boundary_chartedSpaceComp (L : E ≃ₜ E') (hL : ∀ x, I' (Φ x) = L (I x))
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
    letI := ChartedSpace.comp H' H M
    I'.boundary M = I.boundary M := by
  let := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let := ChartedSpace.comp H' H M
  rw [← I'.compl_interior, ← I.compl_interior, Φ.interior_chartedSpaceComp L hL M]

end Homeomorph
