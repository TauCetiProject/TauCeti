/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Topology.CategoryTheory.FullSubcategory

/-!
# Manifold charts on open full subcategories

The object and total-arrow inclusions pull back the ambient charts to an open full subcategory.
With these charts the inclusions are local diffeomorphisms.
-/

public noncomputable section

open scoped ContDiff Manifold

namespace CategoryTheory.ObjectProperty

open TauCeti

variable {C : Type*} [Category C] [TopologicalSpace C]
  (P : ObjectProperty C) (hP : IsOpen {x | P x})

/-- The charts on an open full subcategory's objects are the restrictions of the ambient charts. -/
abbrev fullSubcategoryChartedSpace {H : Type*} [TopologicalSpace H] [ChartedSpace H C] :
    ChartedSpace H P.FullSubcategory :=
  (isOpenEmbedding_obj_fullSubcategory hP).isLocalHomeomorph.chartedSpaceComap

section Total

variable [TopologicalSpace (Quiver.Total C)]

/-- For continuous endpoints, the total-arrow charts of an open full subcategory are the
restrictions of the ambient arrow charts. -/
abbrev fullSubcategoryTotalChartedSpace {K : Type*} [TopologicalSpace K]
    [ChartedSpace K (Quiver.Total C)]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C)) :
    ChartedSpace K (Quiver.Total P.FullSubcategory) :=
  (isOpenEmbedding_total_fullSubcategory hP hs ht).isLocalHomeomorph.chartedSpaceComap

end Total

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

/-- The object inclusion of an open full subcategory is a local diffeomorphism for the
restricted object atlas. -/
theorem isLocalDiffeomorph_ι_obj [ChartedSpace H C] :
    letI := P.fullSubcategoryChartedSpace (H := H) hP
    IsLocalDiffeomorph I I n P.ι.obj :=
  (isOpenEmbedding_obj_fullSubcategory hP).isLocalHomeomorph.isLocalDiffeomorph_chartedSpaceComap

/-- The total-arrow inclusion of an open full subcategory is a local diffeomorphism for the
restricted arrow atlas when the ambient endpoints are continuous. -/
theorem isLocalDiffeomorph_ι_mapTotal [TopologicalSpace (Quiver.Total C)]
    [ChartedSpace H (Quiver.Total C)]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C)) :
    letI := P.fullSubcategoryTotalChartedSpace (K := H) hP hs ht
    IsLocalDiffeomorph I I n P.ι.toPrefunctor.mapTotal :=
  (isOpenEmbedding_total_fullSubcategory hP hs ht).isLocalHomeomorph
    |>.isLocalDiffeomorph_chartedSpaceComap

end CategoryTheory.ObjectProperty
