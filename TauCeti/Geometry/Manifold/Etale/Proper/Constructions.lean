/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Proper.Basic
public import TauCeti.Geometry.Manifold.FullSubcategory
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Pullback
import TauCeti.Topology.CategoryTheory.Functor.Groupoid

/-!
# Constructions of proper étale Lie groupoids

A full restriction to an open set of objects inherits the object and arrow charts via the
two open embeddings. The product uses product charts on objects and pulls back the product
arrow charts along the homeomorphism between total arrows of the product and pairs of total
arrows. The resulting groupoids are proper étale. Proper étaleness also transfers along a functor
whose object and total-arrow maps are diffeomorphisms. This also supplies the Lie groupoid
structure on the source of that functor.
-/

public noncomputable section

open CategoryTheory Topology
open scoped ContDiff Manifold

namespace CategoryTheory.ObjectProperty

open TauCeti

variable {C H K : Type*} [Category C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (P : ObjectProperty C) (hP : IsOpen {x | P x})

variable {E F : Type*}
  [TopologicalSpace H] [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K) [I.Boundaryless] [J.Boundaryless]
  [IsGroupoid C] [ChartedSpace H C] [IsManifold I ∞ C] [ChartedSpace K (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsProperEtaleGroupoid I J C]

/-- The full subgroupoid on an open set, with the restricted manifold atlases, is proper étale. -/
theorem isProperEtaleGroupoid_fullSubcategory :
    letI := P.fullSubcategoryChartedSpace (H := H) hP
    letI := P.fullSubcategoryTotalChartedSpace (K := K) hP
      (IsLieGroupoid.contMDiff_source I J C).continuous
      (IsLieGroupoid.contMDiff_target I J C).continuous
    letI : IsManifold I ∞ P.FullSubcategory :=
      (isOpenEmbedding_obj_fullSubcategory hP).isLocalHomeomorph.isManifold_chartedSpaceComap
    letI : IsManifold J ∞ (Quiver.Total P.FullSubcategory) :=
      (isOpenEmbedding_total_fullSubcategory hP (IsLieGroupoid.contMDiff_source I J C).continuous
        (IsLieGroupoid.contMDiff_target I J C).continuous).isLocalHomeomorph
          |>.isManifold_chartedSpaceComap (I := J) (n := ∞)
    IsProperEtaleGroupoid I J P.FullSubcategory := by
  let := IsLieGroupoid.isTopologicalGroupoid I J C
  let := IsLieGroupoid.secondCountableTopology_arrows (I := I) (J := J) (C := C)
  let := IsProperEtaleGroupoid.t2Space_arrows (I := I) (J := J) (C := C)
  have hObj := (isOpenEmbedding_obj_fullSubcategory hP).isLocalHomeomorph
  have hArr := (isOpenEmbedding_total_fullSubcategory hP
    IsTopologicalGroupoid.continuous_source
    IsTopologicalGroupoid.continuous_target).isLocalHomeomorph
  have hObj' := P.isLocalDiffeomorph_obj_ι hP I ∞
  have hArr' := P.isLocalDiffeomorph_mapTotal_ι hP J ∞
    IsTopologicalGroupoid.continuous_source IsTopologicalGroupoid.continuous_target
  let := P.fullSubcategoryChartedSpace (H := H) hP
  let := P.fullSubcategoryTotalChartedSpace (K := K) hP
    IsTopologicalGroupoid.continuous_source IsTopologicalGroupoid.continuous_target
  have : IsManifold I ∞ P.FullSubcategory := hObj.isManifold_chartedSpaceComap
  have : IsManifold J ∞ (Quiver.Total P.FullSubcategory) := hArr.isManifold_chartedSpaceComap
  have hs := IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := I) (J := J) (C := C)
  have ht := IsProperEtaleGroupoid.isLocalDiffeomorph_target (I := I) (J := J) (C := C)
  refine IsProperEtaleGroupoid.of_isTopologicalGroupoid ?_ ?_
    (isProperMap_source_target_fullSubcategory (P := P)
      (IsProperEtaleGroupoid.isProperMap_source_target (I := I) (J := J)))
  · have h : Quiver.Total.left ∘ P.ι.toPrefunctor.mapTotal = P.ι.obj ∘ Quiver.Total.left :=
      funext (Prefunctor.mapTotal_left P.ι.toPrefunctor)
    intro a
    have hc := (hArr' a).comp (hg := hs _)
    rw [h] at hc
    exact hc.of_comp_left (hObj' a.left) IsTopologicalGroupoid.continuous_source.continuousAt
  · have h : Quiver.Total.right ∘ P.ι.toPrefunctor.mapTotal = P.ι.obj ∘ Quiver.Total.right :=
      funext (Prefunctor.mapTotal_right P.ι.toPrefunctor)
    intro a
    have hc := (hArr' a).comp (hg := ht _)
    rw [h] at hc
    exact hc.of_comp_left (hObj' a.right) IsTopologicalGroupoid.continuous_target.continuousAt

end CategoryTheory.ObjectProperty

namespace TauCeti

section Product

variable {C D H K : Type*} [Category C] [Category D] [TopologicalSpace (Quiver.Total C)]
  [TopologicalSpace (Quiver.Total D)] [TopologicalSpace H] [TopologicalSpace K]
  [ChartedSpace H (Quiver.Total C)] [ChartedSpace K (Quiver.Total D)]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (J : ModelWithCorners ℝ E H) (J' : ModelWithCorners ℝ F K)

variable {E₀ F₀ H₀ K₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [TopologicalSpace H₀] [TopologicalSpace K₀]
  (I : ModelWithCorners ℝ E₀ H₀) (I' : ModelWithCorners ℝ F₀ K₀)
  [FiniteDimensional ℝ E₀] [FiniteDimensional ℝ F₀]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [J'.Boundaryless]
  [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace H₀ C] [ChartedSpace K₀ D]
  [IsManifold I ∞ C] [IsManifold I' ∞ D] [IsManifold J ∞ (Quiver.Total C)]
  [IsManifold J' ∞ (Quiver.Total D)] [IsGroupoid C] [IsGroupoid D]
  [IsProperEtaleGroupoid I J C] [IsProperEtaleGroupoid I' J' D]

/-- Products preserve proper étale presentations. -/
theorem IsProperEtaleGroupoid.prod :
    letI := (totalProdHomeomorph C D).pullbackChartedSpace (H := ModelProd H K)
    letI : IsManifold (J.prod J') ∞ (Quiver.Total (C × D)) :=
      (totalProdHomeomorph C D).pullback_isManifold (J.prod J') ∞
    IsProperEtaleGroupoid (I.prod I') (J.prod J') (C × D) := by
  let := IsLieGroupoid.isTopologicalGroupoid I J C
  let := IsLieGroupoid.isTopologicalGroupoid I' J' D
  let := IsLieGroupoid.secondCountableTopology_arrows (I := I) (J := J) (C := C)
  let := IsLieGroupoid.secondCountableTopology_arrows (I := I') (J := J') (C := D)
  let := IsProperEtaleGroupoid.t2Space_arrows (I := I) (J := J) (C := C)
  let := IsProperEtaleGroupoid.t2Space_arrows (I := I') (J := J') (C := D)
  let e := totalProdHomeomorph C D
  let := e.pullbackChartedSpace (H := ModelProd H K)
  have : IsManifold (J.prod J') ∞ (Quiver.Total (C × D)) := e.pullback_isManifold (J.prod J') ∞
  have hs := (isLocalDiffeomorph_source (I := I) (J := J) (C := C)).prodMap
    (isLocalDiffeomorph_source (I := I') (J := J') (C := D))
  have ht := (isLocalDiffeomorph_target (I := I) (J := J) (C := C)).prodMap
    (isLocalDiffeomorph_target (I := I') (J := J') (C := D))
  refine of_isTopologicalGroupoid ?_ ?_
    (isProperMap_source_target_prod (isProperMap_source_target (I := I) (J := J))
      (isProperMap_source_target (I := I') (J := J')))
  · have h : Prod.map Quiver.Total.left Quiver.Total.left ∘ e = Quiver.Total.left := by
      funext a
      simp [e, Prod.map]
    rw [← h]
    exact (e.isLocalDiffeomorph_comp_pullbackChartedSpace_iff).2 hs
  · have h : Prod.map Quiver.Total.right Quiver.Total.right ∘ e = Quiver.Total.right := by
      funext a
      simp [e, Prod.map]
    rw [← h]
    exact (e.isLocalDiffeomorph_comp_pullbackChartedSpace_iff).2 ht

end Product

end TauCeti

namespace CategoryTheory.Functor

open TauCeti

variable {C D E F E' F' H K H' K' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace K]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] [TopologicalSpace K']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {I' : ModelWithCorners ℝ E' H'} {J' : ModelWithCorners ℝ F' K'}
  [I.Boundaryless] [J.Boundaryless] [I'.Boundaryless] [J'.Boundaryless]
  [Category C] [IsGroupoid C] [Category D] [IsGroupoid D]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace D] [ChartedSpace H' D] [IsManifold I' ∞ D]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace K (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)]
  [TopologicalSpace (Quiver.Total D)] [ChartedSpace K' (Quiver.Total D)]
  [IsManifold J' ∞ (Quiver.Total D)]
  [IsProperEtaleGroupoid I J C]

/-- A functor into a proper étale Lie groupoid gives its domain a proper étale Lie groupoid
structure if it is a diffeomorphism on objects and on total arrows. -/
theorem isProperEtaleGroupoid_of_diffeomorphisms
    (F : D ⥤ C) (e₀ : D ≃ₘ^∞⟮I', I⟯ C) (e₁ : Quiver.Total D ≃ₘ^∞⟮J', J⟯ Quiver.Total C)
    (h₀ : ⇑e₀ = F.obj) (h₁ : ⇑e₁ = F.toPrefunctor.mapTotal) :
    IsProperEtaleGroupoid I' J' D := by
  have hsource (a : Quiver.Total D) : (e₁ a).left = e₀ a.left := by
    simp [h₀, h₁]
  have htarget (a : Quiver.Total D) : (e₁ a).right = e₀ a.right := by
    simp [h₀, h₁]
  have hs : (Quiver.Total.left : Quiver.Total D → D) =
      e₀.symm ∘ Quiver.Total.left ∘ e₁ := by
    funext a
    simp [Function.comp_apply, hsource]
  have ht : (Quiver.Total.right : Quiver.Total D → D) =
      e₀.symm ∘ Quiver.Total.right ∘ e₁ := by
    funext a
    simp [Function.comp_apply, htarget]
  have hp : (fun a : Quiver.Total D ↦ (a.left, a.right)) =
      (e₀.symm.toHomeomorph.prodCongr e₀.symm.toHomeomorph) ∘
        (fun a : Quiver.Total C ↦ (a.left, a.right)) ∘ e₁ := by
    funext a
    simp [hsource, htarget]
  let := IsLieGroupoid.isTopologicalGroupoid I J C
  let := F.isTopologicalGroupoid_of_isInducing
    (h₀ ▸ e₀.toHomeomorph.isInducing) (h₁ ▸ e₁.toHomeomorph.isInducing)
  let := IsLieGroupoid.secondCountableTopology_arrows (I := I) (J := J) (C := C)
  let := IsProperEtaleGroupoid.t2Space_arrows (I := I) (J := J) (C := C)
  let := e₁.toHomeomorph.secondCountableTopology
  let := e₁.toHomeomorph.isEmbedding.t2Space
  refine IsProperEtaleGroupoid.of_isTopologicalGroupoid ?_ ?_ ?_
  · rw [hs]
    exact fun a ↦ ((e₁.isLocalDiffeomorph a).comp
      (hg := IsProperEtaleGroupoid.isLocalDiffeomorph_source (I := I) (J := J) (e₁ a))).comp
        (hg := e₀.symm.isLocalDiffeomorph (e₁ a).left)
  · rw [ht]
    exact fun a ↦ ((e₁.isLocalDiffeomorph a).comp
      (hg := IsProperEtaleGroupoid.isLocalDiffeomorph_target (I := I) (J := J) (e₁ a))).comp
        (hg := e₀.symm.isLocalDiffeomorph (e₁ a).right)
  · rw [hp]
    exact (e₀.symm.toHomeomorph.prodCongr e₀.symm.toHomeomorph).isProperMap.comp
      ((IsProperEtaleGroupoid.isProperMap_source_target (I := I) (J := J)).comp
        e₁.toHomeomorph.isProperMap)

end CategoryTheory.Functor
