/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.DualGraph
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Category
import TauCeti.AlgebraicGeometry.Scheme.Basic
import TauCeti.Topology.Irreducible

/-!
# Vertices of the dual graph contracted by a prestable map

Let `F : C ⟶ V` be a prestable map over a separably closed field `K`. The vertices of the dual
graph of its pointed source curve (`TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraph`)
are the irreducible components of the blowup `ν : C^ν ⟶ C` of `C` along its singular subscheme. A
vertex `v` is **contracted** by `F` when `ν ≫ F` is constant on `v`, that is, when `F` is constant
on the image `ν(v)`, an irreducible component of `C`.

A constant map contracts every vertex. Postcomposition with a morphism of targets `h` contracts
every vertex the map contracts, and exactly those when the fibres of `h` are discrete, for
instance when `h` is locally quasi-finite or injective on points: the image of a vertex is
irreducible, and an irreducible subset of a discrete set has at most one point.

The image `ν(v)` is irreducible (`isIrreducible_image_blowupToBase`), and the contraction
criterion is stated on it (`isContractedVertex_iff_image`). That `ν(v)` is moreover an irreducible
component of `C`, so that the component lemmas of the curve apply to it, is not proved here: it
needs `ν` to be an isomorphism over the smooth locus, and the smooth locus to be dense in every
component of `C`, neither of which the nodal blowup API provides yet.

## Main definitions

* `TauCeti.AlgebraicGeometry.PrestableMap.IsContractedVertex`: a vertex of the dual graph of the
  source curve whose component is contracted by the map.

## Main results

In the namespace `TauCeti.AlgebraicGeometry.PrestableMap`:

* `isContractedVertex_iff_image`: a vertex is contracted when the map is constant on its image
  in the source curve.
* `isContractedVertex_const`: a constant map contracts every vertex.
* `IsContractedVertex.postcomp`: postcomposition contracts every vertex the map contracts.
* `isContractedVertex_postcomp_iff_of_isDiscrete`: postcomposition with a morphism of targets with
  discrete fibres contracts the same vertices; `isContractedVertex_postcomp_iff_of_injective`,
  `isContractedVertex_postcomp_iff_of_locallyQuasiFinite` and `isContractedVertex_postcomp_iff`
  are the cases of a morphism injective on points, locally quasi-finite, or universally injective.
* `isContractedVertex_dualGraphIsoOfIso_vertexEquiv_iff`: an isomorphism of source curves
  commuting with the maps, such as one coming from an isomorphism of prestable maps, matches the
  contracted vertices.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PrestableMap

variable {V W : Scheme.{u}} {n : ℕ} {K : Type u} [Field K] [IsSepClosed K]
  {q : V ⟶ Spec (.of K)} (F : PrestableMap q n)

/-- A vertex `v` of the dual graph of the source curve of a prestable map over a separably closed
field is **contracted** by the map when the composite of the blowup `ν` of the curve along its
singular subscheme with the map is constant on the component `v` of the blowup, that is, when the
map is constant on the image `ν(v)` of `v`, an irreducible component of the curve. -/
def IsContractedVertex (v : F.curve.dualGraph.Vertex) : Prop :=
  (((F.curve.total.singularLocus K).blowupToBase ≫ F.map) ''
    (F.curve.total.dualGraphVertexEquiv F.curve.markingPoint v : Set _)).Subsingleton

/-- Restatement of the definition of a contracted vertex. -/
theorem isContractedVertex_iff (v : F.curve.dualGraph.Vertex) :
    F.IsContractedVertex v ↔
      (((F.curve.total.singularLocus K).blowupToBase ≫ F.map) ''
        (F.curve.total.dualGraphVertexEquiv F.curve.markingPoint v : Set _)).Subsingleton :=
  Iff.rfl

/-- The image `ν(v)` in the source curve of the component `v` of the blowup is irreducible. -/
theorem isIrreducible_image_blowupToBase (v : F.curve.dualGraph.Vertex) :
    IsIrreducible ((F.curve.total.singularLocus K).blowupToBase ''
      (F.curve.total.dualGraphVertexEquiv F.curve.markingPoint v : Set _)) :=
  (F.curve.total.dualGraphVertexEquiv F.curve.markingPoint v).prop.1.image _
    (Scheme.Hom.continuous _).continuousOn

/-- A vertex `v` is contracted exactly when the map is constant on the image `ν(v)` of its
component in the source curve. -/
theorem isContractedVertex_iff_image (v : F.curve.dualGraph.Vertex) :
    F.IsContractedVertex v ↔
      (F.map '' ((F.curve.total.singularLocus K).blowupToBase ''
        (F.curve.total.dualGraphVertexEquiv F.curve.markingPoint v : Set _))).Subsingleton := by
  rw [isContractedVertex_iff, Scheme.Hom.image_comp]

/-- Over a separably closed field, a constant map contracts every vertex of the dual graph of its
source curve. -/
@[simp]
theorem isContractedVertex_const (P : PointedPrestableFamily (Spec (.of K)) n)
    (σ : Spec (.of K) ⟶ V) (hσ : σ ≫ q = 𝟙 _) (v : P.dualGraph.Vertex) :
    (const P σ hσ).IsContractedVertex v := by
  -- The map of `const P σ hσ` is `P.toBase ≫ σ` by definition and its curve is `P`; the image
  -- factors through the point `Spec K`. `rw [const_map]` is not used: the dual-graph vertex `v`
  -- depends on the curve, so the rewrite would change the type of the set being mapped.
  have : (((P.total.singularLocus K).blowupToBase ≫ P.toBase ≫ σ) ''
      (P.total.dualGraphVertexEquiv P.markingPoint v : Set _)).Subsingleton := by
    rw [← Category.assoc, Scheme.Hom.image_comp]
    exact Set.subsingleton_of_subsingleton.image _
  exact this

/-- A vertex is contracted by the postcomposed map exactly when its image under the map is
contracted by the morphism of targets. -/
private theorem isContractedVertex_postcomp_iff_image {r : W ⟶ Spec (.of K)} (h : V ⟶ W)
    (hh : h ≫ r = q) (v : F.curve.dualGraph.Vertex) :
    (F.postcomp h hh).IsContractedVertex v ↔
      (h '' (((F.curve.total.singularLocus K).blowupToBase ≫ F.map) ''
        (F.curve.total.dualGraphVertexEquiv F.curve.markingPoint v : Set _))).Subsingleton := by
  -- The source curve of `F.postcomp h hh` is that of `F` (`postcomp_curve`); `change` is used
  -- because the vertex `v` depends on the curve, so rewriting with that lemma would change the
  -- type of the set being mapped. For the same reason the image computation is a term, not `rw`.
  change (((F.curve.total.singularLocus K).blowupToBase ≫ (F.postcomp h hh).map) ''
    (F.curve.total.dualGraphVertexEquiv F.curve.markingPoint v : Set _)).Subsingleton ↔ _
  exact Iff.of_eq <| congrArg Set.Subsingleton <| (Scheme.Hom.image_comp _ _ _).trans <|
    (F.image_postcomp_map h hh _).trans (congrArg _ (Scheme.Hom.image_comp _ _ _).symm)

variable {F} in
/-- Postcomposition with a morphism of targets contracts every vertex the map contracts. -/
theorem IsContractedVertex.postcomp {r : W ⟶ Spec (.of K)} (h : V ⟶ W) (hh : h ≫ r = q)
    {v : F.curve.dualGraph.Vertex} (hv : F.IsContractedVertex v) :
    (F.postcomp h hh).IsContractedVertex v := by
  exact (F.isContractedVertex_postcomp_iff_image h hh v).2 (hv.image h)

/-- Postcomposition with a morphism of targets whose fibres are discrete contracts the same
vertices: the image of a vertex is irreducible, so it is a point once its image under the
morphism of targets is. -/
theorem isContractedVertex_postcomp_iff_of_isDiscrete {r : W ⟶ Spec (.of K)} (h : V ⟶ W)
    (hdisc : ∀ w : W, _root_.IsDiscrete (h ⁻¹' {w})) (hh : h ≫ r = q)
    {v : F.curve.dualGraph.Vertex} :
    (F.postcomp h hh).IsContractedVertex v ↔ F.IsContractedVertex v := by
  rw [isContractedVertex_postcomp_iff_image, isContractedVertex_iff]
  exact ((F.curve.total.dualGraphVertexEquiv F.curve.markingPoint v).prop.1.image _
    (Scheme.Hom.continuous _).continuousOn).isPreirreducible.subsingleton_image_iff hdisc

/-- Postcomposition with a morphism of targets that is injective on points contracts the same
vertices. -/
theorem isContractedVertex_postcomp_iff_of_injective {r : W ⟶ Spec (.of K)} (h : V ⟶ W)
    (hinj : Function.Injective h) (hh : h ≫ r = q) {v : F.curve.dualGraph.Vertex} :
    (F.postcomp h hh).IsContractedVertex v ↔ F.IsContractedVertex v :=
  F.isContractedVertex_postcomp_iff_of_isDiscrete h
    (fun _ ↦ (Set.subsingleton_singleton.preimage hinj).isDiscrete) hh

/-- Postcomposition with a locally quasi-finite morphism of targets, for instance a finite
morphism or an immersion, contracts the same vertices. -/
@[simp]
theorem isContractedVertex_postcomp_iff_of_locallyQuasiFinite {r : W ⟶ Spec (.of K)} (h : V ⟶ W)
    [LocallyQuasiFinite h] (hh : h ≫ r = q) {v : F.curve.dualGraph.Vertex} :
    (F.postcomp h hh).IsContractedVertex v ↔ F.IsContractedVertex v :=
  F.isContractedVertex_postcomp_iff_of_isDiscrete h h.isDiscrete_preimage_singleton hh

/-- Postcomposition with a universally injective morphism of targets contracts the same
vertices. -/
@[simp]
theorem isContractedVertex_postcomp_iff {r : W ⟶ Spec (.of K)} (h : V ⟶ W)
    [UniversallyInjective h] (hh : h ≫ r = q) {v : F.curve.dualGraph.Vertex} :
    (F.postcomp h hh).IsContractedVertex v ↔ F.IsContractedVertex v :=
  F.isContractedVertex_postcomp_iff_of_injective h h.injective hh

section Iso

variable {F} {G : PrestableMap q n}

/-- An isomorphism of the source curves of prestable maps over a separably closed field that
commutes with the maps, for instance the one underlying an isomorphism `e : F ≅ G` of prestable
maps (`toCurve.mapIso e`), matches the contracted vertices: under the induced isomorphism
`PointedPrestableFamily.dualGraphIsoOfIso` of dual graphs, the map `G` is constant on the image of
the component corresponding to `v` exactly when `F` is constant on the image of `v`. -/
@[simp]
theorem isContractedVertex_dualGraphIsoOfIso_vertexEquiv_iff (e : F.curve ≅ G.curve)
    (he : e.hom.hom ≫ G.map = F.map) (v : F.curve.dualGraph.Vertex) :
    G.IsContractedVertex ((PointedPrestableFamily.dualGraphIsoOfIso e).vertexEquiv v) ↔
      F.IsContractedVertex v := by
  have h := Scheme.image_blowupToBase_comp_dualGraphIsoOfIso_vertexEquiv (K := K)
    (PointedPrestableFamily.totalIso e) e.hom.hom_comp_toBase _ _
    (PointedPrestableFamily.totalIso_hom_markingPoint e) G.map v
  rw [PointedPrestableFamily.totalIso_hom, he] at h
  rw [isContractedVertex_iff, isContractedVertex_iff, PointedPrestableFamily.dualGraphIsoOfIso, h]

end Iso

end PrestableMap

end TauCeti.AlgebraicGeometry
