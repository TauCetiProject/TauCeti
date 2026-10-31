/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Retraction
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Homeomorph

import TauCeti.Order.Chain

/-!
# Open simplicial neighbourhoods of subcomplexes

Let `P` be a subcomplex of an abstract simplicial complex `K`, or more generally any precomplex
of finite sets of vertices. Its polyhedron in the weak realization of `K` is the closed set of
points whose barycentric support is a face of `P`. A subcomplex need not be full, so the open
star retraction of `AbstractSimplicialComplex.openStarRetraction` does not apply to it directly.

After one barycentric subdivision it does. The vertices of the subdivision are the faces of `K`.
Under the canonical homeomorphism `barycentricSubdivisionRealizationHomeomorph`, the polyhedron
of `P` is exactly the polyhedron of the full subcomplex of the subdivision spanned by the faces
of `P`: the support of the image of a subdivision point is the greatest face in its support
chain, and `P` is closed under passing to nonempty subsets.

The open star of these face-vertices therefore transports to an open neighbourhood of the
polyhedron of `P` in the realization of `K`, together with a strong deformation retraction onto
that polyhedron. In the barycentric coordinates of `K` the neighbourhood has an intrinsic
description: a point lies in it exactly when the set of vertices at which its coordinate is
largest is a face of `P`. Indeed, that set is the least face in the support chain of the
corresponding subdivision point.

No finiteness or local finiteness is assumed.

## Main definitions

* `AbstractSimplicialComplex.openSimplicialNeighborhood`: the points whose maximal barycentric
  coordinates occur exactly on a face of `P`.
* `AbstractSimplicialComplex.openSimplicialNeighborhoodRetraction`: the retraction of this
  neighbourhood onto the polyhedron of `P`.
* `AbstractSimplicialComplex.openSimplicialNeighborhoodDeformation`: a homotopy from the identity
  of the neighbourhood to this retraction, fixing the polyhedron of `P`.

## Main results

* `preimage_barycentricSubdivisionRealizationHomeomorph_setOf_support_mem`: the polyhedron of
  `P` is the polyhedron of the full subcomplex of the subdivision spanned by the faces of `P`.
* `preimage_barycentricSubdivisionRealizationHomeomorph_openSimplicialNeighborhood`: the
  neighbourhood is the image of the open star of those face-vertices.
* `AbstractSimplicialComplex.isOpen_openSimplicialNeighborhood` and
  `AbstractSimplicialComplex.setOf_support_mem_subset_openSimplicialNeighborhood`: it is an open
  neighbourhood of the polyhedron of `P`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 3 (derived neighbourhoods; every subcomplex is full in a derived subdivision).
-/

public section

noncomputable section

open Set Topology TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι) (P : PreAbstractSimplicialComplex ι)

attribute [local instance] Classical.decEq

/-- The support of a point of the barycentric subdivision has a greatest face. -/
private theorem exists_greatest_mem_support
    (x : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex)) :
    ∃ σ ∈ x.1.support, ∀ τ ∈ x.1.support, τ ≤ σ := by
  have hx := TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff.mp
    (support_mem _ x)
  obtain ⟨σ, hσ, hmax⟩ := hx.2.exists_isGreatest x.1.support.finite_toSet hx.1
  exact ⟨σ, hσ, fun τ hτ => hmax hτ⟩

/-- The support of a point of the barycentric subdivision has a least face. -/
private theorem exists_least_mem_support
    (x : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex)) :
    ∃ σ ∈ x.1.support, ∀ τ ∈ x.1.support, σ ≤ τ := by
  have hx := TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff.mp
    (support_mem _ x)
  obtain ⟨σ, hσ, hmin⟩ := hx.2.exists_isLeast x.1.support.finite_toSet hx.1
  exact ⟨σ, hσ, fun τ hτ => hmin hτ⟩

/-- A point of the barycentric subdivision maps into the polyhedron of `P` exactly when every
face-vertex in its support is a face of `P`. -/
theorem support_barycentricSubdivisionRealizationMap_mem_iff
    (x : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex)) :
    (barycentricSubdivisionRealizationMap K x).1.support ∈ P ↔
      (x.1.support : Set (Face K)) ⊆ {σ | σ.1 ∈ P} := by
  obtain ⟨σ, hσ, hmax⟩ := exists_greatest_mem_support K x
  rw [barycentricSubdivisionRealizationMap_val,
    support_barycentricSubdivisionLinearMap_eq_greatest K (Realization.nonneg _ x) hσ hmax]
  refine ⟨fun hP τ hτ => ?_, fun h => h hσ⟩
  exact P.isRelLowerSet_faces.mem_of_le hP (hmax τ hτ) (K.isRelLowerSet_faces.prop_of_mem τ.2)

/-- **Every subcomplex is full after one barycentric subdivision.** The canonical subdivision
homeomorphism identifies the polyhedron of `P` with the polyhedron of the full subcomplex of the
subdivision spanned by the faces of `P`. -/
theorem preimage_barycentricSubdivisionRealizationHomeomorph_setOf_support_mem :
    barycentricSubdivisionRealizationHomeomorph K ⁻¹' {y : Realization K | y.1.support ∈ P} =
      {x | (x.1.support : Set (Face K)) ⊆ {σ | σ.1 ∈ P}} := by
  ext x
  rw [mem_preimage, barycentricSubdivisionRealizationHomeomorph_apply]
  exact support_barycentricSubdivisionRealizationMap_mem_iff K P x

/-- The open simplicial neighbourhood of `P` in the realization of `K`: the points whose set of
vertices of largest barycentric coordinate is a face of `P`. It is the image of the open star, in
the barycentric subdivision, of the face-vertices that are faces of `P`. -/
def openSimplicialNeighborhood : Set (Realization K) :=
  {y | ∃ σ ∈ P, ∀ v, v ∈ σ ↔ ∀ w, y.1 w ≤ y.1 v}

/-- Membership in the open simplicial neighbourhood: the vertices of largest coordinate form a
face of `P`. -/
@[simp]
theorem mem_openSimplicialNeighborhood_iff {y : Realization K} :
    y ∈ K.openSimplicialNeighborhood P ↔ ∃ σ ∈ P, ∀ v, v ∈ σ ↔ ∀ w, y.1 w ≤ y.1 v :=
  Iff.rfl

/-- The least face in the support chain of a subdivision point is the set of vertices at which
its image has largest coordinate. -/
private theorem mem_least_iff_forall_le
    (x : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex))
    {σ : Face K} (hσ : σ ∈ x.1.support) (hmin : ∀ τ ∈ x.1.support, σ ≤ τ) (v : ι) :
    v ∈ σ.1 ↔ ∀ w, (barycentricSubdivisionRealizationMap K x).1 w ≤
      (barycentricSubdivisionRealizationMap K x).1 v := by
  -- Every coordinate is at most the total `T` of the weighted reciprocal cardinalities, with
  -- equality exactly on the least face of the chain.
  set T := ∑ τ ∈ x.1.support, x.1 τ * (τ.1.card : ℝ)⁻¹
  have hterm (u : ι) (τ : Face K) :
      x.1 τ * (if u ∈ τ.1 then (τ.1.card : ℝ)⁻¹ else 0) ≤ x.1 τ * (τ.1.card : ℝ)⁻¹ := by
    refine mul_le_mul_of_nonneg_left ?_ (Realization.nonneg _ x τ)
    split_ifs
    · exact le_rfl
    · positivity
  have hle (u : ι) : (barycentricSubdivisionRealizationMap K x).1 u ≤ T := by
    rw [barycentricSubdivisionRealizationMap_val, barycentricSubdivisionLinearMap_apply]
    exact Finset.sum_le_sum fun τ _ => hterm u τ
  have heq {u : ι} (hu : u ∈ σ.1) : (barycentricSubdivisionRealizationMap K x).1 u = T := by
    rw [barycentricSubdivisionRealizationMap_val, barycentricSubdivisionLinearMap_apply]
    exact Finset.sum_congr rfl fun τ hτ => by simp [hmin τ hτ hu]
  have hlt {u : ι} (hu : u ∉ σ.1) : (barycentricSubdivisionRealizationMap K x).1 u < T := by
    rw [barycentricSubdivisionRealizationMap_val, barycentricSubdivisionLinearMap_apply]
    refine Finset.sum_lt_sum (fun τ _ => hterm u τ) ⟨σ, hσ, ?_⟩
    have hpos : 0 < x.1 σ :=
      Realization.pos_of_mem_support _ x hσ
    have hcard : 0 < (σ.1.card : ℝ)⁻¹ := by
      have := Finset.card_pos.mpr (K.isRelLowerSet_faces.prop_of_mem σ.2)
      positivity
    simpa [hu] using mul_pos hpos hcard
  refine ⟨fun hv w => heq hv ▸ hle w, fun hv => ?_⟩
  by_contra hvσ
  obtain ⟨u, hu⟩ := K.isRelLowerSet_faces.prop_of_mem σ.2
  exact (hlt hvσ).not_ge ((heq hu).symm ▸ hv u)

/-- A point of the barycentric subdivision maps into the open simplicial neighbourhood of `P`
exactly when it lies in the open star of the face-vertices that are faces of `P`. -/
theorem barycentricSubdivisionRealizationMap_mem_openSimplicialNeighborhood_iff
    (x : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex)) :
    barycentricSubdivisionRealizationMap K x ∈ K.openSimplicialNeighborhood P ↔
      x ∈ (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openStarRealizationSet {σ : Face K | σ.1 ∈ P} := by
  obtain ⟨σ, hσ, hmin⟩ := exists_least_mem_support K x
  have hchar := mem_least_iff_forall_le K x hσ hmin
  rw [mem_openSimplicialNeighborhood_iff, mem_openStarRealizationSet]
  constructor
  · rintro ⟨ρ, hρ, hρchar⟩
    have hρσ : ρ = σ.1 := Finset.ext fun v => (hρchar v).trans (hchar v).symm
    exact ⟨σ, (hρσ ▸ hρ : σ.1 ∈ P), Realization.pos_of_mem_support _ x hσ⟩
  · rintro ⟨τ, hτ, hpos⟩
    have hτsupp : τ ∈ x.1.support := Finsupp.mem_support_iff.mpr hpos.ne'
    refine ⟨σ.1, ?_, hchar⟩
    exact P.isRelLowerSet_faces.mem_of_le hτ (hmin τ hτsupp)
      (K.isRelLowerSet_faces.prop_of_mem σ.2)

/-- The canonical subdivision homeomorphism identifies the open star, in the barycentric
subdivision, of the face-vertices that are faces of `P` with the open simplicial neighbourhood
of `P`. -/
theorem preimage_barycentricSubdivisionRealizationHomeomorph_openSimplicialNeighborhood :
    barycentricSubdivisionRealizationHomeomorph K ⁻¹' K.openSimplicialNeighborhood P =
      (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openStarRealizationSet {σ : Face K | σ.1 ∈ P} := by
  ext x
  rw [mem_preimage, barycentricSubdivisionRealizationHomeomorph_apply]
  exact barycentricSubdivisionRealizationMap_mem_openSimplicialNeighborhood_iff K P x

/-- The open simplicial neighbourhood of `P` is open in the weak topology. -/
theorem isOpen_openSimplicialNeighborhood : IsOpen (K.openSimplicialNeighborhood P) := by
  rw [← (barycentricSubdivisionRealizationHomeomorph K).isOpen_preimage,
    preimage_barycentricSubdivisionRealizationHomeomorph_openSimplicialNeighborhood]
  exact isOpen_openStarRealizationSet _ _

/-- The polyhedron of `P` lies in its open simplicial neighbourhood. -/
theorem setOf_support_mem_subset_openSimplicialNeighborhood :
    {y : Realization K | y.1.support ∈ P} ⊆ K.openSimplicialNeighborhood P := by
  rw [← (barycentricSubdivisionRealizationHomeomorph K).image_preimage
      {y : Realization K | y.1.support ∈ P},
    preimage_barycentricSubdivisionRealizationHomeomorph_setOf_support_mem, image_subset_iff,
    preimage_barycentricSubdivisionRealizationHomeomorph_openSimplicialNeighborhood]
  exact setOf_support_subset_subset_openStarRealizationSet _ _

/-- The subdivision homeomorphism, restricted to the open star of the face-vertices of `P` and
the open simplicial neighbourhood of `P`. -/
private abbrev openStarHomeomorph :
    (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openStarRealizationSet {σ : Face K | σ.1 ∈ P} ≃ₜ
      K.openSimplicialNeighborhood P :=
  (barycentricSubdivisionRealizationHomeomorph K).sets
    (preimage_barycentricSubdivisionRealizationHomeomorph_openSimplicialNeighborhood K P).symm

/-- The subdivision homeomorphism, restricted to the polyhedron of the full subcomplex spanned by
the face-vertices of `P` and the polyhedron of `P`. -/
private abbrev fullHomeomorph :
    {x : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex) | (x.1.support : Set (Face K)) ⊆ {σ | σ.1 ∈ P}} ≃ₜ
      {y : Realization K | y.1.support ∈ P} :=
  (barycentricSubdivisionRealizationHomeomorph K).sets
    (preimage_barycentricSubdivisionRealizationHomeomorph_setOf_support_mem K P).symm

private theorem openStarHomeomorph_symm_mk
    (x : (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).openStarRealizationSet {σ : Face K | σ.1 ∈ P}) :
    (openStarHomeomorph K P).symm
        ⟨barycentricSubdivisionRealizationMap K x,
          (barycentricSubdivisionRealizationMap_mem_openSimplicialNeighborhood_iff K P x).2 x.2⟩ =
      x :=
  (openStarHomeomorph K P).symm_apply_eq.2 (Subtype.ext (by simp))

/-- The retraction of the open simplicial neighbourhood of `P` onto the polyhedron of `P`. It is
the open star retraction of the barycentric subdivision onto the full subcomplex spanned by the
faces of `P`, transported along the subdivision homeomorphism. -/
def openSimplicialNeighborhoodRetraction :
    C(K.openSimplicialNeighborhood P, {y : Realization K | y.1.support ∈ P}) :=
  (fullHomeomorph K P : C(_, _)).comp
    (((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).openStarRetraction {σ : Face K | σ.1 ∈ P}).comp
        ((openStarHomeomorph K P).symm : C(_, _)))

/-- The retraction commutes with the subdivision homeomorphism: on the image of a point of the
open star of the face-vertices of `P`, it is the image of the open star retraction. -/
theorem openSimplicialNeighborhoodRetraction_barycentricSubdivisionRealizationMap
    (x : (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).openStarRealizationSet {σ : Face K | σ.1 ∈ P}) :
    (K.openSimplicialNeighborhoodRetraction P
        ⟨barycentricSubdivisionRealizationMap K x,
          (barycentricSubdivisionRealizationMap_mem_openSimplicialNeighborhood_iff K P x).2 x.2⟩ :
        Realization K) =
      barycentricSubdivisionRealizationMap K
        ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
          K.toPreAbstractSimplicialComplex).openStarRetraction {σ : Face K | σ.1 ∈ P} x) := by
  simp only [openSimplicialNeighborhoodRetraction, ContinuousMap.comp_apply,
    ContinuousMap.coe_ofClass, openStarHomeomorph_symm_mk, Homeomorph.subtype_apply_coe,
    barycentricSubdivisionRealizationHomeomorph_apply]

/-- The retraction fixes the polyhedron of `P`. -/
@[simp]
theorem openSimplicialNeighborhoodRetraction_inclusion
    (y : {y : Realization K | y.1.support ∈ P}) :
    K.openSimplicialNeighborhoodRetraction P
      (Set.inclusion (K.setOf_support_mem_subset_openSimplicialNeighborhood P) y) = y := by
  have hx : (openStarHomeomorph K P).symm
      (Set.inclusion (K.setOf_support_mem_subset_openSimplicialNeighborhood P) y) =
      Set.inclusion (setOf_support_subset_subset_openStarRealizationSet _ _)
        ((fullHomeomorph K P).symm y) :=
    Subtype.ext (by simp)
  simp only [openSimplicialNeighborhoodRetraction, ContinuousMap.comp_apply,
    ContinuousMap.coe_ofClass, hx, openStarRetraction_inclusion, Homeomorph.apply_symm_apply]

/-- **The open simplicial neighbourhood of a subcomplex deformation retracts onto it.** At time
`t` a point is moved to the subdivision homeomorphism image of the open star deformation, at time
`t`, of the corresponding subdivision point. The homotopy fixes the polyhedron of `P` at all
times. -/
def openSimplicialNeighborhoodDeformation :
    (ContinuousMap.id (K.openSimplicialNeighborhood P)).HomotopyRel
      ((ContinuousMap.inclusion (K.setOf_support_mem_subset_openSimplicialNeighborhood P)).comp
        (K.openSimplicialNeighborhoodRetraction P))
      {y | (y : Realization K).1.support ∈ P} where
  toFun p := openStarHomeomorph K P
    ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).openStarDeformation {σ : Face K | σ.1 ∈ P}
        (p.1, (openStarHomeomorph K P).symm p.2))
  continuous_toFun := by fun_prop
  map_zero_left y := by simp
  map_one_left y := Subtype.ext (by simp [openSimplicialNeighborhoodRetraction])
  prop' t y hy := by
    have h := ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).openStarDeformation {σ : Face K | σ.1 ∈ P}).eq_fst t
        (x := (openStarHomeomorph K P).symm y) ?_
    · simp [h]
    · refine (support_barycentricSubdivisionRealizationMap_mem_iff K P _).1 ?_
      rw [← barycentricSubdivisionRealizationHomeomorph_apply]
      simpa using hy

/-- The deformation commutes with the subdivision homeomorphism: on the image of a point of the
open star of the face-vertices of `P`, it is the image of the open star deformation. -/
theorem openSimplicialNeighborhoodDeformation_barycentricSubdivisionRealizationMap
    (t : unitInterval)
    (x : (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).openStarRealizationSet {σ : Face K | σ.1 ∈ P}) :
    (K.openSimplicialNeighborhoodDeformation P
        (t, ⟨barycentricSubdivisionRealizationMap K x,
          (barycentricSubdivisionRealizationMap_mem_openSimplicialNeighborhood_iff K P x).2 x.2⟩) :
        Realization K) =
      barycentricSubdivisionRealizationMap K
        ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
          K.toPreAbstractSimplicialComplex).openStarDeformation {σ : Face K | σ.1 ∈ P} (t, x)) := by
  -- The deformation is, by definition, the open star deformation conjugated by the restricted
  -- subdivision homeomorphism.
  refine (congrArg (fun z => (openStarHomeomorph K P
    ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).openStarDeformation {σ : Face K | σ.1 ∈ P} (t, z)) :
        Realization K)) (openStarHomeomorph_symm_mk K P x)).trans ?_
  simp

end AbstractSimplicialComplex
