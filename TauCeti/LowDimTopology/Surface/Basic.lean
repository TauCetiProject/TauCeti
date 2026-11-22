/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.Geometry.Manifold.Basic
public import TauCeti.Geometry.Manifold.Boundary.Interior

/-!
# Surfaces with boundary and punctures

A *surface* in the sense of mapping class group theory is `Σ ∖ P`, where `Σ` is a compact connected
oriented Hausdorff second-countable topological 2-manifold with boundary and `P` is a finite set of
interior points of `Σ`, the punctures. This file records such a surface as the structure
`TauCeti.PuncturedSurface X` on a charted space `X` modelled on the half-plane
`EuclideanHalfSpace 2`: the topology and the boundary charts of `Σ = X` are the charted-space
structure, and the orientation is a homological orientation of the interior of `X`, a manifold
without boundary (`ModelWithCorners.instChartedSpaceInterior`). This is the orientation that, with
a collar of the boundary, gives the fundamental class of `X` relative to its boundary
(`TauCeti.HomologicalOrientation.fundamentalClassRel`).

The surface itself is the open subset `S.carrier = X ∖ P` of `X`. It is a charted space modelled
on the half-plane by restricting the charts of `X` (`TopologicalSpace.Opens.instChartedSpace`), and
it is oriented by restricting the orientation of `X`
(`TauCeti.PuncturedSurface.carrierOrientation`). Its manifold boundary is the boundary of `X`,
since the punctures are interior points (`TauCeti.PuncturedSurface.image_boundary_carrier`).

Genus, Euler characteristic, homology and the intersection form are not part of the structure:
they are invariants of it.

## Main definitions

* `ModelWithCorners.interiorOpensInclusion`: the inclusion of the interior of an open subset `u` of
  a manifold with corners `M` into the interior of `M`, an open embedding.
* `TauCeti.HomologicalOrientation.restrictOpens`: an orientation of the interior of `M` restricts
  to an orientation of the interior of every open subset of `M`.
* `TauCeti.PuncturedSurface X`: the data of a punctured compact connected oriented surface with
  boundary, with underlying compact surface `X`.
* `TauCeti.PuncturedSurface.carrier`: the surface `X ∖ P`, an open subset of `X`.
* `TauCeti.PuncturedSurface.carrierOrientation`: its orientation.
* `TauCeti.PuncturedSurface.numPunctures`: the number of punctures.

## Main results

* `TauCeti.PuncturedSurface.image_boundary_carrier`: the boundary of `X ∖ P` is the boundary of
  `X`.

## References

* B. Farb and D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press, 2012,
  Section 1.1.
* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, Invent. Math.
  221 (2020), Section 8.1.
-/

public section

noncomputable section

open Set Topology TopologicalSpace

open scoped Manifold

universe w

/-! ### Interiors of open subsets -/

namespace ModelWithCorners

variable {E H M : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]

/-- The inclusion of the interior of an open subset `u` of `M` into the interior of `M`: an
interior point of `u` is an interior point of `M` (`ModelWithCorners.interior_open`). -/
@[expose] def interiorOpensInclusion (u : Opens M) : I.interior u → I.interior M :=
  fun x ↦ ⟨x.val.val, by simpa only [interior_open, mem_preimage] using x.property⟩

@[simp]
theorem coe_interiorOpensInclusion (u : Opens M) (x : I.interior u) :
    (I.interiorOpensInclusion u x : M) = x.val.val :=
  rfl

/-- The inclusion of the interior of an open subset into the interior is an open embedding. -/
theorem isOpenEmbedding_interiorOpensInclusion [FiniteDimensional ℝ E] (u : Opens M) :
    IsOpenEmbedding (I.interiorOpensInclusion u) := by
  have h : IsOpenEmbedding (fun x : I.interior u ↦ x.val.val) :=
    u.isOpen.isOpenEmbedding_subtypeVal.comp
      (I.isOpen_interior_of_finiteDimensional u).isOpenEmbedding_subtypeVal
  exact ((I.isOpen_interior_of_finiteDimensional M).isOpenEmbedding_subtypeVal.of_comp_iff _).1 h

end ModelWithCorners

namespace TauCeti

namespace HomologicalOrientation

variable {E H M : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [T2Space M]
  [ChartedSpace H M] {d : ℕ}

/-- **The restriction of an orientation to an open subset.** An orientation of the interior of a
manifold with corners `M` restricts to an orientation of the interior of every open subset `u` of
`M`, by pulling it back along the inclusion of interiors. -/
@[expose] def restrictOpens (o : HomologicalOrientation (I.interior M) E d) (u : Opens M) :
    HomologicalOrientation (I.interior u) E d :=
  o.comap (I.isOpenEmbedding_interiorOpensInclusion u)

/-- Restricting the reversed orientation gives the reversed restriction. -/
@[simp]
theorem restrictOpens_neg (o : HomologicalOrientation (I.interior M) E d) (u : Opens M) :
    (-o).restrictOpens u = -o.restrictOpens u :=
  o.comap_neg _

end HomologicalOrientation

/-! ### Punctured surfaces -/

variable (X : Type) [TopologicalSpace X] [T2Space X] [ChartedSpace (EuclideanHalfSpace 2) X]

/-- **A surface with boundary and punctures**, `Σ ∖ P`. The underlying compact surface `Σ` is the
charted space `X`, modelled on the half-plane, so its boundary charts are actual topological
data; it is compact, connected, Hausdorff and second countable, and it carries an orientation,
a homological orientation of its interior. The punctures `P` form a finite set of interior points
of `X`. The surface itself is `TauCeti.PuncturedSurface.carrier`. -/
structure PuncturedSurface where
  /-- The underlying surface is compact, connected, Hausdorff and second countable. -/
  isCompactConnectedSurface : IsCompactConnectedSurface X
  /-- The orientation of the underlying surface, an orientation of its interior. -/
  orientation : HomologicalOrientation ((𝓡∂ 2).interior X) (EuclideanSpace ℝ (Fin 2)) 2
  /-- The punctures. -/
  punctures : Finset X
  /-- The punctures are interior points. -/
  punctures_subset_interior : (punctures : Set X) ⊆ (𝓡∂ 2).interior X

namespace PuncturedSurface

variable {X} (S : PuncturedSurface X)

/-- The surface `X ∖ P` obtained by removing the punctures, an open subset of `X`. It is a
charted space modelled on the half-plane by the restricted charts of `X`. -/
@[expose] def carrier : Opens X :=
  ⟨(S.punctures : Set X)ᶜ, S.punctures.finite_toSet.isClosed.isOpen_compl⟩

@[simp]
theorem mem_carrier {x : X} : x ∈ S.carrier ↔ x ∉ S.punctures :=
  Iff.rfl

@[simp]
theorem coe_carrier : (S.carrier : Set X) = (S.punctures : Set X)ᶜ :=
  rfl

/-- The number of punctures. -/
@[expose] def numPunctures : ℕ :=
  S.punctures.card

theorem numPunctures_def : S.numPunctures = S.punctures.card :=
  rfl

/-- The orientation of the surface `X ∖ P`, the restriction of the orientation of `X`. -/
@[expose] def carrierOrientation :
    HomologicalOrientation ((𝓡∂ 2).interior S.carrier) (EuclideanSpace ℝ (Fin 2)) 2 :=
  S.orientation.restrictOpens S.carrier

theorem carrierOrientation_def :
    S.carrierOrientation = S.orientation.restrictOpens S.carrier :=
  rfl

/-- **The boundary of `X ∖ P` is the boundary of `X`.** The punctures are interior points, so
every boundary point of `X` lies in `X ∖ P`, where it is a boundary point. -/
theorem image_boundary_carrier :
    Subtype.val '' (𝓡∂ 2).boundary S.carrier = (𝓡∂ 2).boundary X := by
  rw [ModelWithCorners.boundary_open, image_preimage_eq_inter_range, Subtype.range_coe,
    inter_eq_left]
  intro x hx hP
  exact ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).1
    (S.punctures_subset_interior hP) hx

/-- The surface with the reversed orientation. -/
@[expose] def reverse : PuncturedSurface X where
  isCompactConnectedSurface := S.isCompactConnectedSurface
  orientation := -S.orientation
  punctures := S.punctures
  punctures_subset_interior := S.punctures_subset_interior

@[simp]
theorem orientation_reverse : S.reverse.orientation = -S.orientation :=
  rfl

@[simp]
theorem punctures_reverse : S.reverse.punctures = S.punctures :=
  rfl

@[simp]
theorem carrierOrientation_reverse : S.reverse.carrierOrientation = -S.carrierOrientation :=
  HomologicalOrientation.restrictOpens_neg _ _

end PuncturedSurface

end TauCeti
