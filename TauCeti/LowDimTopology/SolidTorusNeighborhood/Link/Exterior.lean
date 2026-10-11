/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Sigma
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Exterior
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Link.Basic

/-!
# Link exteriors from disjoint solid-torus neighbourhoods

The exterior of a link is the complement of the open solid tori of a family of pairwise disjoint
solid-torus neighbourhoods of its components (`TauCeti.IsSolidTorusLinkNeighborhood`). This file
names that complement and shows that, after shrinking every solid torus to half its radius, it is
a topological manifold with boundary whose manifold boundary is the union of the boundary tori,
one for each component.

The construction is the knot case (`TauCeti.IsSolidTorusNeighborhood.exteriorChartedSpace`) run on
all components at once. Each half-radius boundary torus has the bicollar
`TauCeti.halveBicollar (Φ i)` swept out by the annuli of `Φ i`, inside the image of `Φ i`. Since
the solid tori are pairwise disjoint, these bicollars assemble into one bicollar of the disjoint
union `Σ i, S¹ × S¹` of the boundary tori (`TauCeti.IsBicollar.sigma`), charted on `ℝ²` through
`ChartedSpace.sigma`. The link exterior is the outer side of that bicollar, so
`TauCeti.IsBicollar.sideChartedSpace` charts it on the half-space `EuclideanHalfSpace 3`. Finitely
many components are needed for the exterior to be open away from the boundary tori.

## Main definitions

* `TauCeti.linkExterior Φ`: the complement of the open solid tori of a family `Φ`.
* `TauCeti.IsSolidTorusLinkNeighborhood.exteriorChartedSpace`: the exterior of the half-radius
  neighbourhoods of a finite link in a Hausdorff topological `3`-manifold, charted on the
  Euclidean half-space.
* `TauCeti.IsSolidTorusLinkNeighborhood.boundaryHomeomorph`: the manifold boundary of that
  exterior is homeomorphic to `Σ i, S¹ × S¹`, one torus for each component.

## Main results

* `TauCeti.IsSolidTorusLinkNeighborhood.isCompact_linkExterior`: in a compact ambient space the
  link exterior is compact.
* `TauCeti.IsSolidTorusLinkNeighborhood.frontier_linkExterior`: for a finite link in a Hausdorff
  space, the frontier of the exterior is the union of the boundary tori.
* `TauCeti.IsSolidTorusLinkNeighborhood.isBicollared_comp_halve_comp_boundaryInclusion`: the
  half-radius boundary tori are jointly bicollared.
* `TauCeti.IsSolidTorusLinkNeighborhood.boundary_exteriorChartedSpace` and
  `TauCeti.IsSolidTorusLinkNeighborhood.interior_exteriorChartedSpace`: the manifold boundary of
  the exterior is the union of the half-radius boundary tori, and its manifold interior is the
  complement of the closed half-radius solid tori.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Sections 2E and 9F (link exteriors and
  their boundary tori, the setting of Dehn surgery on links).
-/

public section

open Set Topology Function
open scoped Manifold

namespace TauCeti

variable {ι X : Type*}

/-- The closed exterior of a family of solid-torus neighbourhoods: the complement of the union of
their open solid-torus images, that is, the intersection of their knot exteriors. -/
def linkExterior (Φ : ι → SolidTorus → X) : Set X :=
  ⋂ i, knotExterior (Φ := Φ i)

/-- The link exterior is the intersection of the knot exteriors of its solid tori. -/
theorem linkExterior_def (Φ : ι → SolidTorus → X) :
    linkExterior Φ = ⋂ i, knotExterior (Φ := Φ i) :=
  (rfl)

/-- A point is in the link exterior when it is outside every open solid torus. -/
@[simp]
theorem mem_linkExterior {Φ : ι → SolidTorus → X} {x : X} :
    x ∈ linkExterior Φ ↔ ∀ i, x ∉ Φ i '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} := by
  simp only [linkExterior, mem_iInter, mem_knotExterior]

/-- The exterior of a one-component link is the knot exterior of its solid torus. -/
theorem linkExterior_unique [Unique ι] (Φ : ι → SolidTorus → X) :
    linkExterior Φ = knotExterior (Φ := Φ default) := by
  ext x
  simp [Unique.forall_iff]

/-- The link exterior, with its boundary tori removed, is the complement of the closed solid
tori. -/
theorem linkExterior_sdiff_iUnion_range (Φ : ι → SolidTorus → X) :
    linkExterior Φ \ ⋃ i, range (Φ i ∘ SolidTorus.boundaryInclusion) = (⋃ i, range (Φ i))ᶜ := by
  rw [linkExterior, sdiff_eq, compl_iUnion, ← iInter_inter_distrib, compl_iUnion]
  exact iInter_congr fun i => by rw [← sdiff_eq, knotExterior_sdiff_range]

namespace IsSolidTorusLinkNeighborhood

variable [TopologicalSpace X] {f : ι → Circle → X} {Φ : ι → SolidTorus → X}

/-- The link exterior is closed in any ambient topological space. -/
theorem isClosed_linkExterior (h : IsSolidTorusLinkNeighborhood f Φ) :
    IsClosed (linkExterior Φ) :=
  isClosed_iInter fun i => (h.neighborhood i).isClosed_exterior

/-- In a compact ambient space, the link exterior is compact. -/
theorem isCompact_linkExterior [CompactSpace X] (h : IsSolidTorusLinkNeighborhood f Φ) :
    IsCompact (linkExterior Φ) :=
  h.isClosed_linkExterior.isCompact

/-- For a finite link in a Hausdorff space, the frontier of the link exterior is the union of
the boundary tori. -/
theorem frontier_linkExterior [T2Space X] [Finite ι] (h : IsSolidTorusLinkNeighborhood f Φ) :
    frontier (linkExterior Φ) = ⋃ i, range (Φ i ∘ SolidTorus.boundaryInclusion) := by
  set U : ι → Set X := fun i => Φ i '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1}
  have hU : linkExterior Φ = (⋃ i, U i)ᶜ := by ext; simp [U]
  have hfr (i : ι) : range (Φ i ∘ SolidTorus.boundaryInclusion) = closure (U i) \ U i := by
    rw [← (h.neighborhood i).frontier_image, (h.neighborhood i).isOpen_image.frontier_eq]
  -- The closure of each open solid torus lies in the closed solid torus, which is disjoint from
  -- the other open solid tori.
  have hcl (i : ι) : closure (U i) ⊆ range (Φ i) :=
    closure_minimal (image_subset_range _ _) (h.neighborhood i).isClosedEmbedding.isClosed_range
  rw [hU, frontier_compl, (isOpen_iUnion fun i => (h.neighborhood i).isOpen_image).frontier_eq,
    closure_iUnion_of_finite]
  simp_rw [hfr]
  ext x
  simp only [mem_sdiff, mem_iUnion, not_exists]
  refine ⟨fun ⟨⟨i, hi⟩, hx⟩ => ⟨i, hi, hx i⟩, fun ⟨i, hi, hx⟩ => ⟨⟨i, hi⟩, fun j => ?_⟩⟩
  obtain rfl | hij := eq_or_ne j i
  · exact hx
  · exact fun hj => (h.pairwiseDisjoint_range hij).ne_of_mem (image_subset_range _ _ hj)
      (hcl i hi) rfl

/-- Shrinking every solid torus to half its radius gives disjoint solid-torus neighbourhoods
again. -/
theorem comp_halve (h : IsSolidTorusLinkNeighborhood f Φ) :
    IsSolidTorusLinkNeighborhood f fun i => Φ i ∘ SolidTorus.halve where
  neighborhood i := (h.neighborhood i).comp_halve
  pairwiseDisjoint_range _ _ hij :=
    (h.pairwiseDisjoint_range hij).mono (range_comp_subset_range _ _)
      (range_comp_subset_range _ _)

/-- The bicollars `TauCeti.halveBicollar (Φ i)` of the half-radius boundary tori assemble into a
bicollar of the disjoint union of those tori. -/
private theorem isBicollar_sigma (h : IsSolidTorusLinkNeighborhood f Φ) :
    IsBicollar (fun x : Σ _ : ι, Circle × Circle =>
        (Φ x.1 ∘ SolidTorus.halve ∘ SolidTorus.boundaryInclusion) x.2)
      fun p => halveBicollar (Φ p.1.1) (p.1.2, p.2) :=
  IsBicollar.sigma (fun i => (h.neighborhood i).isBicollar_halveBicollar) fun _ _ hij =>
    (h.pairwiseDisjoint_range hij).mono (range_halveBicollar_subset _)
      (range_halveBicollar_subset _)

/-- The half-radius boundary tori of a link neighbourhood are jointly bicollared: their disjoint
union `Σ i, S¹ × S¹` has a bicollar in the ambient space. -/
theorem isBicollared_comp_halve_comp_boundaryInclusion (h : IsSolidTorusLinkNeighborhood f Φ) :
    IsBicollared fun x : Σ _ : ι, Circle × Circle =>
      (Φ x.1 ∘ SolidTorus.halve ∘ SolidTorus.boundaryInclusion) x.2 :=
  h.isBicollar_sigma.isBicollared

private theorem preimage_linkExterior_halve (h : IsSolidTorusLinkNeighborhood f Φ) :
    (fun p : (Σ _ : ι, Circle × Circle) × ℝ => halveBicollar (Φ p.1.1) (p.1.2, p.2)) ⁻¹'
      linkExterior (fun i => Φ i ∘ SolidTorus.halve) = univ ×ˢ Ici 0 := by
  ext ⟨⟨i, q⟩, t⟩
  have hi := congrArg ((q, t) ∈ ·) (h.neighborhood i).preimage_halveBicollar_knotExterior
  simp only [mem_preimage, eq_iff_iff] at hi
  simp only [mem_preimage, linkExterior, mem_iInter, mem_prod, mem_univ, true_and] at hi ⊢
  refine ⟨fun hx => hi.1 (hx i), fun ht j => ?_⟩
  obtain rfl | hij := eq_or_ne j i
  · exact hi.2 ht
  · -- The bicollar of the `i`-th torus lies in the `i`-th solid torus, disjoint from the `j`-th.
    rw [mem_knotExterior]
    rintro ⟨p, -, hp⟩
    exact (h.pairwiseDisjoint_range hij).ne_of_mem (mem_range_self (SolidTorus.halve p))
      (range_halveBicollar_subset _ (mem_range_self (q, t))) hp

/-- The half-radius boundary tori lie in the exterior of the half-radius solid tori. -/
private theorem mem_linkExterior_halve (h : IsSolidTorusLinkNeighborhood f Φ)
    (x : Σ _ : ι, Circle × Circle) :
    (Φ x.1 ∘ SolidTorus.halve ∘ SolidTorus.boundaryInclusion) x.2 ∈
      linkExterior fun i => Φ i ∘ SolidTorus.halve := by
  have hx : (x, (0 : ℝ)) ∈ univ ×ˢ Ici 0 := ⟨trivial, le_rfl⟩
  rw [← h.preimage_linkExterior_halve, mem_preimage] at hx
  rwa [← h.isBicollar_sigma.apply_zero]

private theorem isOpen_linkExterior_halve_sdiff_range [T2Space X] [Finite ι]
    (h : IsSolidTorusLinkNeighborhood f Φ) :
    IsOpen (linkExterior (fun i => Φ i ∘ SolidTorus.halve) \
      range fun x : Σ _ : ι, Circle × Circle =>
        (Φ x.1 ∘ SolidTorus.halve ∘ SolidTorus.boundaryInclusion) x.2) := by
  rw [range_sigma_eq_iUnion_range]
  simp_rw [← Function.comp_assoc (Φ _)]
  rw [linkExterior_sdiff_iUnion_range]
  exact (isClosed_iUnion_of_finite fun i =>
    (h.comp_halve.neighborhood i).isClosedEmbedding.isClosed_range).isOpen_compl

variable [T2Space X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [Finite ι]

/-- The exterior of the half-radius solid tori of a finite link neighbourhood, in a Hausdorff
topological `3`-manifold, as a topological manifold with boundary: it is the outer side of the
joint bicollar of its boundary tori, charted by `TauCeti.IsBicollar.sideChartedSpace`. Its
manifold boundary is the union of the boundary tori
(`TauCeti.IsSolidTorusLinkNeighborhood.boundary_exteriorChartedSpace`). -/
@[instance_reducible]
noncomputable def exteriorChartedSpace (h : IsSolidTorusLinkNeighborhood f Φ) :
    ChartedSpace (EuclideanHalfSpace 3) (linkExterior fun i => Φ i ∘ SolidTorus.halve) :=
  letI := torusChartedSpace
  h.isBicollar_sigma.sideChartedSpace (n := 2) h.preimage_linkExterior_halve
    h.isOpen_linkExterior_halve_sdiff_range

/-- The manifold boundary of the exterior of the half-radius solid tori of a finite link is the
union of their boundary tori, one for each component. -/
theorem boundary_exteriorChartedSpace (h : IsSolidTorusLinkNeighborhood f Φ) :
    letI := h.exteriorChartedSpace
    (𝓡∂ 3).boundary (linkExterior fun i => Φ i ∘ SolidTorus.halve) =
      Subtype.val ⁻¹' ⋃ i, range (Φ i ∘ SolidTorus.halve ∘ SolidTorus.boundaryInclusion) := by
  let := torusChartedSpace
  rw [h.isBicollar_sigma.boundary_sideChartedSpace (n := 2) h.preimage_linkExterior_halve
    h.isOpen_linkExterior_halve_sdiff_range, range_sigma_eq_iUnion_range]

/-- The manifold interior of the exterior of the half-radius solid tori of a finite link is the
complement of the closed half-radius solid tori. -/
theorem interior_exteriorChartedSpace (h : IsSolidTorusLinkNeighborhood f Φ) :
    letI := h.exteriorChartedSpace
    (𝓡∂ 3).interior (linkExterior fun i => Φ i ∘ SolidTorus.halve) =
      Subtype.val ⁻¹' (⋃ i, range (Φ i ∘ SolidTorus.halve))ᶜ := by
  let := h.exteriorChartedSpace
  rw [← ModelWithCorners.compl_boundary, h.boundary_exteriorChartedSpace, ← preimage_compl,
    ← linkExterior_sdiff_iUnion_range, sdiff_eq, preimage_inter, Subtype.coe_preimage_self,
    univ_inter]
  simp_rw [Function.comp_assoc]

/-- The manifold boundary of the exterior of the half-radius solid tori of a finite link is a
disjoint union of tori, one for each component: the `i`-th copy of `S¹ × S¹` parametrizes the
`i`-th half-radius boundary torus through the framing `Φ i`. -/
noncomputable def boundaryHomeomorph (h : IsSolidTorusLinkNeighborhood f Φ) :
    letI := h.exteriorChartedSpace
    (Σ _ : ι, Circle × Circle) ≃ₜ (𝓡∂ 3).boundary (linkExterior fun i => Φ i ∘ SolidTorus.halve) :=
  letI := h.exteriorChartedSpace
  (h.isBicollar_sigma.isEmbedding.codRestrict _ h.mem_linkExterior_halve).toHomeomorph.trans
    (Homeomorph.setCongr (by
      rw [h.boundary_exteriorChartedSpace, range_codRestrict, range_sigma_eq_iUnion_range]))

/-- The boundary parametrization sends `⟨i, q⟩` to the point `Φ i (q₁ / 2, q₂)` of the `i`-th
half-radius boundary torus. -/
@[simp]
theorem coe_boundaryHomeomorph_apply (h : IsSolidTorusLinkNeighborhood f Φ)
    (x : Σ _ : ι, Circle × Circle) :
    ((h.boundaryHomeomorph x : linkExterior fun i => Φ i ∘ SolidTorus.halve) : X) =
      Φ x.1 (SolidTorus.halve (SolidTorus.boundaryInclusion x.2)) :=
  (rfl)

end IsSolidTorusLinkNeighborhood

end TauCeti
