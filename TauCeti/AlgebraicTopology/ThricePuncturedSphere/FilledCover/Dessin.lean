/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.BranchPoints
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Edges
public import TauCeti.Analysis.Convex.Topology
public import TauCeti.Combinatorics.RibbonGraph.OfPermutationTriple

/-!
# The embedded dessin of a filled cover

The preimage of the closed real segment from zero to one is the union of the closed edges
of the dessin. Under the bijections from the fibres over zero and one to the black and white
vertices of the monodromy ribbon graph, the two endpoints of each edge are precisely its
`blackEnd` and `whiteEnd`. These identifications describe incidence even when several edges
join the same pair of vertices. For any such pair, `edgesBetweenEquiv` restricts the
sheet numbering to a bijection with the segment components incident to both vertices.
-/

public noncomputable section

namespace TauCeti.FilledCover

open Set Topology ThricePuncturedSphere PunctureFilling FilledPoint

variable {E : Type*} [TopologicalSpace E] {p : E → ThricePuncturedSphere}
  (hp : IsCoveringMap p) {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n)

/-- A closed edge projects into the closed segment on the sphere. In particular no edge
accumulates over infinity. -/
theorem closure_edge_subset_preimage_segment (i : Fin n) :
    closure (edge hp ν i) ⊆ fillMap p ⁻¹' (((↑) : ℂ → OnePoint ℂ) '' segment ℝ 0 1) := by
  have hs := ((isCompact_segment ℝ (0 : ℂ) 1).image OnePoint.continuous_coe).isClosed
  apply closure_minimal _ (hs.preimage (continuous_fillMap hp (.of_equiv _ ν.symm)))
  intro z hz
  obtain ⟨x, hx, -, rfl⟩ := (mem_edge_iff hp ν i z).1 hz
  rw [mem_preimage, fillMap_incl, toOnePoint_apply, OnePoint.coe_injective.mem_set_image]
  exact (Set.ext_iff.mp preimage_segment_zero_one (p x)).2 hx

/-- The closure of a sheet's open edge consists of the edge and its black and white endpoints
in the monodromy ribbon graph, identified with points of the two marked fibres. -/
theorem closure_edge (i : Fin n) :
    closure (edge hp ν i) =
      insert ((fiberZeroEquivSameCycleQuotient hp ν).symm
        ((hp.monodromyTriple ν).ribbonGraph.blackEnd i) : FilledCover p)
        (insert ((fiberOneEquivSameCycleQuotient hp ν).symm
          ((hp.monodromyTriple ν).ribbonGraph.whiteEnd i) : FilledCover p) (edge hp ν i)) := by
  simp only [PermutationTriple.blackEnd_ribbonGraph, PermutationTriple.whiteEnd_ribbonGraph,
    coe_fiberZeroEquivSameCycleQuotient_symm_apply, coe_fiberOneEquivSameCycleQuotient_symm_apply]
  refine Subset.antisymm ?_ (insert_subset_iff.2 ⟨(center_overZero_mem_closure_edge_iff ..).2 rfl,
    insert_subset_iff.2 ⟨(center_overOne_mem_closure_edge_iff ..).2 rfl, subset_closure⟩⟩)
  intro z
  induction z using PunctureFilling.induction with
  | incl x => exact fun hx ↦ Or.inr (Or.inr ((incl_mem_closure_edge_iff hp ν i x).1 hx))
  | center j =>
    rcases FilledPoint.cases p j with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · intro hc
      rw [(center_overZero_mem_closure_edge_iff hp ν i c).1 hc]
      exact Or.inl rfl
    · intro hc
      rw [(center_overOne_mem_closure_edge_iff hp ν i c).1 hc]
      exact Or.inr (Or.inl rfl)
    · intro hc
      have h := closure_edge_subset_preimage_segment hp ν i hc
      simp at h

/-- The closed edges of the monodromy dessin cover exactly the preimage of the closed real
segment from zero to one. -/
theorem preimage_segment_eq_iUnion_closure_edge :
    fillMap p ⁻¹' (((↑) : ℂ → OnePoint ℂ) '' segment ℝ 0 1) = ⋃ i, closure (edge hp ν i) := by
  refine Subset.antisymm ?_ (iUnion_subset (closure_edge_subset_preimage_segment hp ν))
  intro z
  induction z using PunctureFilling.induction with
  | incl x =>
    intro hx
    have hx' : p x ∈ unitSegment := by
      rw [← preimage_segment_zero_one]
      simpa only [mem_preimage, fillMap_incl, toOnePoint_apply,
        OnePoint.coe_injective.mem_set_image] using hx
    obtain ⟨i, hi⟩ := (hp.finEquivConnectedComponentsUnitSegment ν).surjective
      (ConnectedComponents.mk ⟨x, hx'⟩)
    exact mem_iUnion.2 ⟨i, subset_closure ((incl_mem_edge_iff hp ν i x).2 ⟨hx', hi.symm⟩)⟩
  | center j =>
    rcases FilledPoint.cases p j with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · obtain ⟨b, rfl⟩ := (hp.sameCycleQuotientσ0EquivConnectedComponents ν).surjective c
      obtain ⟨i, rfl⟩ := Quotient.mk_surjective b
      exact fun _ ↦ mem_iUnion.2 ⟨i, (center_overZero_mem_closure_edge_iff ..).2 rfl⟩
    · obtain ⟨w, rfl⟩ := (hp.sameCycleQuotientσ1EquivConnectedComponents ν).surjective c
      obtain ⟨i, rfl⟩ := Quotient.mk_surjective w
      exact fun _ ↦ mem_iUnion.2 ⟨i, (center_overOne_mem_closure_edge_iff ..).2 rfl⟩
    · simp

/-- For fixed vertices over zero and one, the edges between their monodromy cycles correspond
bijectively to the components over the open segment whose closures contain both vertices. -/
def edgesBetweenEquiv (b : fillMap p ⁻¹' {((0 : ℂ) : OnePoint ℂ)})
    (w : fillMap p ⁻¹' {((1 : ℂ) : OnePoint ℂ)}) :
    {i : (hp.monodromyTriple ν).ribbonGraph.E //
      (hp.monodromyTriple ν).ribbonGraph.blackEnd i = fiberZeroEquivSameCycleQuotient hp ν b ∧
      (hp.monodromyTriple ν).ribbonGraph.whiteEnd i = fiberOneEquivSameCycleQuotient hp ν w} ≃
    {c : ConnectedComponents (p ⁻¹' unitSegment) //
      (b : FilledCover p) ∈ closure (incl (chart p) '' c.carrierIn) ∧
      (w : FilledCover p) ∈ closure (incl (chart p) '' c.carrierIn)} :=
  (hp.finEquivConnectedComponentsUnitSegment ν).subtypeEquiv fun i ↦ by
    obtain ⟨v, rfl⟩ := (fiberZeroEquivSameCycleQuotient hp ν).symm.surjective b
    obtain ⟨v', rfl⟩ := (fiberOneEquivSameCycleQuotient hp ν).symm.surjective w
    simp only [← edge_eq_image_carrierIn, PermutationTriple.blackEnd_ribbonGraph,
      PermutationTriple.whiteEnd_ribbonGraph, Equiv.apply_symm_apply,
      coe_fiberZeroEquivSameCycleQuotient_symm_apply, coe_fiberOneEquivSameCycleQuotient_symm_apply,
      center_overZero_mem_closure_edge_iff, center_overOne_mem_closure_edge_iff,
      Equiv.apply_eq_iff_eq]
    exact and_congr eq_comm eq_comm

/-- An incident sheet maps to its component over the open segment. -/
@[simp] theorem coe_edgesBetweenEquiv_apply (b w i) :
    ↑(edgesBetweenEquiv hp ν b w i) = hp.finEquivConnectedComponentsUnitSegment ν i.val :=
  (rfl)

/-- The inverse incidence bijection reads off the sheet of a segment component. -/
@[simp] theorem coe_edgesBetweenEquiv_symm_apply (b w c) :
    ((edgesBetweenEquiv hp ν b w).symm c : (hp.monodromyTriple ν).ribbonGraph.E) =
      (hp.finEquivConnectedComponentsUnitSegment ν).symm c.val :=
  (rfl)

end TauCeti.FilledCover
