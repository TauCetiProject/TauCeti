/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Hole

/-!
# The boundary of a finite simply connected region is preconnected

For a finite simply connected region `R` of the triangular lattice, the boundary graph
`boundaryGraph R` (the boundary vertices `∂R`, joined along the boundary edges) is preconnected
(`TauCeti.IsSimplyConnectedRegion.preconnected_boundaryGraph`): any two boundary vertices are
joined by a path of boundary edges.

The route goes through functions on the vertices
(`TauCeti.IsSimplyConnectedRegion.eq_of_forall_boundaryEdges`): if `h` takes equal values at the
two endpoints of every boundary edge of `R`, then `h` is constant on `∂R`. Indeed, the cochain equal
to the coboundary of `h` on the edges of `R` and to `0` elsewhere is closed on the whole plane:
on a face outside `R`, each edge is either not an edge of `R` or a boundary edge of `R`, and the
cochain vanishes there. The plane is simply connected, so the cochain has a primitive `G` on the
plane. `G` is constant on each face outside `R`, hence, the faces outside `R` being connected
through shared edges (`TauCeti.IsSimplyConnectedRegion.connected_induce_compl`), constant on all
their vertices, which include `∂R`. On `R`, which is connected, `G` and `h` are primitives of the
same cochain, so they differ by a constant on the vertices of `R`, and `h` is constant on `∂R`.
Applied to the indicator of a component of the boundary graph, this gives preconnectedness.

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. 198 (2023),
  Section 1.2.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 1.
-/

public section

namespace TauCeti

variable {R : Set TriFace}

/-- On a face outside `R`, the cochain equal to the coboundary of `h` on the edges of `R` and to
`0` elsewhere vanishes, when `h` takes equal values at the endpoints of each boundary edge. -/
private theorem boundaryCochain_eq_zero {h : ℤ × ℤ → ℤ}
    (hh : ∀ e ∈ boundaryEdges R, h e.target = h e.v) {f : TriFace} (hf : f ∉ R) {e : TriEdge}
    (he : e ∈ f.edges) :
    (open Classical in if e ∈ regionEdges R then h e.target - h e.v else 0) = 0 := by
  split_ifs with heR
  · rw [hh e (mem_boundaryEdges.2 ⟨heR, f, hf, he⟩), sub_self]
  · rfl

/-- **Functions constant along the boundary are constant on the boundary.** Let `R` be a finite
simply connected region and `h : ℤ × ℤ → ℤ` take equal values at the two endpoints of every
boundary edge of `R`. Then `h` is constant on the boundary vertices `∂R`. -/
theorem IsSimplyConnectedRegion.eq_of_forall_boundaryEdges (hR : IsSimplyConnectedRegion R)
    (hfin : R.Finite) {h : ℤ × ℤ → ℤ} (hh : ∀ e ∈ boundaryEdges R, h e.target = h e.v)
    {u u' : ℤ × ℤ} (hu : u ∈ boundaryVertices R) (hu' : u' ∈ boundaryVertices R) :
    h u = h u' := by
  classical
  set c : TriEdge → ℤ := fun e => if e ∈ regionEdges R then h e.target - h e.v else 0 with hc
  have hout (f : TriFace) (hf : f ∉ R) (e : TriEdge) (he : e ∈ f.edges) : c e = 0 := by
    simpa only [hc] using boundaryCochain_eq_zero hh hf he
  -- the cochain is closed on the plane, hence exact
  have hclosed : IsClosedCochainOn Set.univ c := by
    refine isClosedCochainOn_def.2 fun f _ => ?_
    by_cases hf : f ∈ R
    · have hin (k : Fin 3) : c (f.edge k) = h (f.edge k).target - h (f.edge k).v :=
        by simp [hc, edges_subset_regionEdges hf (f.edge_mem_edges k)]
      rw [hin, hin, hin]
      exact isClosedCochainOn_def.1 (isClosedCochainOn_coboundary Set.univ h) f (Set.mem_univ f)
    · simp only [hout f hf _ (f.edge_mem_edges _), add_zero]
  obtain ⟨G, hG⟩ := isExactCochainOn_def.1 hclosed.isExactCochainOn_univ
  -- `G` is constant on the vertices of each face outside `R`, where `c` vanishes
  have hface {f : TriFace} (hf : f ∉ R) {x y : ℤ × ℤ} (hx : x ∈ f.vertices)
      (hy : y ∈ f.vertices) : G x = G y := by
    simpa using (isConnectedRegion_singleton f).sub_eq_sub_of_isCochainPrimitiveOn
      (g' := fun _ => 0) (hG.mono (Set.subset_univ _))
      (isCochainPrimitiveOn_singleton.2 fun e he => by simpa using hout f hf e he)
      (by simpa using hx) (by simpa using hy)
  -- hence on the vertices of all faces outside `R`
  have hcompl : ∀ a b : (Rᶜ : Set TriFace), (hexGraph.induce Rᶜ).Reachable a b →
      ∀ x ∈ (a : TriFace).vertices, ∀ y ∈ (b : TriFace).vertices, G x = G y := by
    intro a b ⟨p⟩
    induction p with
    | @nil a => exact fun x hx y hy => hface a.property hx hy
    | @cons a b _ hab _ ih =>
      intro x hx y hy
      obtain ⟨-, e, hea, heb⟩ := hexGraph_adj.1 (SimpleGraph.induce_adj.1 hab)
      exact (hface a.property hx (TriFace.v_mem_vertices_of_mem_edges hea)).trans
        (ih _ (TriFace.v_mem_vertices_of_mem_edges heb) y hy)
  have hbdry {x : ℤ × ℤ} (hx : x ∈ boundaryVertices R) :
      ∃ f : (Rᶜ : Set TriFace), x ∈ (f : TriFace).vertices := by
    obtain ⟨e, he, hxe⟩ := mem_boundaryVertices.1 hx
    obtain ⟨-, f, hf, hef⟩ := mem_boundaryEdges.1 he
    exact ⟨⟨f, hf⟩, TriFace.mem_vertices_of_mem_endpoints hef hxe⟩
  obtain ⟨a, ha⟩ := hbdry hu
  obtain ⟨b, hb⟩ := hbdry hu'
  have hGuu' : G u = G u' :=
    hcompl a b ((hR.connected_induce_compl hfin).preconnected a b) u ha u' hb
  -- on `R`, `G` and `h` are primitives of the same cochain
  have hhR : IsCochainPrimitiveOn R c h := isCochainPrimitiveOn_def.2 fun e he => by simp [hc, he]
  have := hR.isConnectedRegion.sub_eq_sub_of_isCochainPrimitiveOn (hG.mono (Set.subset_univ R))
    hhR (boundaryVertices_subset_regionVertices hu) (boundaryVertices_subset_regionVertices hu')
  omega

/-- **The boundary graph of a finite simply connected region is preconnected**: any two boundary
vertices are joined by a path of boundary edges. -/
theorem IsSimplyConnectedRegion.preconnected_boundaryGraph (hR : IsSimplyConnectedRegion R)
    (hfin : R.Finite) : (boundaryGraph R).Preconnected := by
  classical
  intro u u'
  by_contra hne
  let h : ℤ × ℤ → ℤ := fun x =>
    if ∃ hx : x ∈ boundaryVertices R, (boundaryGraph R).Reachable u ⟨x, hx⟩ then 1 else 0
  have hh : ∀ e ∈ boundaryEdges R, h e.target = h e.v := by
    intro e he
    have hadj : (boundaryGraph R).Adj ⟨e.v, v_mem_boundaryVertices he⟩
        ⟨e.target, target_mem_boundaryVertices he⟩ :=
      boundaryGraph_adj.2 ⟨e, he, TriEdge.endpoints_def e⟩
    have hiff : (∃ hx : e.target ∈ boundaryVertices R, (boundaryGraph R).Reachable u ⟨_, hx⟩) ↔
        ∃ hx : e.v ∈ boundaryVertices R, (boundaryGraph R).Reachable u ⟨_, hx⟩ :=
      ⟨fun ⟨_, hr⟩ => ⟨v_mem_boundaryVertices he, hr.trans hadj.symm.reachable⟩,
        fun ⟨_, hr⟩ => ⟨target_mem_boundaryVertices he, hr.trans hadj.reachable⟩⟩
    simp only [h, hiff]
  have h₁ : h u = 1 := by simp [h, u.property]
  have h₀ : h u' = 0 := by simp [h, hne]
  have := hR.eq_of_forall_boundaryEdges hfin hh u.property u'.property
  omega

end TauCeti
