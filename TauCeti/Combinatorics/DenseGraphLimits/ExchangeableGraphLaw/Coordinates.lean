/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Measurable

/-!
# Edge coordinates of an infinite simple graph

An infinite simple graph is equivalently a Boolean assignment to the unordered, non-diagonal
pairs of natural numbers.  This file makes that equivalence measurable and records its
equivariance under relabelling.  It is the carrier-level bridge between laws on infinite simple
graphs and laws on jointly exchangeable symmetric, irreflexive Boolean arrays.

The coordinate type excludes diagonal pairs, rather than imposing an irreflexivity condition on a
two-dimensional array.  Consequently every Boolean assignment is a graph, and relabelling acts by
an honest equivalence of coordinates.

## Main definitions

* `TauCeti.DenseGraphLimits.EdgeIndex` is the type of unordered non-diagonal pairs of naturals;
* `TauCeti.DenseGraphLimits.graphCoordEquiv` identifies infinite graphs with Boolean edge
  coordinates;
* `TauCeti.DenseGraphLimits.edgeIndexMap` is the coordinate relabelling induced by a permutation
  of the vertices.

## Main results

* `TauCeti.DenseGraphLimits.measurable_graphCoordEquiv` and
  `TauCeti.DenseGraphLimits.measurable_graphCoordEquiv_symm` show that the coordinate equivalence
  is measurable in both directions;
* `TauCeti.DenseGraphLimits.graphCoordEquiv_comap` is the relabelling commuting square.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 4.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0,
  `Graphon/InfiniteGraph.lean`.  The off-diagonal coordinate representation and relabelling square
  follow that source, adapted here to Mathlib's existing measurable space on `SimpleGraph ℕ`.
-/

public section

noncomputable section

namespace TauCeti

namespace DenseGraphLimits

/-- The coordinate type of an infinite simple graph: unordered pairs of distinct naturals. -/
abbrev EdgeIndex : Type := {e : Sym2 ℕ // ¬ e.IsDiag}

open Classical in
/-- An infinite simple graph is equivalently a Boolean assignment to its possible edges. -/
def graphCoordEquiv : SimpleGraph ℕ ≃ (EdgeIndex → Bool) where
  toFun G e := if e.1 ∈ G.edgeSet then true else false
  invFun f := SimpleGraph.fromEdgeSet {s : Sym2 ℕ | ∃ h : ¬ s.IsDiag, f ⟨s, h⟩ = true}
  left_inv G := by
    -- The coordinate predicate cuts out exactly `G.edgeSet`, so `fromEdgeSet_edgeSet` applies.
    refine Eq.trans ?_ (SimpleGraph.fromEdgeSet_edgeSet G)
    refine congrArg SimpleGraph.fromEdgeSet (Set.ext fun s => ?_)
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun h => ?_, fun hs => ⟨G.not_isDiag_of_mem_edgeSet hs, by simp [hs]⟩⟩
    by_contra hnot
    simp [hnot] at h
  right_inv f := by
    funext e
    have hcond :
        ((∃ h : ¬(e : Sym2 ℕ).IsDiag, f ⟨e, h⟩ = true) ∧ ¬(e : Sym2 ℕ).IsDiag) ↔
          f e = true := by
      constructor
      · rintro ⟨⟨h, htrue⟩, -⟩
        exact (Subtype.ext rfl : (⟨(e : Sym2 ℕ), h⟩ : EdgeIndex) = e) ▸ htrue
      · exact fun htrue => ⟨⟨e.2, htrue⟩, e.2⟩
    simp only [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_ofPred_eq,
      Sym2.mem_diagSet]
    by_cases hf : f e = true
    · have hc := hcond.mpr hf
      exact (ite_eq_left hc).trans hf.symm
    · have hc : ¬((∃ h : ¬(e : Sym2 ℕ).IsDiag, f ⟨e, h⟩ = true) ∧
          ¬(e : Sym2 ℕ).IsDiag) := fun h => hf (hcond.mp h)
      have hfalse : f e = false := Bool.eq_false_of_not_eq_true hf
      exact (ite_eq_right hc).trans hfalse.symm

/-- The coordinate at `e` is true exactly when `e` is an edge of the graph. -/
@[simp]
theorem graphCoordEquiv_apply (G : SimpleGraph ℕ) (e : EdgeIndex) :
    graphCoordEquiv G e = true ↔ e.1 ∈ G.edgeSet := by
  classical
  simp [graphCoordEquiv]

/-- An edge coordinate is an edge of the decoded graph exactly when its value is true. -/
@[simp]
theorem mem_edgeSet_graphCoordEquiv_symm (f : EdgeIndex → Bool) (e : EdgeIndex) :
    e.1 ∈ (graphCoordEquiv.symm f).edgeSet ↔ f e = true := by
  rw [← graphCoordEquiv_apply, Equiv.apply_symm_apply]

/-- The graph-to-coordinate map is measurable for Mathlib's adjacency-generated measurable space
on simple graphs and the product measurable space on Boolean coordinates. -/
@[fun_prop]
theorem measurable_graphCoordEquiv : Measurable ⇑graphCoordEquiv := by
  rw [measurable_pi_iff]
  intro e
  classical
  have hmem : Measurable fun G : SimpleGraph ℕ => e.1 ∈ G.edgeSet :=
    measurable_set_iff.1 SimpleGraph.measurable_edgeSet e.1
  exact Measurable.ite hmem.setOf measurable_const measurable_const

/-- The coordinate-to-graph map is measurable, so `graphCoordEquiv` is a measurable equivalence in
substance. -/
@[fun_prop]
theorem measurable_graphCoordEquiv_symm : Measurable ⇑graphCoordEquiv.symm := by
  apply SimpleGraph.measurable_fromEdgeSet.comp
  rw [measurable_set_iff]
  intro e
  simp only [Set.mem_ofPred_eq]
  by_cases he : e.IsDiag
  · have hfun : (fun f : EdgeIndex → Bool => ∃ h : ¬ e.IsDiag, f ⟨e, h⟩ = true) =
        fun _ => False := by
      funext f
      simp [he]
    rw [hfun]
    exact measurable_const
  · have hfun : (fun f : EdgeIndex → Bool => ∃ h : ¬ e.IsDiag, f ⟨e, h⟩ = true) =
        fun f => f ⟨e, he⟩ = true := by
      funext f
      apply propext
      constructor
      · rintro ⟨h, hh⟩
        exact (congrArg f (Subtype.ext rfl : (⟨e, h⟩ : EdgeIndex) = ⟨e, he⟩)).symm.trans hh
      · exact fun hh => ⟨he, hh⟩
    rw [hfun]
    fun_prop

/-- A permutation of the vertices relabels the unordered non-diagonal edge coordinates. -/
def edgeIndexMap (e : Equiv.Perm ℕ) : EdgeIndex ≃ EdgeIndex where
  toFun p := ⟨Sym2.map e p.1, fun h => p.2 ((Sym2.isDiag_map e.injective).mp h)⟩
  invFun p := ⟨Sym2.map e.symm p.1, fun h => p.2 ((Sym2.isDiag_map e.symm.injective).mp h)⟩
  left_inv p := by
    apply Subtype.ext
    -- The subtype coercions hide the two successive `Sym2.map`s from rewriting.
    change Sym2.map e.symm (Sym2.map e p.1) = p.1
    rw [Sym2.map_map, e.symm_comp_self, Sym2.map_id]
    rfl
  right_inv p := by
    apply Subtype.ext
    -- The subtype coercions hide the two successive `Sym2.map`s from rewriting.
    change Sym2.map e (Sym2.map e.symm p.1) = p.1
    rw [Sym2.map_map, e.self_comp_symm, Sym2.map_id]
    rfl

/-- Vertex relabelling acts on an edge coordinate by applying the permutation to both endpoints. -/
@[simp]
theorem edgeIndexMap_val (e : Equiv.Perm ℕ) (p : EdgeIndex) :
    (edgeIndexMap e p).1 = Sym2.map e p.1 := (rfl)

/-- The identity vertex relabelling induces the identity edge-coordinate relabelling. -/
@[simp]
theorem edgeIndexMap_refl : edgeIndexMap (Equiv.refl ℕ) = Equiv.refl EdgeIndex := by
  apply Equiv.ext
  intro p
  apply Subtype.ext
  exact congrFun Sym2.map_id p.1

/-- Successive vertex relabellings induce the corresponding successive coordinate relabellings. -/
@[simp]
theorem edgeIndexMap_trans (e₁ e₂ : Equiv.Perm ℕ) :
    edgeIndexMap (e₁.trans e₂) = (edgeIndexMap e₁).trans (edgeIndexMap e₂) := by
  apply Equiv.ext
  intro p
  apply Subtype.ext
  -- Unfold the two equivalence applications so functoriality of `Sym2.map` applies.
  change Sym2.map ⇑(e₁.trans e₂) p.1 = Sym2.map ⇑e₂ (Sym2.map ⇑e₁ p.1)
  rw [Sym2.map_map, Equiv.coe_trans]

/-- Relabelling an infinite graph is the same as relabelling its Boolean edge coordinates. -/
@[simp]
theorem graphCoordEquiv_comap (e : Equiv.Perm ℕ) (G : SimpleGraph ℕ) (p : EdgeIndex) :
    graphCoordEquiv (SimpleGraph.comap ⇑e G) p = graphCoordEquiv G (edgeIndexMap e p) := by
  -- `e` is a graph isomorphism from the pullback onto `G`, so it preserves edge-set membership.
  have h := (SimpleGraph.Iso.comap e G).map_mem_edgeSet_iff (e := p.1)
  rw [show ⇑(SimpleGraph.Iso.comap e G) = ⇑e from funext (SimpleGraph.Iso.comap_apply e G)] at h
  apply Bool.eq_iff_iff.mpr
  simp only [graphCoordEquiv_apply, edgeIndexMap_val]
  exact h.symm

end DenseGraphLimits

end TauCeti
