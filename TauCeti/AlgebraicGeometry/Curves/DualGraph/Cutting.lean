/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Smoothing

/-!
# Cutting nodes of dual graphs

Cutting a set `S` of nodes replaces each node by its two labelled branches. The resulting
partial normalization can be disconnected. Its connected pieces are indexed by the vertices
of `G.smoothing Sᶜ`: two original vertices lie in the same piece exactly when they can be
joined using uncut edges. This reuses the connectivity quotient of smoothing; no genus is
transferred between vertices when cutting.

`DualGraph.cutComponent` retains the uncut edges, the original vertex genera and markings,
and adds a marking for each branch of a cut edge on the piece. In particular, cutting a
self-node adds two different labels even when they lie on the same vertex.

The total genus formula is
`∑ x, (G.cutComponent S x).arithmeticGenus + #S + 1 = G.arithmeticGenus + #pieces`.
For a single node, a nonseparating cut lowers the genus by one, whereas a separating cut
preserves the sum of the genera. Every vertex retains its log-canonical degree, so all the pieces
are
stable (respectively semistable) exactly when the original graph is. These are the numerical
invariants of partial normalization used when decomposing a nodal curve into pointed pieces.

## References

* E. Arbarello, M. Cornalba and P. A. Griffiths, *Geometry of Algebraic Curves, Volume II*,
  Chapter X, for partial normalization and dual graphs of nodal curves.
-/

public section

namespace TauCeti
namespace DualGraph

open Finset

universe u v

variable {ι : Type v} (G : DualGraph.{u} ι) (S : Finset G.Edge)

/-- The vertex carrying an old marking or a labelled branch of a cut node. The two branches
of each cut edge have distinct labels, including for a loop. -/
def cutMarking : ι ⊕ (S × Fin 2) → G.Vertex :=
  Sum.elim G.marking fun h ↦ G.endpoint h.1.1 h.2

@[simp]
lemma cutMarking_inl (i : ι) : G.cutMarking S (.inl i) = G.marking i := (rfl)

@[simp]
lemma cutMarking_inr (e : S) (i : Fin 2) :
    G.cutMarking S (.inr (e, i)) = G.endpoint e.1 i := (rfl)

/-- A connected component of the partial normalization at `S`. The index is a connectivity
class for the uncut edges, and the markings include both labelled branches of every cut node
on this component. -/
noncomputable abbrev cutComponent (x : (G.smoothing Sᶜ).Vertex) :
    DualGraph.{u} {i : ι ⊕ (S × Fin 2) //
      G.smoothingVertex Sᶜ (G.cutMarking S i) = x} where
  Vertex := (G.smoothingComponent Sᶜ x).Vertex
  vertexNonempty := (G.smoothingComponent Sᶜ x).vertexNonempty
  Edge := (G.smoothingComponent Sᶜ x).Edge
  endpoint := (G.smoothingComponent Sᶜ x).endpoint
  genus := (G.smoothingComponent Sᶜ x).genus
  marking i := ⟨G.cutMarking S i.1, i.2⟩
  connected := (G.smoothingComponent Sᶜ x).connected

@[simp]
lemma endpoint_cutComponent (x : (G.smoothing Sᶜ).Vertex)
    (e : (G.cutComponent S x).Edge) (i : Fin 2) :
    ((G.cutComponent S x).endpoint e i).1 = G.endpoint e.1 i := (rfl)

@[simp]
lemma genus_cutComponent (x : (G.smoothing Sᶜ).Vertex)
    (v : (G.cutComponent S x).Vertex) :
    (G.cutComponent S x).genus v = G.genus v.1 := (rfl)

@[simp]
lemma marking_cutComponent (x : (G.smoothing Sᶜ).Vertex)
    (i : {i : ι ⊕ (S × Fin 2) // G.smoothingVertex Sᶜ (G.cutMarking S i) = x}) :
    ((G.cutComponent S x).marking i).1 = G.cutMarking S i.1 := (rfl)

/-- The vertices of the cut pieces, taken together, are the original vertices. -/
def sigmaVertexCutComponentEquiv :
    (Σ x : (G.smoothing Sᶜ).Vertex, (G.cutComponent S x).Vertex) ≃ G.Vertex :=
  Equiv.sigmaFiberEquiv (G.smoothingVertex Sᶜ)

@[simp]
lemma sigmaVertexCutComponentEquiv_apply
    (v : Σ x : (G.smoothing Sᶜ).Vertex, (G.cutComponent S x).Vertex) :
    G.sigmaVertexCutComponentEquiv S v = v.2.1 := (rfl)

@[simp]
lemma sigmaVertexCutComponentEquiv_symm_apply (v : G.Vertex) :
    (G.sigmaVertexCutComponentEquiv S).symm v =
      ⟨G.smoothingVertex Sᶜ v, ⟨v, rfl⟩⟩ := (rfl)

/-- The edges of the cut pieces, taken together, are exactly the uncut edges. -/
def sigmaEdgeCutComponentEquiv :
    (Σ x : (G.smoothing Sᶜ).Vertex, (G.cutComponent S x).Edge) ≃ {e // e ∉ S} :=
  (Equiv.sigmaCongrRight fun x ↦
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ Sᶜ)
      (fun e ↦ G.smoothingVertex Sᶜ (G.endpoint e 0) = x)).symm).trans
    ((Equiv.sigmaFiberEquiv fun e : ↥(Sᶜ) ↦
      G.smoothingVertex Sᶜ (G.endpoint e.1 0)).trans
      (Equiv.subtypeEquivRight fun _ ↦ mem_compl))

@[simp]
lemma sigmaEdgeCutComponentEquiv_apply
    (e : Σ x : (G.smoothing Sᶜ).Vertex, (G.cutComponent S x).Edge) :
    G.sigmaEdgeCutComponentEquiv S e = ⟨e.2.1, mem_compl.mp e.2.2.1⟩ := (rfl)

@[simp]
lemma sigmaEdgeCutComponentEquiv_symm_apply (e : {e // e ∉ S}) :
    (G.sigmaEdgeCutComponentEquiv S).symm e =
      ⟨G.smoothingVertex Sᶜ (G.endpoint e.1 0), ⟨e.1, mem_compl.mpr e.2, rfl⟩⟩ := (rfl)

/-- Branch markings do not affect the arithmetic genus of a cut component. -/
@[simp]
theorem arithmeticGenus_cutComponent (x : (G.smoothing Sᶜ).Vertex) :
    (G.cutComponent S x).arithmeticGenus = (G.smoothing Sᶜ).genus x := by
  rw [genus_smoothing]
  -- The vertex, edge and genus fields coincide; only the marking type and map differ.
  simp only [arithmeticGenus_def, firstBetti_def]

/-- **Genus of a partial normalization.** The sum of the arithmetic genera of its connected
pieces, plus the number of cut nodes plus one, equals the original genus plus the number of
pieces. This includes separating, nonseparating and simultaneous cuts, without subtraction. -/
theorem sum_arithmeticGenus_cutComponent_add_card :
    (∑ x : (G.smoothing Sᶜ).Vertex, (G.cutComponent S x).arithmeticGenus) + #S + 1 =
      G.arithmeticGenus + Fintype.card (G.smoothing Sᶜ).Vertex := by
  have h : G.arithmeticGenus + Fintype.card (G.smoothing Sᶜ).Vertex =
      (∑ x : (G.smoothing Sᶜ).Vertex, (G.cutComponent S x).arithmeticGenus) +
        Fintype.card (G.smoothing Sᶜ).Edge + 1 := by
    simpa only [arithmeticGenus_smoothing, arithmeticGenus_cutComponent, genus_smoothing] using
      (G.smoothing Sᶜ).arithmeticGenus_add_card_vertex
  have hE := G.card_edge_smoothing Sᶜ
  have hS := card_add_card_compl S
  omega

/-- Partial normalization cannot increase the sum of the arithmetic genera. -/
theorem sum_arithmeticGenus_cutComponent_le :
    (∑ x : (G.smoothing Sᶜ).Vertex, (G.cutComponent S x).arithmeticGenus) ≤
      G.arithmeticGenus := by
  have := G.sum_arithmeticGenus_cutComponent_add_card S
  have := G.card_vertex_smoothing_add_card_le Sᶜ
  have := card_add_card_compl S
  omega

/-! ### Special flags and stability -/

/-- The valence at a vertex of a cut piece counts the branches of uncut nodes there. -/
theorem valence_cutComponent (x : (G.smoothing Sᶜ).Vertex)
    (v : (G.cutComponent S x).Vertex) :
    (G.cutComponent S x).valence v =
      ∑ e ∈ Sᶜ, #{i : Fin 2 | G.endpoint e i = v.1} := by
  simp only [valence_eq_sum, ← Subtype.val_inj]
  rw [← sum_subtype {e ∈ Sᶜ | G.smoothingVertex Sᶜ (G.endpoint e 0) = x}
    (by simp) (fun e ↦ #{i : Fin 2 | G.endpoint e i = v.1})]
  refine sum_subset (filter_subset _ _) fun e he hnot ↦ ?_
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro i _ hei
  have hex := (G.smoothingVertex_endpoint Sᶜ he 0 i).trans
    ((congrArg (G.smoothingVertex Sᶜ) hei).trans v.2)
  exact hnot (by simp [he, hex])

variable [Fintype ι]

/-- The markings at a vertex of a cut piece are its original markings and the branches of
cut nodes there. -/
theorem numMarkings_cutComponent (x : (G.smoothing Sᶜ).Vertex)
    (v : (G.cutComponent S x).Vertex) :
    (G.cutComponent S x).numMarkings v = G.numMarkings v.1 +
      ∑ e ∈ S, #{i : Fin 2 | G.endpoint e i = v.1} := by
  simp only [numMarkings_def, card_filter, ← Subtype.val_inj]
  rw [← sum_subtype {i | G.smoothingVertex Sᶜ (G.cutMarking S i) = x}
    (by simp) (fun i ↦ if G.cutMarking S i = v.1 then 1 else 0)]
  rw [sum_filter_of_ne (fun i _ hi ↦ ?_)]
  · simp only [Fintype.sum_sum_type, cutMarking_inl, cutMarking_inr,
      Fintype.sum_prod_type]
    rw [← sum_subtype S (by simp)
      (fun e ↦ ∑ i : Fin 2, if G.endpoint e i = v.1 then 1 else 0)]
  · by_cases hei : G.cutMarking S i = v.1
    · exact (congrArg (G.smoothingVertex Sᶜ) hei).trans v.2
    · simp [hei] at hi

/-- At a vertex of a cut piece, the number of remaining node branches plus the number of
markings equals the original number of special flags. A cut branch becomes a marking. -/
theorem valence_add_numMarkings_cutComponent (x : (G.smoothing Sᶜ).Vertex)
    (v : (G.cutComponent S x).Vertex) :
    (G.cutComponent S x).valence v + (G.cutComponent S x).numMarkings v =
      G.valence v.1 + G.numMarkings v.1 := by
  rw [G.valence_cutComponent S x v, G.numMarkings_cutComponent S x v, G.valence_eq_sum]
  have h := sum_add_sum_compl S fun e ↦ #{i : Fin 2 | G.endpoint e i = v.1}
  omega

/-- Partial normalization with its branch markings preserves each log-canonical degree. -/
@[simp]
theorem logCanonicalDegree_cutComponent (x : (G.smoothing Sᶜ).Vertex)
    (v : (G.cutComponent S x).Vertex) :
    (G.cutComponent S x).logCanonicalDegree v = G.logCanonicalDegree v.1 := by
  have := G.valence_add_numMarkings_cutComponent S x v
  simp only [logCanonicalDegree_def]
  omega

/-- All pieces of a partial normalization are stable exactly when the original graph is. -/
@[simp]
theorem forall_isStable_cutComponent_iff :
    (∀ x : (G.smoothing Sᶜ).Vertex, (G.cutComponent S x).IsStable) ↔ G.IsStable := by
  simp only [isStable_iff, logCanonicalDegree_cutComponent]
  exact ⟨fun h v ↦ h (G.smoothingVertex Sᶜ v) ⟨v, rfl⟩, fun h _ v ↦ h v.1⟩

/-- All pieces of a partial normalization are semistable exactly when the original graph is. -/
@[simp]
theorem forall_isSemistable_cutComponent_iff :
    (∀ x : (G.smoothing Sᶜ).Vertex, (G.cutComponent S x).IsSemistable) ↔ G.IsSemistable := by
  simp only [isSemistable_iff, logCanonicalDegree_cutComponent]
  exact ⟨fun h v ↦ h (G.smoothingVertex Sᶜ v) ⟨v, rfl⟩, fun h _ v ↦ h v.1⟩

end DualGraph
end TauCeti
