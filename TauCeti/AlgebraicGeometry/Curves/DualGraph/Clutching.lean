/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Clutching dual graphs

Pointed nodal curves are glued along markings by the two clutching operations of Knudsen. In
**external clutching**, two pointed curves with marking sets `I ⊔ {a}` and `J ⊔ {b}` are glued by
identifying the points `a` and `b`, which become a new node; the result carries the markings
`I ⊔ J`. In **self-clutching**, one pointed curve with marking set `I ⊔ {a, b}` is glued to itself
by identifying `a` with `b`; the result carries the markings `I`.

This file describes the effect of both operations on dual graphs.

* `TauCeti.DualGraph.clutch G₁ G₂`: for dual graphs `G₁` and `G₂` with markings indexed by
  `Option ι` and `Option κ`, the extra marking being `none`, the disjoint union of `G₁` and `G₂`
  with one new edge joining the components carrying the two `none` markings; its markings are
  indexed by `ι ⊕ κ`.
* `TauCeti.DualGraph.selfClutch G`: for a dual graph `G` with markings indexed by `ι ⊕ Fin 2`, the
  graph `G` with one new edge joining the components carrying the two markings `Sum.inr 0` and
  `Sum.inr 1`, a loop when both lie on the same component; its markings are indexed by `ι`.

## Main results

* `TauCeti.DualGraph.arithmeticGenus_clutch` and `TauCeti.DualGraph.firstBetti_clutch`: external
  clutching adds the arithmetic genera and the first Betti numbers.
* `TauCeti.DualGraph.arithmeticGenus_selfClutch` and `TauCeti.DualGraph.firstBetti_selfClutch`:
  self-clutching raises the arithmetic genus and the first Betti number by one.
* `TauCeti.DualGraph.logCanonicalDegree_clutch_inl`,
  `TauCeti.DualGraph.logCanonicalDegree_clutch_inr` and
  `TauCeti.DualGraph.logCanonicalDegree_selfClutch`: clutching preserves every log-canonical
  degree, since each glued marking is replaced by a branch of the new node.
* `TauCeti.DualGraph.isStable_clutch_iff` and `TauCeti.DualGraph.isStable_selfClutch_iff`, with
  their semistable counterparts: a clutched graph is stable exactly when its inputs are.

## Implementation notes

The glued markings are singled out by the shape of the marking type, `Option ι` for external
clutching and `ι ⊕ Fin 2` for self-clutching, so that the new edge `none` is determined by them.
Both constructions are abbreviations, so that their vertex and edge types reduce to
`G₁.Vertex ⊕ G₂.Vertex` and `Option (G₁.Edge ⊕ G₂.Edge)`, respectively `G.Vertex` and
`Option G.Edge`, and vertices of an externally clutched graph can be written as `Sum.inl v` and
`Sum.inr v`.

## References

* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks
  `M_{g,n}`*, Math. Scand. 52 (1983), 161–199, §3, for the clutching morphisms.
-/

public section

namespace TauCeti

namespace DualGraph

open Finset

universe u u₁ u₂ v w

variable {ι : Type v} {κ : Type w}

/-! ### External clutching -/

section External

variable (G₁ : DualGraph.{u₁} (Option ι)) (G₂ : DualGraph.{u₂} (Option κ))

/-- A chain in `H` maps to a chain for any edge-endpoint function `f` through which the edges of
`H` map compatibly with a vertex map `g`. -/
private lemma reflTransGen_lift {κ' : Type*} (H : DualGraph.{u} κ') {V E : Type*}
    {f : E → Fin 2 → V} (g : H.Vertex → V) (φ : H.Edge → E)
    (hf : ∀ e i, f (φ e) i = g (H.endpoint e i)) (v w : H.Vertex) :
    Relation.ReflTransGen (fun v w ↦ ∃ e, (f e 0 = v ∧ f e 1 = w) ∨ (f e 0 = w ∧ f e 1 = v))
      (g v) (g w) :=
  (H.connected v w).lift g fun _ _ ⟨e, h⟩ ↦
    ⟨φ e, by obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h <;> simp [hf]⟩

/-- Connectivity of an externally clutched graph, for any edge-endpoint function `f` taking the
values of `clutch`: chains in `G₁` and `G₂` lift to the two halves, and the new edge joins the
halves. -/
private lemma clutch_connected {f : Option (G₁.Edge ⊕ G₂.Edge) → Fin 2 → G₁.Vertex ⊕ G₂.Vertex}
    (hnone : f none = ![.inl (G₁.marking none), .inr (G₂.marking none)])
    (hinl : ∀ e i, f (some (.inl e)) i = .inl (G₁.endpoint e i))
    (hinr : ∀ e i, f (some (.inr e)) i = .inr (G₂.endpoint e i)) (v w : G₁.Vertex ⊕ G₂.Vertex) :
    Relation.ReflTransGen (fun v w ↦ ∃ e, (f e 0 = v ∧ f e 1 = w) ∨ (f e 0 = w ∧ f e 1 = v))
      v w := by
  have hl := reflTransGen_lift G₁ Sum.inl (some ∘ Sum.inl) hinl
  have hr := reflTransGen_lift G₂ Sum.inr (some ∘ Sum.inr) hinr
  have hnew : f none 0 = .inl (G₁.marking none) ∧ f none 1 = .inr (G₂.marking none) := by
    simp [hnone]
  rcases v with v | v <;> rcases w with w | w
  · exact hl v w
  · exact (hl v _).trans (.head ⟨none, Or.inl hnew⟩ (hr _ w))
  · exact (hr v _).trans (.head ⟨none, Or.inr hnew⟩ (hl _ w))
  · exact hr v w

/-- External clutching: the dual graph obtained by gluing a curve with dual graph `G₁` to a curve
with dual graph `G₂` along their markings `none`. It is the disjoint union of `G₁` and `G₂` with a
new edge, the edge `none`, joining the components carrying those two markings. -/
abbrev clutch : DualGraph.{max u₁ u₂} (ι ⊕ κ) where
  Vertex := G₁.Vertex ⊕ G₂.Vertex
  Edge := Option (G₁.Edge ⊕ G₂.Edge)
  endpoint
    | none => ![.inl (G₁.marking none), .inr (G₂.marking none)]
    | some (.inl e) => fun i ↦ .inl (G₁.endpoint e i)
    | some (.inr e) => fun i ↦ .inr (G₂.endpoint e i)
  genus := Sum.elim G₁.genus G₂.genus
  marking := Sum.elim (fun i ↦ .inl (G₁.marking (some i))) (fun j ↦ .inr (G₂.marking (some j)))
  connected := by exact clutch_connected G₁ G₂ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp]
lemma endpoint_clutch_none :
    (G₁.clutch G₂).endpoint none = ![.inl (G₁.marking none), .inr (G₂.marking none)] :=
  rfl

@[simp]
lemma endpoint_clutch_some_inl (e : G₁.Edge) (i : Fin 2) :
    (G₁.clutch G₂).endpoint (some (.inl e)) i = .inl (G₁.endpoint e i) :=
  rfl

@[simp]
lemma endpoint_clutch_some_inr (e : G₂.Edge) (i : Fin 2) :
    (G₁.clutch G₂).endpoint (some (.inr e)) i = .inr (G₂.endpoint e i) :=
  rfl

@[simp]
lemma genus_clutch_inl (v : G₁.Vertex) : (G₁.clutch G₂).genus (.inl v) = G₁.genus v :=
  rfl

@[simp]
lemma genus_clutch_inr (v : G₂.Vertex) : (G₁.clutch G₂).genus (.inr v) = G₂.genus v :=
  rfl

@[simp]
lemma marking_clutch_inl (i : ι) : (G₁.clutch G₂).marking (.inl i) = .inl (G₁.marking (some i)) :=
  rfl

@[simp]
lemma marking_clutch_inr (j : κ) : (G₁.clutch G₂).marking (.inr j) = .inr (G₂.marking (some j)) :=
  rfl

lemma card_vertex_clutch :
    Fintype.card (G₁.clutch G₂).Vertex = Fintype.card G₁.Vertex + Fintype.card G₂.Vertex :=
  Fintype.card_sum

/-- External clutching adds exactly one edge, the new node. -/
lemma card_edge_clutch :
    Fintype.card (G₁.clutch G₂).Edge = Fintype.card G₁.Edge + Fintype.card G₂.Edge + 1 := by
  rw [Fintype.card_option, Fintype.card_sum]

/-- External clutching adds the first Betti numbers: the new edge joins two components that were
not connected before, so it creates no cycle. -/
@[simp]
theorem firstBetti_clutch : (G₁.clutch G₂).firstBetti = G₁.firstBetti + G₂.firstBetti := by
  have := (G₁.clutch G₂).firstBetti_add_card_vertex
  have := G₁.firstBetti_add_card_vertex
  have := G₂.firstBetti_add_card_vertex
  rw [card_vertex_clutch, card_edge_clutch] at *
  omega

/-- External clutching adds the arithmetic genera. -/
@[simp]
theorem arithmeticGenus_clutch :
    (G₁.clutch G₂).arithmeticGenus = G₁.arithmeticGenus + G₂.arithmeticGenus := by
  have hsum : ∑ v, (G₁.clutch G₂).genus v = ∑ v, G₁.genus v + ∑ v, G₂.genus v :=
    Fintype.sum_sum_type _
  rw [arithmeticGenus_def, arithmeticGenus_def, arithmeticGenus_def, hsum, firstBetti_clutch]
  omega

/-- A component of `G₁` gains one branch of the new node exactly when it carries the glued
marking. -/
theorem valence_clutch_inl (v : G₁.Vertex) :
    (G₁.clutch G₂).valence (.inl v) = G₁.valence v + if G₁.marking none = v then 1 else 0 := by
  simp [valence_eq_sum, card_filter, Fintype.sum_option, Fintype.sum_sum_type, Fin.sum_univ_two,
    -sum_boole]
  omega

/-- A component of `G₂` gains one branch of the new node exactly when it carries the glued
marking. -/
theorem valence_clutch_inr (v : G₂.Vertex) :
    (G₁.clutch G₂).valence (.inr v) = G₂.valence v + if G₂.marking none = v then 1 else 0 := by
  simp [valence_eq_sum, card_filter, Fintype.sum_option, Fintype.sum_sum_type, Fin.sum_univ_two,
    -sum_boole]
  omega

variable [Fintype ι] [Fintype κ]

/-- A component of `G₁` loses the glued marking exactly when it carries it. -/
theorem numMarkings_clutch_inl (v : G₁.Vertex) :
    (G₁.clutch G₂).numMarkings (.inl v) + (if G₁.marking none = v then 1 else 0) =
      G₁.numMarkings v := by
  simp [numMarkings_def, card_filter, Fintype.sum_option, Fintype.sum_sum_type, -sum_boole]
  omega

/-- A component of `G₂` loses the glued marking exactly when it carries it. -/
theorem numMarkings_clutch_inr (v : G₂.Vertex) :
    (G₁.clutch G₂).numMarkings (.inr v) + (if G₂.marking none = v then 1 else 0) =
      G₂.numMarkings v := by
  simp [numMarkings_def, card_filter, Fintype.sum_option, Fintype.sum_sum_type, -sum_boole]
  omega

/-- External clutching preserves the log-canonical degree of every component of `G₁`: the glued
marking becomes a branch of the new node. -/
@[simp]
theorem logCanonicalDegree_clutch_inl (v : G₁.Vertex) :
    (G₁.clutch G₂).logCanonicalDegree (.inl v) = G₁.logCanonicalDegree v := by
  have := G₁.valence_clutch_inl G₂ v
  have := G₁.numMarkings_clutch_inl G₂ v
  rw [logCanonicalDegree_def, logCanonicalDegree_def, genus_clutch_inl]
  omega

/-- External clutching preserves the log-canonical degree of every component of `G₂`: the glued
marking becomes a branch of the new node. -/
@[simp]
theorem logCanonicalDegree_clutch_inr (v : G₂.Vertex) :
    (G₁.clutch G₂).logCanonicalDegree (.inr v) = G₂.logCanonicalDegree v := by
  have := G₁.valence_clutch_inr G₂ v
  have := G₁.numMarkings_clutch_inr G₂ v
  rw [logCanonicalDegree_def, logCanonicalDegree_def, genus_clutch_inr]
  omega

/-- An externally clutched graph is stable exactly when both of its inputs are. -/
@[simp]
theorem isStable_clutch_iff : (G₁.clutch G₂).IsStable ↔ G₁.IsStable ∧ G₂.IsStable := by
  simp [isStable_iff, Sum.forall]

/-- An externally clutched graph is semistable exactly when both of its inputs are. -/
@[simp]
theorem isSemistable_clutch_iff :
    (G₁.clutch G₂).IsSemistable ↔ G₁.IsSemistable ∧ G₂.IsSemistable := by
  simp [isSemistable_iff, Sum.forall]

end External

/-! ### Self-clutching -/

section Self

variable (G : DualGraph.{u} (ι ⊕ Fin 2))

/-- Self-clutching: the dual graph obtained from a curve with dual graph `G` by gluing its
markings `Sum.inr 0` and `Sum.inr 1`. It is `G` with a new edge, the edge `none`, joining the
components carrying those two markings; the edge is a loop when they lie on one component. -/
abbrev selfClutch : DualGraph.{u} ι where
  Vertex := G.Vertex
  Edge := Option G.Edge
  endpoint
    | none => fun i ↦ G.marking (.inr i)
    | some e => G.endpoint e
  genus := G.genus
  marking i := G.marking (.inl i)
  connected v w := (G.connected v w).lift id fun _ _ ⟨e, h⟩ ↦ ⟨some e, h⟩

@[simp]
lemma endpoint_selfClutch_none (i : Fin 2) :
    G.selfClutch.endpoint none i = G.marking (.inr i) :=
  rfl

@[simp]
lemma endpoint_selfClutch_some (e : G.Edge) (i : Fin 2) :
    G.selfClutch.endpoint (some e) i = G.endpoint e i :=
  rfl

@[simp]
lemma genus_selfClutch (v : G.Vertex) : G.selfClutch.genus v = G.genus v :=
  rfl

@[simp]
lemma marking_selfClutch (i : ι) : G.selfClutch.marking i = G.marking (.inl i) :=
  rfl

lemma card_vertex_selfClutch : Fintype.card G.selfClutch.Vertex = Fintype.card G.Vertex :=
  rfl

/-- Self-clutching adds exactly one edge, the new node. -/
lemma card_edge_selfClutch : Fintype.card G.selfClutch.Edge = Fintype.card G.Edge + 1 :=
  Fintype.card_option

/-- Self-clutching raises the first Betti number by one: the new edge closes a cycle. -/
@[simp]
theorem firstBetti_selfClutch : G.selfClutch.firstBetti = G.firstBetti + 1 := by
  have := G.selfClutch.firstBetti_add_card_vertex
  have := G.firstBetti_add_card_vertex
  rw [card_vertex_selfClutch, card_edge_selfClutch] at *
  omega

/-- Self-clutching raises the arithmetic genus by one. -/
@[simp]
theorem arithmeticGenus_selfClutch : G.selfClutch.arithmeticGenus = G.arithmeticGenus + 1 := by
  simp only [arithmeticGenus_def, firstBetti_selfClutch, add_assoc]

/-- A component gains one branch of the new node for each glued marking it carries. -/
theorem valence_selfClutch (v : G.Vertex) :
    G.selfClutch.valence v = G.valence v + #{i : Fin 2 | G.marking (.inr i) = v} := by
  simp [valence_eq_sum, card_filter, Fintype.sum_option, -sum_boole]
  omega

variable [Fintype ι]

/-- A component loses each glued marking it carries. -/
theorem numMarkings_selfClutch (v : G.Vertex) :
    G.selfClutch.numMarkings v + #{i : Fin 2 | G.marking (.inr i) = v} = G.numMarkings v := by
  simp [numMarkings_def, card_filter, Fintype.sum_sum_type, -sum_boole]

/-- Self-clutching preserves every log-canonical degree: the two glued markings become the two
branches of the new node. -/
@[simp]
theorem logCanonicalDegree_selfClutch (v : G.Vertex) :
    G.selfClutch.logCanonicalDegree v = G.logCanonicalDegree v := by
  have := G.valence_selfClutch v
  have := G.numMarkings_selfClutch v
  rw [logCanonicalDegree_def, logCanonicalDegree_def, genus_selfClutch]
  omega

/-- A self-clutched graph is stable exactly when its input is. -/
@[simp]
theorem isStable_selfClutch_iff : G.selfClutch.IsStable ↔ G.IsStable := by
  simp only [isStable_iff, logCanonicalDegree_selfClutch]

/-- A self-clutched graph is semistable exactly when its input is. -/
@[simp]
theorem isSemistable_selfClutch_iff : G.selfClutch.IsSemistable ↔ G.IsSemistable := by
  simp only [isSemistable_iff, logCanonicalDegree_selfClutch]

end Self

end DualGraph

end TauCeti
