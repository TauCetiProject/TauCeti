/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.Fin.Rev
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.VertexConnectivity
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation
import Mathlib.Data.List.NodupEquivFin
import TauCeti.Combinatorics.SimpleGraph.Connectivity.Fan
import TauCeti.Combinatorics.SimpleGraph.Paths

/-!
# `st`-numberings and bipolar acyclic orientations of simple graphs

An *`st`-numbering* of a finite simple graph `G` on `V` with chosen source `s` and sink `t` is a
bijection `V ≃ Fin (Fintype.card V)` assigning `0` to `s` and `Fintype.card V - 1` to `t` such that
every vertex other than `s` and `t` has both a lower-numbered neighbour and a higher-numbered
neighbour. Directing each edge from its lower-numbered endpoint to its higher-numbered endpoint
yields a bipolar acyclic orientation of `G`: it has no positive-length directed closed paths, and
whenever `G` is preconnected (in particular whenever `s` and `t` are adjacent or `V` has at least
three vertices), `s` is the unique vertex with no incoming arrow, `t` is the unique vertex with no
outgoing arrow, and every vertex lies on a directed path from `s` to `t`.

On a finite vertex type with at least three vertices and `s ≠ t`, Lempel, Even, and Cederbaum
characterized the existence of an `st`-numbering by `2`-vertex-connectivity of `G ⊔ edge s t`
(and hence of `G` itself when `G.Adj s t`). The existence direction is proved here by iteratively
attaching open ears to a partial vertex list starting at `[s, t]` via the fan lemma
(`SimpleGraph.IsVertexConnected.exists_fan`), inserting the internal vertices of each new ear
between its two attachment vertices.

## Main definitions

* `SimpleGraph.STNumbering G s t`: a bijective numbering `V ≃ Fin (Fintype.card V)` placing `s`
  first, `t` last, and giving every other vertex both a lower-numbered and a higher-numbered
  neighbour.
* `SimpleGraph.STNumbering.symm`, `SimpleGraph.STNumbering.symmEquiv`: order reversal on
  `Fin (Fintype.card V)`, exchanging `s` and `t`.
* `SimpleGraph.STNumbering.map`, `SimpleGraph.Iso.stNumberingEquiv`: transport of `st`-numberings
  along graph isomorphisms.
* `SimpleGraph.STNumbering.mono`: preservation of an `st`-numbering upon adding edges on the same
  vertex type.
* `SimpleGraph.STNumbering.toOrientation`: the `TauCeti.DoubledQuiver.Orientation` directing each
  edge toward its higher-numbered endpoint.
* `SimpleGraph.STNumbering.arrow`, `SimpleGraph.STNumbering.homEquiv`: arrow transport between
  `OrientedQuiver G n.toOrientation` and adjacency with strict numbering inequality.

## Main results

* `SimpleGraph.STNumbering.isAcyclic_toOrientation`: the induced orientation is acyclic.
* `SimpleGraph.STNumbering.nonempty_path_from_source`,
  `SimpleGraph.STNumbering.nonempty_path_to_sink`,
  `SimpleGraph.STNumbering.forall_isEmpty_hom_target_iff`,
  `SimpleGraph.STNumbering.forall_isEmpty_hom_source_iff`: when `G` is preconnected (in particular
  when `G.Adj s t` or `3 ≤ Fintype.card V`), every vertex is reachable from `s` and can reach `t`,
  `s` is the unique vertex with no incoming arrow, and `t` is the unique vertex with no outgoing
  arrow (together with their graph-level transports `forall_isEmpty_vertexEquiv_hom_target_iff`,
  `forall_isEmpty_vertexEquiv_hom_source_iff`, `forall_not_adj_and_numbering_lt_iff`, and
  `forall_not_adj_and_lt_numbering_iff`).
* `SimpleGraph.nonempty_stNumbering_iff_isVertexConnected_two_sup_edge`,
  `SimpleGraph.nonempty_stNumbering_iff_isVertexConnected_two`,
  `SimpleGraph.IsVertexConnected.nonempty_stNumbering`: **Lempel–Even–Cederbaum theorem**: on at
  least three vertices with `s ≠ t`, `G` admits an `st`-numbering if and only if
  `G ⊔ SimpleGraph.edge s t` is `2`-vertex-connected.

## References

* A. Lempel, S. Even, and I. Cederbaum, *An algorithm for planarity testing of graphs*, in
  *Theory of Graphs: International Symposium (Rome, 1966)*, Gordon and Breach, New York, 1967,
  215–232.
* S. Even and R. E. Tarjan, *Computing an st-numbering*, Theor. Comput. Sci. 2 (1976), 339–344,
  Theorem 1.
* R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017.
-/

public section

open Finset TauCeti.DoubledQuiver
open scoped List

universe u

namespace SimpleGraph

variable {V : Type u}

section Defs

variable (G : SimpleGraph V) [Fintype V]

/-- An **`st`-numbering** of a finite simple graph `G` with source `s` and sink `t` is a bijection
`V ≃ Fin (Fintype.card V)` sending `s` to `0` and `t` to `Fintype.card V - 1` such that every
vertex other than `s` and `t` has both a lower-numbered neighbour and a higher-numbered
neighbour. -/
structure STNumbering (s t : V) where
  /-- The bijective numbering of the vertices by `Fin (Fintype.card V)`. -/
  numbering : V ≃ Fin (Fintype.card V)
  /-- The source `s` receives number `0`. -/
  source_first : (numbering s).val = 0
  /-- The sink `t` receives number `Fintype.card V - 1`. -/
  sink_last : (numbering t).val + 1 = Fintype.card V
  /-- Every vertex other than `s` and `t` has a lower-numbered neighbour. -/
  lower_neighbor : ∀ ⦃v⦄, v ≠ s → v ≠ t → ∃ u, G.Adj u v ∧ numbering u < numbering v
  /-- Every vertex other than `s` and `t` has a higher-numbered neighbour. -/
  higher_neighbor : ∀ ⦃v⦄, v ≠ s → v ≠ t → ∃ w, G.Adj v w ∧ numbering v < numbering w

end Defs

namespace STNumbering

variable [Fintype V] {G H : SimpleGraph V} {s t : V}

/-! ### Basic numbering API -/

/-- Two `st`-numberings are equal when they assign the same index to every vertex. -/
@[ext]
theorem ext {n₁ n₂ : G.STNumbering s t} (h : ∀ v, n₁.numbering v = n₂.numbering v) : n₁ = n₂ := by
  cases n₁
  cases n₂
  congr
  exact Equiv.ext h

/-- Two `st`-numberings are equal when they assign the same natural number to every vertex. -/
theorem ext_val {n₁ n₂ : G.STNumbering s t}
    (h : ∀ v, (n₁.numbering v).val = (n₂.numbering v).val) : n₁ = n₂ :=
  ext fun v ↦ Fin.ext (h v)

/-- The vertex numbering of an `st`-numbering is injective. -/
theorem injective (n : G.STNumbering s t) : Function.Injective n.numbering :=
  n.numbering.injective

/-- The vertex numbering of an `st`-numbering is bijective. -/
theorem bijective (n : G.STNumbering s t) : Function.Bijective n.numbering :=
  n.numbering.bijective

/-- The natural-number values of an `st`-numbering are injective. -/
theorem val_numbering_injective (n : G.STNumbering s t) :
    Function.Injective fun v ↦ (n.numbering v).val :=
  Fin.val_injective.comp n.injective

/-- A graph admitting an `st`-numbering has a nonempty vertex type. -/
theorem nonempty (_ : G.STNumbering s t) : Nonempty V :=
  ⟨s⟩

/-- A graph admitting an `st`-numbering has positive vertex count. -/
theorem card_pos (n : G.STNumbering s t) : 0 < Fintype.card V :=
  (n.numbering s).pos

@[simp]
theorem val_numbering_source (n : G.STNumbering s t) : (n.numbering s).val = 0 :=
  n.source_first

@[simp]
theorem val_numbering_sink (n : G.STNumbering s t) :
    (n.numbering t).val = Fintype.card V - 1 := by
  have := n.sink_last
  omega

/-- Explicit `Fin` value of the source in an `st`-numbering. -/
theorem numbering_source (n : G.STNumbering s t) : n.numbering s = ⟨0, n.card_pos⟩ :=
  Fin.ext n.source_first

/-- Explicit `Fin` value of the sink in an `st`-numbering. -/
theorem numbering_sink (n : G.STNumbering s t) :
    n.numbering t = ⟨Fintype.card V - 1, Nat.sub_lt n.card_pos Nat.one_pos⟩ :=
  Fin.ext n.val_numbering_sink

/-- A vertex receives number `0` if and only if it is the source `s`. -/
theorem val_numbering_eq_zero_iff (n : G.STNumbering s t) {v : V} :
    (n.numbering v).val = 0 ↔ v = s := by
  rw [← n.val_numbering_source]
  exact n.val_numbering_injective.eq_iff

/-- A vertex receives number `Fintype.card V - 1` if and only if it is the sink `t`. -/
theorem val_numbering_eq_card_sub_one_iff (n : G.STNumbering s t) {v : V} :
    (n.numbering v).val = Fintype.card V - 1 ↔ v = t := by
  rw [← n.val_numbering_sink]
  exact n.val_numbering_injective.eq_iff

/-- In an `st`-numbering, `s = t` holds exactly when the graph has a single vertex. -/
theorem source_eq_sink_iff (n : G.STNumbering s t) : s = t ↔ Fintype.card V = 1 := by
  rw [← n.val_numbering_eq_card_sub_one_iff, n.val_numbering_source]
  have := n.card_pos
  omega

/-- On a nontrivial vertex type, the source and sink of an `st`-numbering are distinct. -/
theorem source_ne_sink [Nontrivial V] (n : G.STNumbering s t) : s ≠ t := by
  rw [ne_eq, n.source_eq_sink_iff]
  exact Fintype.one_lt_card.ne'

/-- The source `s` has the minimum number among all vertices. -/
theorem numbering_source_le (n : G.STNumbering s t) (v : V) :
    n.numbering s ≤ n.numbering v := by
  simp [Fin.le_iff_val_le_val]

@[simp]
theorem not_lt_numbering_source (n : G.STNumbering s t) (v : V) :
    ¬n.numbering v < n.numbering s :=
  not_lt_of_ge (n.numbering_source_le v)

/-- A vertex has strictly larger number than `s` if and only if it is distinct from `s`. -/
theorem numbering_source_lt_iff (n : G.STNumbering s t) {v : V} :
    n.numbering s < n.numbering v ↔ v ≠ s := by
  rw [lt_iff_le_and_ne, ne_comm, n.injective.ne_iff]
  exact and_iff_right (n.numbering_source_le v)

/-- The sink `t` has the maximum number among all vertices. -/
theorem le_numbering_sink (n : G.STNumbering s t) (v : V) :
    n.numbering v ≤ n.numbering t := by
  rw [Fin.le_iff_val_le_val, n.val_numbering_sink]
  have := (n.numbering v).isLt
  omega

@[simp]
theorem not_numbering_sink_lt (n : G.STNumbering s t) (v : V) :
    ¬n.numbering t < n.numbering v :=
  not_lt_of_ge (n.le_numbering_sink v)

/-- A vertex has strictly smaller number than `t` if and only if it is distinct from `t`. -/
theorem lt_numbering_sink_iff (n : G.STNumbering s t) {v : V} :
    n.numbering v < n.numbering t ↔ v ≠ t := by
  rw [lt_iff_le_and_ne, n.injective.ne_iff]
  exact and_iff_right (n.le_numbering_sink v)

/-! ### Endpoint copy, reversal, monotonicity, and isomorphism transport -/

/-- Copy an `st`-numbering across equalities of its source and sink vertices. -/
def copy (n : G.STNumbering s t) {s' t' : V} (hs : s = s') (ht : t = t') :
    G.STNumbering s' t' where
  numbering := n.numbering
  source_first := hs ▸ n.source_first
  sink_last := ht ▸ n.sink_last
  lower_neighbor _ hvs' hvt' := n.lower_neighbor (hs ▸ hvs') (ht ▸ hvt')
  higher_neighbor _ hvs' hvt' := n.higher_neighbor (hs ▸ hvs') (ht ▸ hvt')

@[simp]
theorem copy_numbering (n : G.STNumbering s t) {s' t' : V} (hs : s = s') (ht : t = t') :
    (n.copy hs ht).numbering = n.numbering :=
  (rfl)

@[simp]
theorem copy_rfl (n : G.STNumbering s t) : n.copy rfl rfl = n :=
  (rfl)

/-- Reverse an `st`-numbering via `Fin.revPerm`, exchanging the source `s` and the sink `t`. -/
def symm (n : G.STNumbering s t) : G.STNumbering t s where
  numbering := n.numbering.trans Fin.revPerm
  source_first := by
    simp only [Equiv.trans_apply, Fin.revPerm_apply, Fin.val_rev, n.val_numbering_sink]
    omega
  sink_last := by
    have := n.card_pos
    simp only [Equiv.trans_apply, Fin.revPerm_apply, Fin.val_rev, n.val_numbering_source]
    omega
  lower_neighbor _ hvt hvs := by
    obtain ⟨w, hadj, hlt⟩ := n.higher_neighbor hvs hvt
    exact ⟨w, hadj.symm, Fin.rev_lt_rev.2 hlt⟩
  higher_neighbor _ hvt hvs := by
    obtain ⟨u, hadj, hlt⟩ := n.lower_neighbor hvs hvt
    exact ⟨u, hadj.symm, Fin.rev_lt_rev.2 hlt⟩

@[simp]
theorem symm_numbering_apply (n : G.STNumbering s t) (v : V) :
    n.symm.numbering v = (n.numbering v).rev :=
  (rfl)

/-- Explicit natural-number formula for the reversed `st`-numbering. -/
theorem val_symm_numbering (n : G.STNumbering s t) (v : V) :
    (n.symm.numbering v).val = Fintype.card V - 1 - (n.numbering v).val := by
  simp only [symm_numbering_apply, Fin.val_rev]
  omega

@[simp]
theorem symm_symm (n : G.STNumbering s t) : n.symm.symm = n :=
  ext fun v ↦ Fin.rev_rev (n.numbering v)

@[simp]
theorem symm_copy (n : G.STNumbering s t) {s' t' : V} (hs : s = s') (ht : t = t') :
    (n.copy hs ht).symm = n.symm.copy ht hs :=
  (rfl)

/-- Reversing the order on `Fin (Fintype.card V)` identifies `st`-numberings with
`ts`-numberings. -/
def symmEquiv (G : SimpleGraph V) (s t : V) : G.STNumbering s t ≃ G.STNumbering t s where
  toFun := symm
  invFun := symm
  left_inv := symm_symm
  right_inv := symm_symm

@[simp]
theorem symmEquiv_apply (n : G.STNumbering s t) : symmEquiv G s t n = n.symm :=
  (rfl)

@[simp]
theorem symmEquiv_symm (G : SimpleGraph V) (s t : V) :
    (symmEquiv G s t).symm = symmEquiv G t s :=
  (rfl)

/-- Adding edges on the same vertex type preserves an `st`-numbering. -/
def mono (hGH : G ≤ H) (n : G.STNumbering s t) : H.STNumbering s t where
  numbering := n.numbering
  source_first := n.source_first
  sink_last := n.sink_last
  lower_neighbor _ hvs hvt :=
    let ⟨u, hadj, hlt⟩ := n.lower_neighbor hvs hvt
    ⟨u, hGH hadj, hlt⟩
  higher_neighbor _ hvs hvt :=
    let ⟨w, hadj, hlt⟩ := n.higher_neighbor hvs hvt
    ⟨w, hGH hadj, hlt⟩

@[simp]
theorem mono_numbering (hGH : G ≤ H) (n : G.STNumbering s t) :
    (n.mono hGH).numbering = n.numbering :=
  (rfl)

@[simp]
theorem mono_rfl (n : G.STNumbering s t) : n.mono le_rfl = n :=
  (rfl)

/-- Edge-monotonicity of `st`-numberings composes transitively. -/
theorem mono_trans {K : SimpleGraph V} (hGH : G ≤ H) (hHK : H ≤ K) (n : G.STNumbering s t) :
    (n.mono hGH).mono hHK = n.mono (hGH.trans hHK) :=
  (rfl)

@[simp]
theorem symm_mono (hGH : G ≤ H) (n : G.STNumbering s t) :
    (n.mono hGH).symm = n.symm.mono hGH :=
  (rfl)

/-- Transport an `st`-numbering along a graph isomorphism. -/
def map {W : Type*} [Fintype W] {G' : SimpleGraph W} (n : G.STNumbering s t) (e : G ≃g G') :
    G'.STNumbering (e s) (e t) where
  numbering := e.symm.toEquiv.trans (n.numbering.trans (finCongr (Fintype.card_congr e.toEquiv)))
  source_first := by
    simp only [Equiv.trans_apply, RelIso.coe_fn_toEquiv, finCongr_apply, Fin.val_cast,
      RelIso.symm_apply_apply, n.val_numbering_source]
  sink_last := by
    simp only [Equiv.trans_apply, RelIso.coe_fn_toEquiv, finCongr_apply, Fin.val_cast,
      RelIso.symm_apply_apply, ← Fintype.card_congr e.toEquiv, n.sink_last]
  lower_neighbor w hws hwt := by
    have hws' : e.symm w ≠ s := fun h ↦ hws (by simpa using congrArg e h)
    have hwt' : e.symm w ≠ t := fun h ↦ hwt (by simpa using congrArg e h)
    obtain ⟨u, hadj, hlt⟩ := n.lower_neighbor hws' hwt'
    have hadj' : G'.Adj (e u) w := by
      simpa only [RelIso.apply_symm_apply] using e.map_adj_iff.2 hadj
    refine ⟨e u, hadj', ?_⟩
    simp only [Equiv.trans_apply, RelIso.coe_fn_toEquiv, finCongr_apply, Fin.lt_def, Fin.val_cast,
      RelIso.symm_apply_apply]
    exact Fin.lt_def.1 hlt
  higher_neighbor w hws hwt := by
    have hws' : e.symm w ≠ s := fun h ↦ hws (by simpa using congrArg e h)
    have hwt' : e.symm w ≠ t := fun h ↦ hwt (by simpa using congrArg e h)
    obtain ⟨u, hadj, hlt⟩ := n.higher_neighbor hws' hwt'
    have hadj' : G'.Adj w (e u) := by
      simpa only [RelIso.apply_symm_apply] using e.map_adj_iff.2 hadj
    refine ⟨e u, hadj', ?_⟩
    simp only [Equiv.trans_apply, RelIso.coe_fn_toEquiv, finCongr_apply, Fin.lt_def, Fin.val_cast,
      RelIso.symm_apply_apply]
    exact Fin.lt_def.1 hlt

@[simp]
theorem val_map_numbering {W : Type*} [Fintype W] {G' : SimpleGraph W} (n : G.STNumbering s t)
    (e : G ≃g G') (w : W) :
    ((n.map e).numbering w).val = (n.numbering (e.symm w)).val :=
  (rfl)

/-- Evaluating `n.map e` at `e v` recovers the natural-number index of `v`. -/
theorem val_map_numbering_apply {W : Type*} [Fintype W] {G' : SimpleGraph W}
    (n : G.STNumbering s t) (e : G ≃g G') (v : V) :
    ((n.map e).numbering (e v)).val = (n.numbering v).val := by
  rw [val_map_numbering, RelIso.symm_apply_apply]

@[simp]
theorem map_refl (n : G.STNumbering s t) : n.map Iso.refl = n :=
  ext_val fun _ ↦ rfl

/-- Transport of `st`-numberings along graph isomorphisms composes functorially. -/
theorem map_trans {W X : Type*} [Fintype W] [Fintype X] {G' : SimpleGraph W} {G'' : SimpleGraph X}
    (n : G.STNumbering s t) (e₁ : G ≃g G') (e₂ : G' ≃g G'') :
    (n.map e₁).map e₂ = n.map (e₁.trans e₂) :=
  ext_val fun _ ↦ rfl

@[simp]
theorem symm_map {W : Type*} [Fintype W] {G' : SimpleGraph W} (n : G.STNumbering s t)
    (e : G ≃g G') :
    (n.map e).symm = n.symm.map e :=
  ext_val fun _ ↦ by simp [Fintype.card_congr e.toEquiv]

end STNumbering

namespace Iso

/-- A graph isomorphism induces an equivalence of `st`-numberings. -/
def stNumberingEquiv [Fintype V] {W : Type*} [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (s t : V) : G.STNumbering s t ≃ H.STNumbering (e s) (e t) where
  toFun n := n.map e
  invFun m := (m.map e.symm).copy (e.symm_apply_apply s) (e.symm_apply_apply t)
  left_inv _ := STNumbering.ext_val fun _ ↦ by simp
  right_inv _ := STNumbering.ext_val fun _ ↦ by simp

@[simp]
theorem stNumberingEquiv_apply [Fintype V] {W : Type*} [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (s t : V) (n : G.STNumbering s t) :
    e.stNumberingEquiv s t n = n.map e :=
  (rfl)

@[simp]
theorem val_stNumberingEquiv_symm_numbering [Fintype V] {W : Type*} [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (s t : V)
    (m : H.STNumbering (e s) (e t)) (v : V) :
    (((e.stNumberingEquiv s t).symm m).numbering v).val = (m.numbering (e v)).val := by
  simp [stNumberingEquiv]

end Iso

namespace STNumbering

variable [Fintype V] {G : SimpleGraph V} {s t : V}

/-! ### Induced bipolar orientation and quiver transport -/

/-- The orientation induced by an `st`-numbering, directing every edge from its lower-numbered
endpoint to its higher-numbered endpoint. -/
def toOrientation (n : G.STNumbering s t) : Orientation G :=
  @Orientation.ofLinearOrder V G (LinearOrder.lift' n.numbering n.injective)

/-- A dart belongs to `n.toOrientation` exactly when its first endpoint has a strictly smaller
number than its second endpoint. -/
@[simp]
theorem mem_toOrientation (n : G.STNumbering s t) (d : G.Dart) :
    d ∈ n.toOrientation ↔ n.numbering d.fst < n.numbering d.snd :=
  @Orientation.mem_ofLinearOrder_iff V G (LinearOrder.lift' n.numbering n.injective) d

@[simp]
theorem toOrientation_copy (n : G.STNumbering s t) {s' t' : V} (hs : s = s') (ht : t = t') :
    (n.copy hs ht).toOrientation = n.toOrientation :=
  (rfl)

/-- Reversing an `st`-numbering reverses every dart of its induced orientation. -/
theorem mem_symm_toOrientation (n : G.STNumbering s t) (d : G.Dart) :
    d ∈ n.symm.toOrientation ↔ d.symm ∈ n.toOrientation := by
  simp [mem_toOrientation, Fin.rev_lt_rev]

/-- Construct the oriented-quiver arrow over an edge directed toward its higher-numbered
endpoint. -/
def arrow (n : G.STNumbering s t) {u v : V} (h : G.Adj u v) (hlt : n.numbering u < n.numbering v) :
    OrientedQuiver.vertex G n.toOrientation u ⟶ OrientedQuiver.vertex G n.toOrientation v :=
  OrientedQuiver.arrow G n.toOrientation h ((n.mem_toOrientation ⟨(u, v), h⟩).2 hlt)

/-- Transport arrows of `OrientedQuiver G n.toOrientation` across `OrientedQuiver.homEquiv` to
pairs of an adjacency proof and a strict numbering inequality. -/
def homEquiv (n : G.STNumbering s t) (u v : V) :
    (OrientedQuiver.vertex G n.toOrientation u ⟶ OrientedQuiver.vertex G n.toOrientation v) ≃
      Subtype fun _ : G.Adj u v ↦ n.numbering u < n.numbering v :=
  (OrientedQuiver.homEquiv G n.toOrientation u v).trans
    (Equiv.subtypeEquivRight fun h ↦ n.mem_toOrientation ⟨(u, v), h⟩)

@[simp]
theorem homEquiv_arrow (n : G.STNumbering s t) {u v : V} (h : G.Adj u v)
    (hlt : n.numbering u < n.numbering v) :
    n.homEquiv u v (n.arrow h hlt) = ⟨h, hlt⟩ :=
  Subtype.ext rfl

@[simp]
theorem homEquiv_symm_apply (n : G.STNumbering s t) {u v : V} (h : G.Adj u v)
    (hlt : n.numbering u < n.numbering v) :
    (n.homEquiv u v).symm ⟨h, hlt⟩ = n.arrow h hlt :=
  Subsingleton.elim _ _

/-- An arrow from `u` to `v` exists in `OrientedQuiver G n.toOrientation` if and only if `u` and
`v` are adjacent with `n.numbering u < n.numbering v`. -/
theorem nonempty_hom_iff (n : G.STNumbering s t) {u v : V} :
    Nonempty (OrientedQuiver.vertex G n.toOrientation u ⟶
        OrientedQuiver.vertex G n.toOrientation v) ↔
      G.Adj u v ∧ n.numbering u < n.numbering v := by
  rw [(n.homEquiv u v).nonempty_congr]
  exact ⟨fun ⟨⟨h, hlt⟩⟩ ↦ ⟨h, hlt⟩, fun ⟨h, hlt⟩ ↦ ⟨⟨h, hlt⟩⟩⟩

/-- There is no arrow from `u` to `v` in `OrientedQuiver G n.toOrientation` if and only if `u` and
`v` are not adjacent with `n.numbering u < n.numbering v`. -/
theorem isEmpty_hom_iff (n : G.STNumbering s t) {u v : V} :
    IsEmpty (OrientedQuiver.vertex G n.toOrientation u ⟶
        OrientedQuiver.vertex G n.toOrientation v) ↔
      ¬(G.Adj u v ∧ n.numbering u < n.numbering v) := by
  rw [← not_nonempty_iff, n.nonempty_hom_iff]

/-- The orientation induced by an `st`-numbering is acyclic. -/
theorem isAcyclic_toOrientation (n : G.STNumbering s t) :
    TauCeti.Quiver.IsAcyclic (OrientedQuiver G n.toOrientation) :=
  @OrientedQuiver.isAcyclic_ofLinearOrder V G (LinearOrder.lift' n.numbering n.injective)

private theorem adj_and_lt_of_hom (n : G.STNumbering s t) {x y : OrientedQuiver G n.toOrientation}
    (e : x ⟶ y) :
    G.Adj ((OrientedQuiver.vertexEquiv G n.toOrientation).symm x)
        ((OrientedQuiver.vertexEquiv G n.toOrientation).symm y) ∧
      n.numbering ((OrientedQuiver.vertexEquiv G n.toOrientation).symm x) <
        n.numbering ((OrientedQuiver.vertexEquiv G n.toOrientation).symm y) := by
  let u := (OrientedQuiver.vertexEquiv G n.toOrientation).symm x
  let v := (OrientedQuiver.vertexEquiv G n.toOrientation).symm y
  have hx : OrientedQuiver.vertex G n.toOrientation u = x := by
    rw [← OrientedQuiver.vertexEquiv_apply, Equiv.apply_symm_apply]
  have hy : OrientedQuiver.vertex G n.toOrientation v = y := by
    rw [← OrientedQuiver.vertexEquiv_apply, Equiv.apply_symm_apply]
  obtain ⟨hadj, hlt⟩ := n.homEquiv u v (Quiver.homOfEq e hx.symm hy.symm)
  exact ⟨hadj, hlt⟩

/-- Along any directed path in `OrientedQuiver G n.toOrientation`, vertex numbers are monotone. -/
theorem numbering_le_of_path (n : G.STNumbering s t) {x y : OrientedQuiver G n.toOrientation}
    (p : Quiver.Path x y) :
    n.numbering ((OrientedQuiver.vertexEquiv G n.toOrientation).symm x) ≤
      n.numbering ((OrientedQuiver.vertexEquiv G n.toOrientation).symm y) := by
  induction p with
  | nil => exact le_rfl
  | cons _ e ih => exact ih.trans (n.adj_and_lt_of_hom e).2.le

/-- Along any positive-length directed path in `OrientedQuiver G n.toOrientation`, the endpoint
number is strictly greater than the start number. -/
theorem numbering_lt_of_path_of_length_pos (n : G.STNumbering s t)
    {x y : OrientedQuiver G n.toOrientation} (p : Quiver.Path x y) (hp : 0 < p.length) :
    n.numbering ((OrientedQuiver.vertexEquiv G n.toOrientation).symm x) <
      n.numbering ((OrientedQuiver.vertexEquiv G n.toOrientation).symm y) := by
  cases p with
  | nil => cases hp
  | cons q e => exact (n.numbering_le_of_path q).trans_lt (n.adj_and_lt_of_hom e).2

/-! ### Monotone walks, source, sink, and directed reachability -/

/-- Every vertex `v ≠ t` is joined from `s` by a walk in `G` whose vertices all have numbers at
most `n.numbering v`. -/
theorem exists_walk_from_source_of_ne_sink (n : G.STNumbering s t) {v : V} (hvt : v ≠ t) :
    ∃ p : G.Walk s v, ∀ x ∈ p.support, n.numbering x ≤ n.numbering v := by
  induction hk : (n.numbering v).val using Nat.strongRec generalizing v with
  | ind k ih =>
    obtain rfl | hvs := eq_or_ne v s
    · refine ⟨.nil, fun x hx ↦ ?_⟩
      simp only [Walk.support_nil, List.mem_singleton] at hx
      rw [hx]
    · obtain ⟨u, hadj, hlt⟩ := n.lower_neighbor hvs hvt
      have hut : u ≠ t := n.lt_numbering_sink_iff.1 (hlt.trans_le (n.le_numbering_sink v))
      obtain ⟨p, hp⟩ := ih (n.numbering u).val (hk ▸ Fin.lt_def.1 hlt) hut rfl
      refine ⟨p.append hadj.toWalk, fun x hx ↦ ?_⟩
      simp only [Walk.mem_support_append_iff, Walk.support_cons, Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | rfl | rfl
      · exact (hp x hx).trans hlt.le
      · exact hlt.le
      · exact le_rfl

/-- Every vertex `v ≠ s` is joined to `t` by a walk in `G` whose vertices all have numbers at
least `n.numbering v`. -/
theorem exists_walk_to_sink_of_ne_source (n : G.STNumbering s t) {v : V} (hvs : v ≠ s) :
    ∃ p : G.Walk v t, ∀ x ∈ p.support, n.numbering v ≤ n.numbering x := by
  obtain ⟨p, hp⟩ := n.symm.exists_walk_from_source_of_ne_sink hvs
  refine ⟨p.reverse, fun x hx ↦ ?_⟩
  rw [Walk.support_reverse, List.mem_reverse] at hx
  exact Fin.rev_le_rev.1 (hp x hx)

/-- If `s` and `t` are adjacent, any graph admitting an `st`-numbering is preconnected. -/
theorem preconnected_of_adj (n : G.STNumbering s t) (hst : G.Adj s t) : G.Preconnected := by
  have hreach (v : V) : G.Reachable s v := by
    obtain rfl | hvt := eq_or_ne v t
    · exact hst.reachable
    · obtain ⟨p, -⟩ := n.exists_walk_from_source_of_ne_sink hvt
      exact ⟨p⟩
  exact fun u v ↦ (hreach u).symm.trans (hreach v)

/-- If `s` and `t` are adjacent, any graph admitting an `st`-numbering is connected. -/
theorem connected_of_adj (n : G.STNumbering s t) (hst : G.Adj s t) : G.Connected :=
  (connected_iff G).2 ⟨n.preconnected_of_adj hst, n.nonempty⟩

/-- On at least three vertices, any graph admitting an `st`-numbering is preconnected, even if `s`
and `t` are not adjacent. -/
theorem preconnected_of_three_le_card (n : G.STNumbering s t) (h3 : 3 ≤ Fintype.card V) :
    G.Preconnected := by
  let m : V := n.numbering.symm ⟨1, by omega⟩
  have hmv : (n.numbering m).val = 1 := by simp [m]
  have hms : m ≠ s := by
    rw [ne_eq, ← n.val_numbering_eq_zero_iff, hmv]
    omega
  have hmt : m ≠ t := by
    rw [ne_eq, ← n.val_numbering_eq_card_sub_one_iff, hmv]
    omega
  obtain ⟨ps, -⟩ := n.exists_walk_from_source_of_ne_sink hmt
  obtain ⟨pt, -⟩ := n.exists_walk_to_sink_of_ne_source hms
  have hst : G.Reachable s t := ⟨ps.append pt⟩
  have hreach (v : V) : G.Reachable s v := by
    obtain rfl | hvt := eq_or_ne v t
    · exact hst
    · obtain ⟨p, -⟩ := n.exists_walk_from_source_of_ne_sink hvt
      exact ⟨p⟩
  exact fun u v ↦ (hreach u).symm.trans (hreach v)

/-- On at least three vertices, any graph admitting an `st`-numbering is connected. -/
theorem connected_of_three_le_card (n : G.STNumbering s t) (h3 : 3 ≤ Fintype.card V) :
    G.Connected :=
  (connected_iff G).2 ⟨n.preconnected_of_three_le_card h3, n.nonempty⟩

/-- The source `s` has no incoming arrow in `OrientedQuiver G n.toOrientation`. -/
theorem isEmpty_hom_source (n : G.STNumbering s t) (x : OrientedQuiver G n.toOrientation) :
    IsEmpty (x ⟶ OrientedQuiver.vertex G n.toOrientation s) :=
  ⟨fun e ↦ by
    have hlt := (n.adj_and_lt_of_hom e).2
    rw [OrientedQuiver.vertexEquiv_symm_vertex] at hlt
    exact n.not_lt_numbering_source _ hlt⟩

/-- The sink `t` has no outgoing arrow in `OrientedQuiver G n.toOrientation`. -/
theorem isEmpty_hom_sink (n : G.STNumbering s t) (x : OrientedQuiver G n.toOrientation) :
    IsEmpty (OrientedQuiver.vertex G n.toOrientation t ⟶ x) :=
  ⟨fun e ↦ by
    have hlt := (n.adj_and_lt_of_hom e).2
    rw [OrientedQuiver.vertexEquiv_symm_vertex] at hlt
    exact n.not_numbering_sink_lt _ hlt⟩

/-- Every vertex `v ≠ t` is reachable from `s` in `OrientedQuiver G n.toOrientation` (with no
connectedness hypothesis on `G`). -/
theorem nonempty_path_from_source_of_ne_sink (n : G.STNumbering s t) {v : V} (hvt : v ≠ t) :
    Nonempty (Quiver.Path (OrientedQuiver.vertex G n.toOrientation s)
      (OrientedQuiver.vertex G n.toOrientation v)) := by
  induction hk : (n.numbering v).val using Nat.strongRec generalizing v with
  | ind k ih =>
    obtain rfl | hvs := eq_or_ne v s
    · exact ⟨.nil⟩
    · obtain ⟨u, hadj, hlt⟩ := n.lower_neighbor hvs hvt
      have hut : u ≠ t := n.lt_numbering_sink_iff.1 (hlt.trans_le (n.le_numbering_sink v))
      obtain ⟨p⟩ := ih (n.numbering u).val (hk ▸ Fin.lt_def.1 hlt) hut rfl
      exact ⟨p.cons (n.arrow hadj hlt)⟩

/-- Every vertex `v ≠ s` can reach `t` in `OrientedQuiver G n.toOrientation` (with no
connectedness hypothesis on `G`). -/
theorem nonempty_path_to_sink_of_ne_source (n : G.STNumbering s t) {v : V} (hvs : v ≠ s) :
    Nonempty (Quiver.Path (OrientedQuiver.vertex G n.toOrientation v)
      (OrientedQuiver.vertex G n.toOrientation t)) := by
  induction hk : Fintype.card V - 1 - (n.numbering v).val using Nat.strongRec generalizing v with
  | ind k ih =>
    obtain rfl | hvt := eq_or_ne v t
    · exact ⟨.nil⟩
    · obtain ⟨w, hadj, hlt⟩ := n.higher_neighbor hvs hvt
      have hws : w ≠ s := n.numbering_source_lt_iff.1 ((n.numbering_source_le v).trans_lt hlt)
      have hlt_val : (n.numbering v).val < (n.numbering w).val := Fin.lt_def.1 hlt
      have hw_bound : (n.numbering w).val < Fintype.card V := (n.numbering w).isLt
      obtain ⟨p⟩ := ih (Fintype.card V - 1 - (n.numbering w).val) (by omega) hws rfl
      exact ⟨(n.arrow hadj hlt).toPath.comp p⟩

/-- When `G` is preconnected, `OrientedQuiver G n.toOrientation` has a directed path from `s` to
`t`. -/
theorem nonempty_path_source_sink_of_preconnected (n : G.STNumbering s t) (hG : G.Preconnected) :
    Nonempty (Quiver.Path (OrientedQuiver.vertex G n.toOrientation s)
      (OrientedQuiver.vertex G n.toOrientation t)) := by
  obtain rfl | hst := eq_or_ne s t
  · exact ⟨.nil⟩
  · obtain ⟨w, hadj, -⟩ := Walk.exists_eq_cons_of_ne hst (hG s t).some
    obtain ⟨p⟩ := n.nonempty_path_to_sink_of_ne_source hadj.ne'
    exact ⟨(n.arrow hadj (n.numbering_source_lt_iff.2 hadj.ne')).toPath.comp p⟩

/-- When `G` is preconnected, every vertex of `OrientedQuiver G n.toOrientation` is reachable from
`s`. -/
theorem nonempty_path_from_source (n : G.STNumbering s t) (hG : G.Preconnected)
    (x : OrientedQuiver G n.toOrientation) :
    Nonempty (Quiver.Path (OrientedQuiver.vertex G n.toOrientation s) x) := by
  obtain ⟨v, rfl⟩ := (OrientedQuiver.vertexEquiv G n.toOrientation).surjective x
  rw [OrientedQuiver.vertexEquiv_apply]
  obtain rfl | hvt := eq_or_ne v t
  · exact n.nonempty_path_source_sink_of_preconnected hG
  · exact n.nonempty_path_from_source_of_ne_sink hvt

/-- When `G` is preconnected, every vertex of `OrientedQuiver G n.toOrientation` can reach `t`. -/
theorem nonempty_path_to_sink (n : G.STNumbering s t) (hG : G.Preconnected)
    (x : OrientedQuiver G n.toOrientation) :
    Nonempty (Quiver.Path x (OrientedQuiver.vertex G n.toOrientation t)) := by
  obtain ⟨v, rfl⟩ := (OrientedQuiver.vertexEquiv G n.toOrientation).surjective x
  rw [OrientedQuiver.vertexEquiv_apply]
  obtain rfl | hvs := eq_or_ne v s
  · exact n.nonempty_path_source_sink_of_preconnected hG
  · exact n.nonempty_path_to_sink_of_ne_source hvs

/-- When `G` is preconnected, `s` is the unique vertex of `OrientedQuiver G n.toOrientation` with
no incoming arrow. -/
theorem forall_isEmpty_hom_target_iff (n : G.STNumbering s t) (hG : G.Preconnected)
    (x : OrientedQuiver G n.toOrientation) :
    (∀ y, IsEmpty (y ⟶ x)) ↔ x = OrientedQuiver.vertex G n.toOrientation s := by
  refine ⟨fun h ↦ ?_, fun h y ↦ h ▸ n.isEmpty_hom_source y⟩
  obtain ⟨p⟩ := n.nonempty_path_from_source hG x
  cases p with
  | nil => rfl
  | cons _ e => exact ((h _).false e).elim

/-- When `G` is preconnected, `t` is the unique vertex of `OrientedQuiver G n.toOrientation` with
no outgoing arrow. -/
theorem forall_isEmpty_hom_source_iff (n : G.STNumbering s t) (hG : G.Preconnected)
    (x : OrientedQuiver G n.toOrientation) :
    (∀ y, IsEmpty (x ⟶ y)) ↔ x = OrientedQuiver.vertex G n.toOrientation t := by
  refine ⟨fun h ↦ ?_, fun h y ↦ h ▸ n.isEmpty_hom_sink y⟩
  by_contra hxt
  obtain ⟨v, rfl⟩ := (OrientedQuiver.vertexEquiv G n.toOrientation).surjective x
  rw [OrientedQuiver.vertexEquiv_apply] at hxt h
  have hvt : v ≠ t := by rintro rfl; exact hxt rfl
  obtain rfl | hvs := eq_or_ne v s
  · obtain ⟨w, hadj, -⟩ := Walk.exists_eq_cons_of_ne hvt (hG v t).some
    exact (h (OrientedQuiver.vertex G n.toOrientation w)).false
      (n.arrow hadj (n.numbering_source_lt_iff.2 hadj.ne'))
  · obtain ⟨w, hadj, hlt⟩ := n.higher_neighbor hvs hvt
    exact (h (OrientedQuiver.vertex G n.toOrientation w)).false (n.arrow hadj hlt)

/-- Transported through `OrientedQuiver.vertexEquiv`, when `G` is preconnected `s` is the unique
vertex `v : V` with no incoming arrow in `OrientedQuiver G n.toOrientation`. -/
theorem forall_isEmpty_vertexEquiv_hom_target_iff (n : G.STNumbering s t) (hG : G.Preconnected)
    {v : V} :
    (∀ u, IsEmpty (OrientedQuiver.vertexEquiv G n.toOrientation u ⟶
        OrientedQuiver.vertexEquiv G n.toOrientation v)) ↔ v = s := by
  let e := OrientedQuiver.vertexEquiv G n.toOrientation
  rw [← e.apply_eq_iff_eq (x := v) (y := s), OrientedQuiver.vertexEquiv_apply,
    OrientedQuiver.vertexEquiv_apply, ← n.forall_isEmpty_hom_target_iff hG]
  exact ⟨fun h y ↦ let ⟨u, hu⟩ := e.surjective y; hu ▸ h u, fun h u ↦ h (e u)⟩

/-- Transported through `OrientedQuiver.vertexEquiv`, when `G` is preconnected `t` is the unique
vertex `v : V` with no outgoing arrow in `OrientedQuiver G n.toOrientation`. -/
theorem forall_isEmpty_vertexEquiv_hom_source_iff (n : G.STNumbering s t) (hG : G.Preconnected)
    {v : V} :
    (∀ w, IsEmpty (OrientedQuiver.vertexEquiv G n.toOrientation v ⟶
        OrientedQuiver.vertexEquiv G n.toOrientation w)) ↔ v = t := by
  let e := OrientedQuiver.vertexEquiv G n.toOrientation
  rw [← e.apply_eq_iff_eq (x := v) (y := t), OrientedQuiver.vertexEquiv_apply,
    OrientedQuiver.vertexEquiv_apply, ← n.forall_isEmpty_hom_source_iff hG]
  exact ⟨fun h y ↦ let ⟨w, hw⟩ := e.surjective y; hw ▸ h w, fun h w ↦ h (e w)⟩

/-- Transported through `OrientedQuiver.vertexEquiv` and `STNumbering.homEquiv`, when `G` is
preconnected `s` is the unique vertex with no lower-numbered neighbour. -/
theorem forall_not_adj_and_numbering_lt_iff (n : G.STNumbering s t) (hG : G.Preconnected) {v : V} :
    (∀ u, ¬(G.Adj u v ∧ n.numbering u < n.numbering v)) ↔ v = s := by
  simpa only [OrientedQuiver.vertexEquiv_apply, n.isEmpty_hom_iff] using
    n.forall_isEmpty_vertexEquiv_hom_target_iff hG (v := v)

/-- Transported through `OrientedQuiver.vertexEquiv` and `STNumbering.homEquiv`, when `G` is
preconnected `t` is the unique vertex with no higher-numbered neighbour. -/
theorem forall_not_adj_and_lt_numbering_iff (n : G.STNumbering s t) (hG : G.Preconnected) {v : V} :
    (∀ w, ¬(G.Adj v w ∧ n.numbering v < n.numbering w)) ↔ v = t := by
  simpa only [OrientedQuiver.vertexEquiv_apply, n.isEmpty_hom_iff] using
    n.forall_isEmpty_vertexEquiv_hom_source_iff hG (v := v)

/-! ### `2`-vertex-connectivity from an `st`-numbering -/

/-- Avoiding any single vertex `z`, every remaining vertex `v ≠ z` has a walk in
`G ⊔ SimpleGraph.edge s t` to `s` (when `z ≠ s`) or to `t` (when `z = s`). -/
private theorem exists_walk_avoiding_singleton (n : G.STNumbering s t) (hst : s ≠ t) (z : V) :
    ∃ r, r ≠ z ∧ ∀ ⦃v⦄, v ≠ z → ∃ p : (G ⊔ SimpleGraph.edge s t).Walk v r, z ∉ p.support := by
  by_cases hzs : z = s
  · subst hzs
    refine ⟨t, hst.symm, fun v hv ↦ ?_⟩
    obtain ⟨p, hp⟩ := n.exists_walk_to_sink_of_ne_source hv
    refine ⟨p.mapLe le_sup_left, ?_⟩
    rw [Walk.support_mapLe_eq_support]
    exact fun hs ↦ (n.numbering_source_lt_iff.2 hv).not_ge (hp z hs)
  · refine ⟨s, Ne.symm hzs, fun v hv ↦ ?_⟩
    by_cases hzt : z = t
    · subst hzt
      obtain ⟨p, hp⟩ := n.exists_walk_from_source_of_ne_sink hv
      refine ⟨p.reverse.mapLe le_sup_left, ?_⟩
      rw [Walk.support_mapLe_eq_support, Walk.support_reverse, List.mem_reverse]
      exact fun ht ↦ (n.lt_numbering_sink_iff.2 hv).not_ge (hp z ht)
    · rcases lt_or_gt_of_ne (n.injective.ne hv) with hlt | hgt
      · have hvt : v ≠ t := n.lt_numbering_sink_iff.1 (hlt.trans_le (n.le_numbering_sink z))
        obtain ⟨p, hp⟩ := n.exists_walk_from_source_of_ne_sink hvt
        refine ⟨p.reverse.mapLe le_sup_left, ?_⟩
        rw [Walk.support_mapLe_eq_support, Walk.support_reverse, List.mem_reverse]
        exact fun hz ↦ hlt.not_ge (hp z hz)
      · have hvs : v ≠ s := n.numbering_source_lt_iff.1 ((n.numbering_source_le z).trans_lt hgt)
        obtain ⟨p, hp⟩ := n.exists_walk_to_sink_of_ne_source hvs
        have hadj : (G ⊔ SimpleGraph.edge s t).Adj t s :=
          .inr ((edge_adj s t t s).2 ⟨.inr ⟨rfl, rfl⟩, hst.symm⟩)
        refine ⟨(p.mapLe le_sup_left).append hadj.toWalk, ?_⟩
        rw [Walk.mem_support_append_iff, Walk.support_mapLe_eq_support]
        rintro (hz | hz)
        · exact hgt.not_ge (hp z hz)
        · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
            or_false] at hz
          rcases hz with rfl | rfl
          exacts [hzt rfl, hzs rfl]

/-- On at least three vertices, admitting an `st`-numbering makes `G ⊔ SimpleGraph.edge s t`
`2`-vertex-connected. -/
theorem isVertexConnected_two_sup_edge (n : G.STNumbering s t) (h3 : 3 ≤ Fintype.card V) :
    (G ⊔ SimpleGraph.edge s t).IsVertexConnected 2 := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hst : s ≠ t := n.source_ne_sink
  refine isVertexConnected_def.2
    ⟨by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast h3, fun a b ↦ ?_⟩
  rw [isVertexReachable_iff_exists_walk]
  intro S hS ha hb
  -- Either `S` has a unique vertex `z`, or `S = ∅` and we pick a dummy vertex `z ∉ {a, b}`.
  have hex : ∃ z : V, z ≠ a ∧ z ≠ b ∧ ∀ x ∈ S, x = z := by
    rcases S.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · classical
      have hcard : #({a, b} : Finset V) < #(univ : Finset V) := by
        have hle2 : #({a, b} : Finset V) ≤ 2 := (card_insert_le a {b}).trans (by simp)
        rw [card_univ]
        omega
      obtain ⟨z, -, hz⟩ := exists_mem_notMem_of_card_lt_card hcard
      simp only [mem_insert, mem_singleton, not_or] at hz
      exact ⟨z, hz.1, hz.2, by simp⟩
    · have hle : S.encard ≤ 1 := by simpa using hS
      refine ⟨z, fun h ↦ ha (h ▸ hz), fun h ↦ hb (h ▸ hz), fun x hx ↦ ?_⟩
      exact (Set.encard_le_one_iff.1 hle) x z hx hz
  obtain ⟨z, hza, hzb, hSz⟩ := hex
  obtain ⟨r, -, hr⟩ := n.exists_walk_avoiding_singleton hst z
  obtain ⟨pa, hpa⟩ := hr hza.symm
  obtain ⟨pb, hpb⟩ := hr hzb.symm
  refine ⟨pa.append pb.reverse, fun x hx hxS ↦ ?_⟩
  have hxz : x = z := hSz x hxS
  subst hxz
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hx
  exact hx.elim hpa hpb

/-- On at least three vertices with `G.Adj s t`, admitting an `st`-numbering makes `G` itself
`2`-vertex-connected. -/
theorem isVertexConnected_two (n : G.STNumbering s t) (h3 : 3 ≤ Fintype.card V)
    (hst : G.Adj s t) : G.IsVertexConnected 2 := by
  have hsup : G ⊔ SimpleGraph.edge s t = G := sup_eq_left.2 ((edge_le_iff G).2 (.inr hst))
  exact hsup ▸ n.isVertexConnected_two_sup_edge h3

end STNumbering

/-! ### Existence of `st`-numberings via open-ear insertion -/

section Existence

/-- A partial `st`-numbering stored as a duplicate-free vertex list starting with `s` and ending
with `t`, in which every intermediate vertex already has a predecessor neighbour and a successor
neighbour in sublist order. -/
private structure IsPartialSTList (G : SimpleGraph V) (s t : V) (L : List V) : Prop where
  nodup : L.Nodup
  head?_eq : L.head? = some s
  getLast?_eq : L.getLast? = some t
  lower : ∀ ⦃v⦄, v ∈ L → v ≠ s → v ≠ t → ∃ u, G.Adj u v ∧ [u, v] <+ L
  higher : ∀ ⦃v⦄, v ∈ L → v ≠ s → v ≠ t → ∃ w, G.Adj v w ∧ [v, w] <+ L

private theorem isPartialSTList_pair {G : SimpleGraph V} {s t : V} (hst : s ≠ t) :
    IsPartialSTList G s t [s, t] where
  nodup := by simp [hst]
  head?_eq := rfl
  getLast?_eq := rfl
  lower v hv hvs hvt := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    exact hv.elim (fun h ↦ (hvs h).elim) (fun h ↦ (hvt h).elim)
  higher v hv hvs hvt := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    exact hv.elim (fun h ↦ (hvs h).elim) (fun h ↦ (hvt h).elim)

/-- Decompose the support of a nontrivial simple path `R : G.Walk a b` as `a :: (I ++ [b])`, where
`I` is duplicate-free and contains neither endpoint, and every vertex of `I` has an adjacent
predecessor and an adjacent successor in `R.support`. -/
private theorem exists_internal_support_of_isPath {G : SimpleGraph V} {a b : V} {R : G.Walk a b}
    (hR : R.IsPath) (hab : a ≠ b) :
    ∃ I : List V, R.support = a :: (I ++ [b]) ∧ I.Nodup ∧ (∀ v ∈ I, v ≠ a ∧ v ≠ b) ∧
      (∀ v ∈ I, (∃ u, G.Adj u v ∧ [u, v] <+ R.support) ∧
        (∃ w, G.Adj v w ∧ [v, w] <+ R.support)) := by
  have hRnil : ¬R.Nil := fun h ↦ hab h.eq
  let I := R.support.tail.dropLast
  have htail_ne : R.support.tail ≠ [] := List.ne_nil_of_mem (R.end_mem_tail_support hRnil)
  have htail_last : R.support.tail.getLast htail_ne = b := by
    have h2 : (a :: R.support.tail).getLast (List.cons_ne_nil _ _) = b := by
      simpa only [Walk.cons_tail_support] using R.getLast_support
    simpa only [List.getLast_cons htail_ne] using h2
  have hsupp_eq : R.support = a :: (I ++ [b]) := by
    rw [← R.cons_tail_support]
    congr 1
    simpa only [I, htail_last] using (List.dropLast_concat_getLast htail_ne).symm
  have hsupp_nd : (a :: (I ++ [b])).Nodup := hsupp_eq ▸ hR.support_nodup
  refine ⟨I, hsupp_eq, (List.nodup_cons.1 hsupp_nd).2.of_append_left, fun v hvI ↦ ?_,
    fun v hvI ↦ ?_⟩
  · refine ⟨fun h ↦ (List.nodup_cons.1 hsupp_nd).1 (List.mem_append_left _ (h ▸ hvI)), ?_⟩
    rintro rfl
    exact (List.nodup_cons.1 hsupp_nd).2.disjoint hvI (List.mem_singleton_self v)
  · obtain ⟨I₁, I₂, hI_eq⟩ := List.mem_iff_append.1 hvI
    have h₁ : a :: I₁ ≠ [] := List.cons_ne_nil _ _
    have h₂ : (a :: I₁) ++ [v] ≠ [] := by simp
    have h₃ : I₂ ++ [b] ≠ [] := by simp
    have hchain₁ : ((a :: I₁) ++ (v :: (I₂ ++ [b]))).IsChain G.Adj := by
      simpa [hsupp_eq, hI_eq, List.cons_append, List.append_assoc] using R.isChain_adj_support
    have hchain₂ : (((a :: I₁) ++ [v]) ++ (I₂ ++ [b])).IsChain G.Adj := by
      simpa [hsupp_eq, hI_eq, List.cons_append, List.append_assoc] using R.isChain_adj_support
    refine ⟨⟨(a :: I₁).getLast h₁,
      by simpa using hchain₁.rel_getLast_head_of_append h₁ (List.cons_ne_nil _ _), ?_⟩,
      ⟨(I₂ ++ [b]).head h₃, by simpa using hchain₂.rel_getLast_head_of_append h₂ h₃, ?_⟩⟩
    · rw [hsupp_eq, hI_eq]
      have hs₁ : [(a :: I₁).getLast h₁] <+ a :: I₁ :=
        List.singleton_sublist.2 (List.getLast_mem h₁)
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        hs₁.append (by simp : [v] <+ v :: (I₂ ++ [b]))
    · rw [hsupp_eq, hI_eq]
      have hs₂ : [(I₂ ++ [b]).head h₃] <+ I₂ ++ [b] := List.singleton_sublist.2 (List.head_mem h₃)
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        (by simp : [v] <+ (a :: I₁) ++ [v]).append hs₂

/-- Inserting the internal vertices of a `G`-path `R` from `a` to `b` immediately after `a` in
`L = A ++ a :: B` (where `b ∈ B` and all internal vertices of `R` lie outside `L`) extends the
partial `st`-list to one containing `R.support`. -/
private theorem IsPartialSTList.insertPath {G : SimpleGraph V} {s t a b : V} {A B : List V}
    (hL : IsPartialSTList G s t (A ++ a :: B)) (hbB : b ∈ B) (R : G.Walk a b) (hR : R.IsPath)
    (hint : ∀ v ∈ R.support, v ≠ a → v ≠ b → v ∉ A ++ a :: B) :
    ∃ L' : List V, IsPartialSTList G s t L' ∧ (A ++ a :: B) <+ L' ∧
      ∀ v ∈ R.support, v ∈ L' := by
  set L := A ++ a :: B
  have hab : a ≠ b := by
    rintro rfl
    have hnd := hL.nodup
    simp only [L, List.nodup_append, List.nodup_cons] at hnd
    exact hnd.2.1.1 hbB
  obtain ⟨I, hsupp_eq, hI_nd, hI_ne, hI_nbrs⟩ := exists_internal_support_of_isPath hR hab
  have hIL : List.Disjoint I L := fun v hvI ↦
    hint v (hsupp_eq ▸ List.mem_cons_of_mem a (List.mem_append_left _ hvI))
      (hI_ne v hvI).1 (hI_ne v hvI).2
  set L' := A ++ a :: (I ++ B)
  have hLL' : L <+ L' := (List.sublist_append_right I B).cons_cons a |>.append_left A
  have hRL' : R.support <+ L' := by
    rw [hsupp_eq]
    exact (((List.singleton_sublist.2 hbB).append_left I).cons_cons a).trans
      (List.sublist_append_right A _)
  have hB_ne : B ≠ [] := List.ne_nil_of_mem hbB
  refine ⟨L', ?_, hLL', fun v hv ↦ hRL'.subset hv⟩
  refine
    { nodup := ?_
      head?_eq := by cases A <;> simpa [L, L'] using hL.head?_eq
      getLast?_eq := by
        have hL_eq : L = (A ++ [a]) ++ B := by simp [L]
        have hL'_eq : L' = (A ++ a :: I) ++ B := by simp [L']
        have hlastL : L.getLast? = B.getLast? := by
          rw [hL_eq, List.getLast?_append_of_ne_nil _ hB_ne]
        have hlastL' : L'.getLast? = B.getLast? := by
          rw [hL'_eq, List.getLast?_append_of_ne_nil _ hB_ne]
        rw [hlastL', ← hlastL, hL.getLast?_eq]
      lower := fun v hv hvs hvt ↦ ?_
      higher := fun v hv hvs hvt ↦ ?_ }
  · have hperm : L' ~ I ++ L := by
      calc
        A ++ a :: (I ++ B) ~ a :: (I ++ B) ++ A := List.perm_append_comm
        _ = a :: (I ++ (B ++ A)) := by simp [List.append_assoc]
        _ ~ I ++ a :: (B ++ A) := List.perm_middle.symm
        _ ~ I ++ (A ++ a :: B) := List.Perm.append_left I
          (by simpa [List.cons_append, List.append_assoc] using
            (List.perm_append_comm (l₁ := a :: B) (l₂ := A)))
    exact hperm.symm.nodup_iff.1 (hI_nd.append hL.nodup hIL)
  · have hv_split : v ∈ L ∨ v ∈ I := by
      simp only [L, L', List.mem_append, List.mem_cons] at hv ⊢; tauto
    refine hv_split.elim (fun hvL ↦ ?_) (fun hvI ↦ ?_)
    · obtain ⟨u, hadj, huv⟩ := hL.lower hvL hvs hvt
      exact ⟨u, hadj, huv.trans hLL'⟩
    · obtain ⟨u, hadj, huv⟩ := (hI_nbrs v hvI).1
      exact ⟨u, hadj, huv.trans hRL'⟩
  · have hv_split : v ∈ L ∨ v ∈ I := by
      simp only [L, L', List.mem_append, List.mem_cons] at hv ⊢; tauto
    refine hv_split.elim (fun hvL ↦ ?_) (fun hvI ↦ ?_)
    · obtain ⟨w, hadj, hvw⟩ := hL.higher hvL hvs hvt
      exact ⟨w, hadj, hvw.trans hLL'⟩
    · obtain ⟨w, hadj, hvw⟩ := (hI_nbrs v hvI).2
      exact ⟨w, hadj, hvw.trans hRL'⟩

/-- Convert a complete `IsPartialSTList` covering all of `V` into an `STNumbering`. -/
private def IsPartialSTList.toSTNumbering [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {s t : V} {L : List V} (hL : IsPartialSTList G s t L) (hall : ∀ v : V, v ∈ L) :
    G.STNumbering s t := by
  let e : Fin L.length ≃ V := hL.nodup.getEquivOfForallMemList L hall
  have hcard : L.length = Fintype.card V := by
    rw [← Fintype.card_fin L.length]
    exact Fintype.card_congr e
  let num : V ≃ Fin (Fintype.card V) := e.symm.trans (finCongr hcard)
  have hlt_of_sublist {u v : V} (huv : [u, v] <+ L) : num u < num v := by
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.1 huv
    let i0 : Fin [u, v].length := ⟨0, by simp⟩
    let i1 : Fin [u, v].length := ⟨1, by simp⟩
    have hu : e (f i0) = u := by simpa [e, i0] using (hf i0).symm
    have hv : e (f i1) = v := by simpa [e, i1] using (hf i1).symm
    have h01 : f i0 < f i1 := f.lt_iff_lt.2 (Fin.mk_lt_mk.2 Nat.zero_lt_one)
    have hu' : e.symm u = f i0 := e.symm_apply_eq.2 hu.symm
    have hv' : e.symm v = f i1 := e.symm_apply_eq.2 hv.symm
    simp only [num, Equiv.trans_apply, finCongr_apply, Fin.lt_def, Fin.val_cast, hu', hv']
    exact Fin.lt_def.1 h01
  have hne : L ≠ [] := List.ne_nil_of_mem (List.mem_of_mem_head? hL.head?_eq)
  refine
    { numbering := num
      source_first := ?_
      sink_last := ?_
      lower_neighbor := fun v hvs hvt ↦
        let ⟨u, hadj, huv⟩ := hL.lower (hall v) hvs hvt
        ⟨u, hadj, hlt_of_sublist huv⟩
      higher_neighbor := fun v hvs hvt ↦
        let ⟨w, hadj, hvw⟩ := hL.higher (hall v) hvs hvt
        ⟨w, hadj, hlt_of_sublist hvw⟩ }
  · obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.1 hL.head?_eq
    have hs : e ⟨0, by simp [htail]⟩ = s := by simp [e, htail]
    have hs' : e.symm s = ⟨0, by simp [htail]⟩ := e.symm_apply_eq.2 hs.symm
    simp only [num, Equiv.trans_apply, finCongr_apply, Fin.val_cast, hs']
  · have hpos : 0 < L.length := List.length_pos_of_ne_nil hne
    have hlast : L.getLast hne = t := Option.some.inj (List.getLast?_eq_some_getLast hne ▸
      hL.getLast?_eq)
    have ht : e ⟨L.length - 1, Nat.sub_lt hpos Nat.one_pos⟩ = t := by
      simpa [e, List.getLast_eq_getElem] using hlast
    have ht' : e.symm t = ⟨L.length - 1, Nat.sub_lt hpos Nat.one_pos⟩ :=
      e.symm_apply_eq.2 ht.symm
    simp only [num, Equiv.trans_apply, finCongr_apply, Fin.val_cast, ht']
    omega

/-- Given `s ≠ t` inside `U : Finset V` and a vertex `x ∉ U`, `2`-vertex-connectivity of
`G ⊔ edge s t` produces an open ear in `G` itself passing through `x` between two distinct
endpoints in `U`, with all internal vertices outside `U`. -/
private theorem exists_open_ear_of_isVertexConnected_two_sup_edge [Finite V]
    {G : SimpleGraph V} {s t x : V} {U : Finset V} (hst : s ≠ t) (hsU : s ∈ U) (htU : t ∈ U)
    (hxU : x ∉ U) (hG : (G ⊔ SimpleGraph.edge s t).IsVertexConnected 2) :
    ∃ (u₀ u₁ : V) (R : G.Walk u₀ u₁), u₀ ∈ U ∧ u₁ ∈ U ∧ u₀ ≠ u₁ ∧ R.IsPath ∧ x ∈ R.support ∧
      ∀ v ∈ R.support, v ≠ u₀ → v ≠ u₁ → v ∉ U := by
  classical
  have hU2 : 2 ≤ #U := Finset.one_lt_card.2 ⟨s, hsU, t, htU, hst⟩
  obtain ⟨u, P, hinj, hu, hP, hint, hdisj⟩ := hG.exists_fan hxU hU2
  have htransfer (i : Fin 2) : ∀ e ∈ (P i).edges, e ∈ G.edgeSet := by
    intro e he
    induction e with | h v w => ?_
    refine ((P i).adj_of_mem_edges he).elim id fun hedge ↦ False.elim ?_
    rw [edge_adj] at hedge
    have hvU : v ∈ U := by rcases hedge.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hwU : w ∈ U := by rcases hedge.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hvu : v = u i := by
      by_contra hne
      exact hint i v ((P i).fst_mem_support_of_mem_edges he) hne hvU
    have hwu : w = u i := by
      by_contra hne
      exact hint i w ((P i).snd_mem_support_of_mem_edges he) hne hwU
    exact hedge.2 (hvu.trans hwu.symm)
  let Q : ∀ i : Fin 2, G.Walk x (u i) := fun i ↦ (P i).transfer G (htransfer i)
  have hQ_supp (i : Fin 2) : (Q i).support = (P i).support := Walk.support_transfer _ _
  have hQ_path (i : Fin 2) : (Q i).IsPath := (Q i).isPath_def.2 (hQ_supp i ▸ (hP i).support_nodup)
  let R₀ : G.Walk (u 0) (u 1) := (Q 0).reverse.append (Q 1)
  refine ⟨u 0, u 1, R₀, hu 0, hu 1, hinj.ne (by decide), ?_,
    (Walk.mem_support_append_iff _ _).2 (.inr (Q 1).start_mem_support), fun v hv h0 h1 hvU ↦ ?_⟩
  · refine (Walk.isPath_append _ _).2 ⟨(hQ_path 0).reverse, (hQ_path 1).tail, fun v hv₀ hv₁ ↦ ?_⟩
    rw [Walk.support_reverse, List.mem_reverse, hQ_supp] at hv₀
    have hvx : v = x :=
      hdisj (by decide : (0 : Fin 2) ≠ 1) v hv₀ (hQ_supp 1 ▸ List.mem_of_mem_tail hv₁)
    exact (hQ_path 1).start_notMem_tail_support (hvx ▸ hv₁)
  · rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse, hQ_supp,
      hQ_supp] at hv
    exact hv.elim (fun h ↦ hint 0 v h h0 hvU) (fun h ↦ hint 1 v h h1 hvU)

/-- **Lempel–Even–Cederbaum theorem (existence).** Let `s ≠ t` be distinct vertices of a finite
simple graph `G` such that `G ⊔ SimpleGraph.edge s t` is `2`-vertex-connected. Then `G` admits an
`st`-numbering. -/
theorem nonempty_stNumbering_of_isVertexConnected_two_sup_edge [Fintype V] {G : SimpleGraph V}
    {s t : V} (hst : s ≠ t) (hG : (G ⊔ SimpleGraph.edge s t).IsVertexConnected 2) :
    Nonempty (G.STNumbering s t) := by
  classical
  -- Induct downward on `Fintype.card V - L.length` to grow `[s, t]` to a full vertex list.
  suffices ∀ (k : ℕ) (L : List V), IsPartialSTList G s t L → Fintype.card V - L.length = k →
      Nonempty (G.STNumbering s t) by
    exact this _ [s, t] (isPartialSTList_pair hst) rfl
  intro k
  induction k using Nat.strongRec with
  | ind k ih =>
    intro L hL hk
    by_cases hall : ∀ v : V, v ∈ L
    · exact ⟨hL.toSTNumbering hall⟩
    · push Not at hall
      obtain ⟨x, hxL⟩ := hall
      obtain ⟨u₀, u₁, R₀, hu₀, hu₁, hu₀₁, hR₀_path, hxR₀, hR₀_int⟩ :=
        exists_open_ear_of_isVertexConnected_two_sup_edge hst
          (List.mem_toFinset.2 (List.mem_of_mem_head? hL.head?_eq))
          (List.mem_toFinset.2 (List.mem_of_mem_getLast? hL.getLast?_eq))
          (List.mem_toFinset.not.2 hxL) hG
      obtain ⟨A₀, B₀, hLA₀⟩ := List.mem_iff_append.1 (List.mem_toFinset.1 hu₀)
      have hu₁_mem : u₁ ∈ A₀ ∨ u₁ ∈ B₀ := by
        have h1 := List.mem_toFinset.1 hu₁
        rw [hLA₀, List.mem_append, List.mem_cons] at h1
        exact h1.elim .inl fun h ↦ .inr (h.resolve_left hu₀₁.symm)
      have hsplit : ∃ (a b : V) (A B : List V) (R : G.Walk a b),
          L = A ++ a :: B ∧ b ∈ B ∧ R.IsPath ∧ x ∈ R.support ∧
            ∀ v ∈ R.support, v ≠ a → v ≠ b → v ∉ L := by
        rcases hu₁_mem with hA | hB
        · obtain ⟨A₁, B₁, rfl⟩ := List.mem_iff_append.1 hA
          refine ⟨u₁, u₀, A₁, B₁ ++ u₀ :: B₀, R₀.reverse, by simp [hLA₀, List.append_assoc],
            by simp, hR₀_path.reverse, by simpa using hxR₀, fun v hv h1 h0 hvL ↦ ?_⟩
          rw [Walk.support_reverse, List.mem_reverse] at hv
          exact hR₀_int v hv h0 h1 (List.mem_toFinset.2 hvL)
        · exact ⟨u₀, u₁, A₀, B₀, R₀, hLA₀, hB, hR₀_path, hxR₀,
            fun v hv h0 h1 hvL ↦ hR₀_int v hv h0 h1 (List.mem_toFinset.2 hvL)⟩
      obtain ⟨a, b, A, B, R, rfl, hbB, hR_path, hxR, hR_int⟩ := hsplit
      obtain ⟨L', hL', hLL', hRL'⟩ := hL.insertPath hbB R hR_path hR_int
      have hssub : (A ++ a :: B).toFinset ⊂ L'.toFinset :=
        (ssubset_iff_of_subset fun y hy ↦
          List.mem_toFinset.2 (hLL'.subset (List.mem_toFinset.1 hy))).2
          ⟨x, List.mem_toFinset.2 (hRL' x hxR), List.mem_toFinset.not.2 hxL⟩
      have hlt_len : (A ++ a :: B).length < L'.length := by
        simpa only [List.toFinset_card_of_nodup hL.nodup,
          List.toFinset_card_of_nodup hL'.nodup] using card_lt_card hssub
      have hle_card : L'.length ≤ Fintype.card V := by
        simpa only [List.toFinset_card_of_nodup hL'.nodup, card_univ] using
          card_le_univ L'.toFinset
      exact ih (Fintype.card V - L'.length) (by omega) L' hL' rfl

/-- Any `2`-vertex-connected finite simple graph admits an `st`-numbering between any two distinct
vertices `s ≠ t`. -/
theorem IsVertexConnected.nonempty_stNumbering_of_ne [Fintype V] {G : SimpleGraph V}
    (hG : G.IsVertexConnected 2) {s t : V} (hst : s ≠ t) :
    Nonempty (G.STNumbering s t) :=
  nonempty_stNumbering_of_isVertexConnected_two_sup_edge hst (hG.mono le_sup_left)

/-- Any `2`-vertex-connected finite simple graph admits an `st`-numbering across any chosen edge
`G.Adj s t`. -/
theorem IsVertexConnected.nonempty_stNumbering [Fintype V] {G : SimpleGraph V}
    (hG : G.IsVertexConnected 2) {s t : V} (hst : G.Adj s t) :
    Nonempty (G.STNumbering s t) :=
  hG.nonempty_stNumbering_of_ne hst.ne

/-- **Lempel–Even–Cederbaum theorem.** On a finite vertex type with at least three vertices, a
simple graph `G` admits an `st`-numbering for distinct vertices `s ≠ t` if and only if
`G ⊔ SimpleGraph.edge s t` is `2`-vertex-connected. -/
theorem nonempty_stNumbering_iff_isVertexConnected_two_sup_edge [Fintype V] {G : SimpleGraph V}
    (h3 : 3 ≤ Fintype.card V) {s t : V} (hst : s ≠ t) :
    Nonempty (G.STNumbering s t) ↔ (G ⊔ SimpleGraph.edge s t).IsVertexConnected 2 :=
  ⟨fun ⟨n⟩ ↦ n.isVertexConnected_two_sup_edge h3,
    nonempty_stNumbering_of_isVertexConnected_two_sup_edge hst⟩

/-- **Lempel–Even–Cederbaum theorem for adjacent endpoints.** On a finite vertex type with at least
three vertices, a simple graph `G` with `G.Adj s t` admits an `st`-numbering if and only if `G` is
`2`-vertex-connected. -/
theorem nonempty_stNumbering_iff_isVertexConnected_two [Fintype V] {G : SimpleGraph V}
    (h3 : 3 ≤ Fintype.card V) {s t : V} (hst : G.Adj s t) :
    Nonempty (G.STNumbering s t) ↔ G.IsVertexConnected 2 :=
  ⟨fun ⟨n⟩ ↦ n.isVertexConnected_two h3 hst, fun hG ↦ hG.nonempty_stNumbering hst⟩

end Existence

end SimpleGraph

