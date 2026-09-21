/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mathlib.Data.Set.BoolIndicator
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import TauCeti.Combinatorics.SimpleGraph.Measurable
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Edge coordinates of an infinite simple graph

An infinite simple graph is equivalently a Boolean assignment to the unordered, non-diagonal
pairs of natural numbers.  This file makes that equivalence measurable and records its
equivariance under relabelling.  It is the carrier-level bridge between laws on infinite simple
graphs and laws on jointly exchangeable symmetric, irreflexive Boolean arrays.

Finite measures on infinite graphs are determined by the laws of all their finite vertex windows:
every finite collection of edge coordinates lies in one such window, so projective-limit
uniqueness applies after transporting the measures through the coordinate equivalence.

The coordinate type excludes diagonal pairs, rather than imposing an irreflexivity condition on a
two-dimensional array.  Consequently every Boolean assignment is a graph, and relabelling acts by
an honest equivalence of coordinates.

## Main definitions

* `TauCeti.DenseGraphLimits.EdgeIndex` is the type of unordered non-diagonal pairs of naturals;
* `TauCeti.DenseGraphLimits.graphCoordEquiv` identifies infinite graphs with Boolean edge
  coordinates;
* `Equiv.Perm.edgeIndexMap` is the coordinate relabelling induced by a permutation of the vertices.

## Main results

* `TauCeti.DenseGraphLimits.measurable_graphCoordEquiv` and
  `TauCeti.DenseGraphLimits.measurable_graphCoordEquiv_symm` show that the coordinate equivalence
  is measurable in both directions;
* `TauCeti.DenseGraphLimits.measure_ext_of_map_restrictFin` shows that a finite measure on infinite
  graphs is determined by its finite windows;
* `Equiv.Perm.graphCoordEquiv_comap` is the relabelling commuting square.

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

/-- An infinite simple graph is equivalently a Boolean assignment to its possible edges. -/
def graphCoordEquiv : SimpleGraph ℕ ≃ (EdgeIndex → Bool) where
  toFun G e := G.edgeSet.boolIndicator e.1
  invFun f := SimpleGraph.fromEdgeSet {s : Sym2 ℕ | ∃ h : ¬ s.IsDiag, f ⟨s, h⟩ = true}
  left_inv G := by
    -- The coordinate predicate cuts out exactly `G.edgeSet`, so `fromEdgeSet_edgeSet` applies.
    refine Eq.trans ?_ (SimpleGraph.fromEdgeSet_edgeSet G)
    refine congrArg SimpleGraph.fromEdgeSet (Set.ext fun s => ?_)
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, h⟩ => (Set.mem_iff_boolIndicator _ _).mpr h,
      fun hs => ⟨G.not_isDiag_of_mem_edgeSet hs, (Set.mem_iff_boolIndicator _ _).mp hs⟩⟩
  right_inv f := by
    funext e
    -- Both sides are Boolean, so compare them through membership in the decoded edge set.
    rw [Bool.eq_iff_iff, ← Set.mem_iff_boolIndicator]
    simp only [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_ofPred_eq,
      Sym2.mem_diagSet]
    exact ⟨fun ⟨⟨h, htrue⟩, _⟩ => (Subtype.ext rfl : (⟨(e : Sym2 ℕ), h⟩ : EdgeIndex) = e) ▸ htrue,
      fun htrue => ⟨⟨e.2, htrue⟩, e.2⟩⟩

end DenseGraphLimits

end TauCeti

namespace SimpleGraph

open TauCeti.DenseGraphLimits

/-- The coordinate at `e` is true exactly when `e` is an edge of the graph. -/
@[simp]
theorem graphCoordEquiv_apply (G : SimpleGraph ℕ) (e : EdgeIndex) :
    graphCoordEquiv G e = true ↔ e.1 ∈ G.edgeSet :=
  (Set.mem_iff_boolIndicator _ _).symm

end SimpleGraph

namespace TauCeti

namespace DenseGraphLimits

open MeasureTheory

/-- An edge coordinate is an edge of the decoded graph exactly when its value is true. -/
@[simp]
theorem mem_edgeSet_graphCoordEquiv_symm (f : EdgeIndex → Bool) (e : EdgeIndex) :
    e.1 ∈ (graphCoordEquiv.symm f).edgeSet ↔ f e = true := by
  rw [← SimpleGraph.graphCoordEquiv_apply, Equiv.apply_symm_apply]

/-- The graph-to-coordinate map is measurable for Mathlib's adjacency-generated measurable space
on simple graphs and the product measurable space on Boolean coordinates. -/
@[fun_prop]
theorem measurable_graphCoordEquiv : Measurable ⇑graphCoordEquiv := by
  rw [measurable_pi_iff]
  intro e
  refine measurable_to_bool ?_
  have hpre : (fun G : SimpleGraph ℕ => graphCoordEquiv G e) ⁻¹' {true} =
      {G : SimpleGraph ℕ | e.1 ∈ G.edgeSet} := Set.ext fun G =>
    SimpleGraph.graphCoordEquiv_apply G e
  rw [hpre]
  exact (measurable_set_iff.1 SimpleGraph.measurable_edgeSet e.1).setOf

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

/-! ### Edge-coordinate windows -/

/-- The edge coordinates both of whose endpoints are below `n`. -/
def edgeWindow (n : ℕ) : Finset EdgeIndex :=
  (Finset.range n).sym2.subtype fun e => ¬ e.IsDiag

/-- Membership in `edgeWindow n` means that both endpoints are below `n`. -/
@[simp]
theorem mem_edgeWindow {n : ℕ} {e : EdgeIndex} :
    e ∈ edgeWindow n ↔ ∀ a ∈ e.1, a < n := by
  simp [edgeWindow, Finset.mem_sym2_iff]

/-- A bound below which all endpoints of the coordinates in `J` lie. -/
def windowBound (J : Finset EdgeIndex) : ℕ :=
  J.sup fun e => e.1.sup + 1

/-- Every coordinate in a finite set lies in the window at its `windowBound`. -/
theorem subset_edgeWindow_windowBound (J : Finset EdgeIndex) :
    J ⊆ edgeWindow (windowBound J) := by
  intro e he
  refine mem_edgeWindow.2 fun a ha => Nat.lt_of_lt_of_le ?_
    (Finset.le_sup (f := fun e : EdgeIndex => e.1.sup + 1) he)
  obtain ⟨s, hs⟩ := e
  induction s using Sym2.ind with
  | _ x y =>
    rcases Sym2.mem_iff.1 ha with rfl | rfl <;> simp

/-- The edge coordinates of a graph on `Fin n`, with its labels read in `ℕ`. -/
def windowCoord {n : ℕ} (H : SimpleGraph (Fin n)) : EdgeIndex → Bool :=
  graphCoordEquiv (H.map Fin.valEmbedding)

/-- A finite graph's window coordinates are those of its embedding into the natural labels. -/
@[simp]
theorem windowCoord_apply {n : ℕ} (H : SimpleGraph (Fin n)) (e : EdgeIndex) :
    windowCoord H e = graphCoordEquiv (H.map Fin.valEmbedding) e := (rfl)

/-- Below a bound, the edge coordinates of an infinite graph are read off its window. -/
theorem graphCoordEquiv_eq_windowCoord {n : ℕ} (G : SimpleGraph ℕ) {e : EdgeIndex}
    (he : e ∈ edgeWindow n) : graphCoordEquiv G e = windowCoord (G.restrictFin n) e := by
  obtain ⟨s, hs⟩ := e
  induction s using Sym2.ind with
  | _ x y =>
    have hx : x < n := mem_edgeWindow.1 he x (Sym2.mem_mk_left x y)
    have hy : y < n := mem_edgeWindow.1 he y (Sym2.mem_mk_right x y)
    rw [windowCoord, Bool.eq_iff_iff, SimpleGraph.graphCoordEquiv_apply,
      SimpleGraph.graphCoordEquiv_apply, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
    have h := SimpleGraph.map_adj_apply (f := Fin.valEmbedding) (G := G.restrictFin n)
      (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    rw [SimpleGraph.restrictFin_adj] at h
    exact h.symm

/-! ### Finite measures on infinite graphs are determined by their windows -/

/-- **A finite measure on the graphs on `ℕ` is determined by its windows.** The coordinates of an
infinite graph below any bound are a function of its window, so the laws of all finitely many
coordinates agree, and the law of the coordinates is their unique projective limit. -/
theorem measure_ext_of_map_restrictFin {μ ν : Measure (SimpleGraph ℕ)} [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (·.restrictFin n) = ν.map (·.restrictFin n)) : μ = ν := by
  -- The law of the coordinates in `J` is a pushforward of the window below `windowBound J`.
  have hcoord : ∀ J : Finset EdgeIndex, (fun G => J.restrict (graphCoordEquiv G)) =
      (fun H => J.restrict (windowCoord H)) ∘ (·.restrictFin (windowBound J)) := fun J => by
    funext G
    ext e
    exact graphCoordEquiv_eq_windowCoord G (subset_edgeWindow_windowBound J e.2)
  have hlaw : ∀ ρ : Measure (SimpleGraph ℕ), ∀ J : Finset EdgeIndex,
      (ρ.map graphCoordEquiv).map J.restrict =
        (ρ.map (·.restrictFin (windowBound J))).map fun H => J.restrict (windowCoord H) :=
    fun ρ J => by
      rw [Measure.map_map (Finset.measurable_restrict J) measurable_graphCoordEquiv,
        Measure.map_map (measurable_of_countable _) (SimpleGraph.measurable_restrictFin _)]
      exact congrArg ρ.map (hcoord J)
  have hcoordEq : μ.map graphCoordEquiv = ν.map graphCoordEquiv :=
    IsProjectiveLimit.unique (P := fun J => (μ.map graphCoordEquiv).map J.restrict)
      (fun _ => rfl) fun J => by beta_reduce; rw [hlaw, hlaw, h]
  have hsymm : ∀ ρ : Measure (SimpleGraph ℕ),
      (ρ.map graphCoordEquiv).map graphCoordEquiv.symm = ρ := fun ρ => by
    rw [Measure.map_map measurable_graphCoordEquiv_symm measurable_graphCoordEquiv,
      Equiv.symm_comp_self, Measure.map_id]
  rw [← hsymm μ, hcoordEq, hsymm]

end DenseGraphLimits

end TauCeti

namespace Equiv.Perm

open TauCeti.DenseGraphLimits

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

/-- Inverting a vertex relabelling inverts the induced edge-coordinate relabelling. -/
@[simp]
theorem edgeIndexMap_symm (e : Equiv.Perm ℕ) :
    (edgeIndexMap e).symm = edgeIndexMap e.symm := by
  apply Equiv.ext
  intro p
  rfl

/-- Relabelling an infinite graph is the same as relabelling its Boolean edge coordinates. -/
@[simp]
theorem graphCoordEquiv_comap (e : Equiv.Perm ℕ) (G : SimpleGraph ℕ) (p : EdgeIndex) :
    graphCoordEquiv (SimpleGraph.comap ⇑e G) p = graphCoordEquiv G (edgeIndexMap e p) := by
  -- `e` is a graph isomorphism from the pullback onto `G`, so it preserves edge-set membership.
  have h := (SimpleGraph.Iso.comap e G).map_mem_edgeSet_iff (e := p.1)
  -- The bundled graph isomorphism and the vertex permutation have distinct coercion paths.
  rw [show ⇑(SimpleGraph.Iso.comap e G) = ⇑e from funext (SimpleGraph.Iso.comap_apply e G)] at h
  apply Bool.eq_iff_iff.mpr
  simp only [SimpleGraph.graphCoordEquiv_apply, edgeIndexMap_val]
  exact h.symm

end Equiv.Perm
