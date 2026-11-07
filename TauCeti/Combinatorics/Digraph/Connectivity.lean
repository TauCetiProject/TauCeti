/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Digraph.Menger
public import TauCeti.Combinatorics.Network.Connectivity.Basic

/-!
# Directed connectivity of digraphs

This file specializes arc connectivity and vertex-strong connectivity from explicit arrow
families to `Digraph`.  A digraph arrow retains its endpoints and its adjacency proof;
`Digraph.deleteArrows` deletes precisely the selected arrows.  Local and global arc connectivity
can then be read as reachability after deleting fewer than the threshold number of arrows.

Vertex deletion is expressed by the induced digraph on the complement.  This gives a native
characterization of vertex-strong connectivity and its Menger path characterization.  The paths
retain the adjacency-arrow representation, so their vertex lists are chains for the original
digraph and distinct ordered pairs cannot be counted as parallel arrows.

The connectivity notions follow J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and
Applications*, 2nd ed., Springer, 2009, Sections 5.1 and 5.4.
-/

public section

open Finset Relation Set TauCeti

universe u

namespace Digraph

variable {V : Type u} (D : Digraph V)

/-! ### Arrow deletion -/

/-- Delete a set of arrows from a digraph.  Each arrow retains its ordered endpoints and the
adjacency proof witnessing that it belongs to `D`. -/
def deleteArrows (F : Set (Σ v w, D.AdjHom v w)) : Digraph V :=
  D \ { Adj := fun v w ↦ ∃ e : D.AdjHom v w, ⟨v, w, e⟩ ∈ F }

/-- An ordered pair is an arrow after deletion exactly when it was an arrow and was not selected.
-/
@[simp]
theorem deleteArrows_adj {F : Set (Σ v w, D.AdjHom v w)} {v w : V} :
    (D.deleteArrows F).Adj v w ↔ ∃ e : D.AdjHom v w, ⟨v, w, e⟩ ∉ F := by
  simp only [deleteArrows, sdiff_adj]
  constructor
  · rintro ⟨h, hF⟩
    exact ⟨⟨h⟩, fun he ↦ hF ⟨⟨h⟩, he⟩⟩
  · rintro ⟨e, hF⟩
    refine ⟨e.down, ?_⟩
    rintro ⟨e', he'⟩
    apply hF
    simpa only [Subsingleton.elim e' e] using he'

/-- Deleting no arrows leaves a digraph unchanged. -/
@[simp]
theorem deleteArrows_empty : D.deleteArrows ∅ = D := by
  ext v w
  simp

/-- Deleting every arrow leaves the empty digraph. -/
@[simp]
theorem deleteArrows_univ : D.deleteArrows Set.univ = ⊥ := by
  ext v w
  simp

/-- Deleting a larger set of arrows gives a smaller digraph. -/
theorem deleteArrows_anti {F F' : Set (Σ v w, D.AdjHom v w)} (hFF' : F ⊆ F') :
    D.deleteArrows F' ≤ D.deleteArrows F := by
  intro v w h
  rw [deleteArrows_adj] at h ⊢
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun hf ↦ he (hFF' hf)⟩

/-! ### Arc connectivity -/

variable {D} {k : ℕ} {s t : V}

/-- A vertex is `k`-arc-reachable in a digraph exactly when it remains reachable after deleting
any set of fewer than `k` adjacent ordered pairs. -/
theorem isArcReachable_iff : IsArcReachable D.AdjHom k s t ↔
    ∀ F : Finset (Σ v w, D.AdjHom v w), #F < k →
      ReflTransGen (D.deleteArrows (F : Set _)).Adj s t := by
  rw [isArcReachable_def]
  refine forall_congr' fun F ↦ imp_congr_right fun _ ↦ ?_
  rw [deleteArrows, reflTransGen_sdiff_iff]
  have hset : (F : Set (Σ v w, D.AdjHom v w)) =
      {a | ∃ e : D.AdjHom a.1 a.2.1,
        (⟨a.1, a.2.1, e⟩ : Σ v w, D.AdjHom v w) ∈ (F : Set _)} := by
    ext ⟨v, w, e⟩
    constructor
    · exact fun he ↦ ⟨e, he⟩
    · rintro ⟨e', he'⟩
      simpa only [Subsingleton.elim e' e] using he'
  -- Expose the deleted-arrow predicate used by `reflTransGen_sdiff_iff` so `hset` applies.
  change ReachableWithout (Q := D.AdjHom) (F : Set (Σ v w, D.AdjHom v w)) s t ↔
    ReachableWithout (Q := D.AdjHom) {a : Σ v w, D.AdjHom v w |
      ∃ e : D.AdjHom a.1 a.2.1,
        (⟨a.1, a.2.1, e⟩ : Σ v w, D.AdjHom v w) ∈ (F : Set _)} s t
  rw [← hset]

/-- A digraph is `k`-arc-strong exactly when every ordered pair remains reachable after deleting
any set of fewer than `k` arrows. -/
theorem isArcStrong_iff : IsArcStrong D.AdjHom k ↔
    ∀ F : Finset (Σ v w, D.AdjHom v w), #F < k →
      ∀ s t, ReflTransGen (D.deleteArrows (F : Set _)).Adj s t := by
  rw [isArcStrong_def]
  constructor
  · intro h F hF s t
    exact isArcReachable_iff.mp (h s t) F hF
  · intro h s t
    exact isArcReachable_iff.mpr fun F hF ↦ h F hF s t

/-- A digraph is `1`-arc-strong exactly when every vertex is reachable from every other vertex
along its adjacency relation. -/
theorem isArcStrong_one_iff : IsArcStrong D.AdjHom 1 ↔
    ∀ v w, ReflTransGen D.Adj v w := by
  rw [TauCeti.isArcStrong_one, Digraph.isStronglyConnected_iff]

/-! ### Vertex-strong connectivity -/

/-- A digraph is `k`-vertex-strong exactly when it has more than `k` vertices and deleting any
fewer than `k` vertices leaves the induced digraph strongly connected. -/
theorem isVertexStrong_iff : IsVertexStrong D.AdjHom k ↔
    (k : ℕ∞) < ENat.card V ∧ ∀ (X : Finset V), #X < k →
      ∀ s t : ↑((X : Set V)ᶜ), ReflTransGen (D.induce (X : Set V)ᶜ).Adj s t := by
  rw [TauCeti.isVertexStrong_def]
  refine and_congr_right fun _ ↦ ⟨fun h X hX s t ↦ ?_, fun h X hX s hs t ht ↦ ?_⟩
  · exact reflTransGen_induce_compl_iff.mpr (h X hX s.2 t.2)
  · let s' : ↑((X : Set V)ᶜ) := ⟨s, by simpa⟩
    let t' : ↑((X : Set V)ᶜ) := ⟨t, by simpa⟩
    exact reflTransGen_induce_compl_iff.mp (h X hX s' t')

/-- A digraph is `1`-vertex-strong exactly when it has two distinct vertices and every vertex is
reachable from every other vertex along adjacency. -/
theorem isVertexStrong_one_iff : IsVertexStrong D.AdjHom 1 ↔
    Nontrivial V ∧ ∀ v w, ReflTransGen D.Adj v w := by
  rw [TauCeti.isVertexStrong_one, Digraph.isStronglyConnected_iff]

/-- On a finite vertex type, vertex-strong connectivity of a digraph is equivalent to the
existence of the threshold number of internally vertex-disjoint directed paths between every two
distinct vertices. -/
theorem isVertexStrong_iff_exists_paths [Finite V] : IsVertexStrong D.AdjHom k ↔
    (k : ℕ∞) < ENat.card V ∧ ∀ {s t : V}, s ≠ t →
      ∃ P : Fin k → ArrowWalk D.AdjHom s t, Function.Injective P ∧
        (∀ i, (P i).IsPath) ∧ Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) :=
  TauCeti.isVertexStrong_iff_exists_paths

/-! ### Degree bounds -/

/-- The arrows leaving a vertex of a digraph are equivalent to its adjacent targets. -/
def outArrowEquiv (D : Digraph V) (v : V) :
    (Σ w, D.AdjHom v w) ≃ {w : V // D.Adj v w} where
  toFun a := ⟨a.1, a.2.down⟩
  invFun w := ⟨w.1, ⟨w.2⟩⟩
  left_inv _ := (rfl)
  right_inv _ := (rfl)

/-- The arrows entering a vertex of a digraph are equivalent to its adjacent sources. -/
def inArrowEquiv (D : Digraph V) (v : V) :
    (Σ w, D.AdjHom w v) ≃ {w : V // D.Adj w v} where
  toFun a := ⟨a.1, a.2.down⟩
  invFun w := ⟨w.1, ⟨w.2⟩⟩
  left_inv _ := (rfl)
  right_inv _ := (rfl)

/-- On at least two vertices, the arc connectivity of a finite digraph is at most the number of
targets adjacent from any specified vertex. -/
theorem arcConnectivity_le_card_out [Fintype V] [Nontrivial V] [DecidableRel D.Adj] (v : V) :
    arcConnectivity D.AdjHom ≤ #{w | D.Adj v w} := by
  classical
  rw [← Fintype.card_subtype (fun w ↦ D.Adj v w),
    ← Fintype.card_congr (D.outArrowEquiv v)]
  exact TauCeti.arcConnectivity_le_card_out v

/-- On at least two vertices, the arc connectivity of a finite digraph is at most the number of
sources adjacent to any specified vertex. -/
theorem arcConnectivity_le_card_in [Fintype V] [Nontrivial V] [DecidableRel D.Adj] (v : V) :
    arcConnectivity D.AdjHom ≤ #{w | D.Adj w v} := by
  classical
  rw [← Fintype.card_subtype (fun w ↦ D.Adj w v),
    ← Fintype.card_congr (D.inArrowEquiv v)]
  exact TauCeti.arcConnectivity_le_card_in v

end Digraph
