/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Digraph.ArrowWalk
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

/-! ### Arc connectivity -/

variable {D} {k : ℕ} {s t : V}

/-- A vertex is `k`-arc-reachable in a digraph exactly when it remains reachable after deleting
any set of fewer than `k` adjacent ordered pairs. -/
theorem isArcReachable_iff : IsArcReachable D.AdjHom k s t ↔
    ∀ F : Finset (Σ v w, D.AdjHom v w), #F < k →
      ReflTransGen (D.deleteArrows (F : Set _)).Adj s t := by
  rw [isArcReachable_def]
  refine forall_congr' fun F ↦ imp_congr_right fun _ ↦ ?_
  have hdelete : D.deleteArrows (F : Set (Σ v w, D.AdjHom v w)) =
      D \ { Adj := fun v w ↦ ∃ e : D.AdjHom v w,
        (⟨v, w, e⟩ : Σ v w, D.AdjHom v w) ∈ (F : Set _) } := by
    ext v w
    simp only [deleteArrows_adj, sdiff_adj]
    constructor
    · rintro ⟨e, he⟩
      exact ⟨e.down, fun ⟨e', he'⟩ ↦ he (by simpa only [Subsingleton.elim e' e] using he')⟩
    · rintro ⟨h, hF⟩
      exact ⟨⟨h⟩, fun he ↦ hF ⟨⟨h⟩, he⟩⟩
  rw [hdelete, reflTransGen_sdiff_iff]
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

/-! ### Degree bounds -/

/-- On at least two vertices, the arc connectivity of a finite digraph is at most the number of
targets adjacent from any specified vertex. -/
theorem arcConnectivity_le_card_out [Fintype V] [Nontrivial V] [DecidableRel D.Adj] (v : V) :
    arcConnectivity D.AdjHom ≤ #{w | D.Adj v w} := by
  classical
  rw [← Fintype.card_subtype (fun w ↦ D.Adj v w),
    ← Fintype.card_congr (Equiv.sigmaPLiftEquivSubtype fun w ↦ D.Adj v w)]
  exact TauCeti.arcConnectivity_le_card_out v

/-- On at least two vertices, the arc connectivity of a finite digraph is at most the number of
sources adjacent to any specified vertex. -/
theorem arcConnectivity_le_card_in [Fintype V] [Nontrivial V] [DecidableRel D.Adj] (v : V) :
    arcConnectivity D.AdjHom ≤ #{w | D.Adj w v} := by
  classical
  rw [← Fintype.card_subtype (fun w ↦ D.Adj w v),
    ← Fintype.card_congr (Equiv.sigmaPLiftEquivSubtype fun w ↦ D.Adj w v)]
  exact TauCeti.arcConnectivity_le_card_in v

end Digraph
