/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Walk

/-!
# Trimming directed paths between terminal sets

A directed path whose source lies in `A` and whose target lies in `B` contains a contiguous
subpath from its last vertex in `A` to its first subsequent vertex in `B`, whose internal vertices
avoid both terminal sets. This file packages that extraction as the operation
`TauCeti.ArrowWalk.trimToSets`. The trimmed path visits only vertices and traverses only arrows of
the original path, so trimming preserves vertex-disjoint and arrow-disjoint families.

The operation permits a path of length zero when the terminal sets overlap. This is the convention
needed when auxiliary source and sink constructions reduce set-to-set path problems to problems
with two distinguished terminals.

## Main definitions

* `TauCeti.ArrowWalk.trimToSets`: trim a directed path to a path between two terminal sets.
* `TauCeti.ArrowWalk.trimToSetsSource` and `TauCeti.ArrowWalk.trimToSetsTarget`: the endpoints of
  the trimmed path.

## Main results

* `TauCeti.ArrowWalk.trimToSets_isPath`: the trimmed walk is a path.
* `TauCeti.ArrowWalk.trimToSets_vertices_subset` and
  `TauCeti.ArrowWalk.trimToSets_arrows_subset`: trimming introduces no vertices or arrows.
* `TauCeti.ArrowWalk.exists_eq_comp_trimToSets_comp`: the trimmed path is a contiguous subpath and
  its source is the last vertex in `A` on the original path.
* `TauCeti.ArrowWalk.trimToSets_interior_notMem`: internal vertices of the trimmed path lie in
  neither terminal set.
* `TauCeti.ArrowWalk.trimToSets_source_eq_target_of_source_mem_right`: trimming stops immediately
  when its chosen source already belongs to both terminal sets.
* `TauCeti.ArrowWalk.pairwise_trimToSets_vertices_disjoint` and
  `TauCeti.ArrowWalk.pairwise_trimToSets_arrows_disjoint`: trimming preserves disjoint families.

## References

* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Chapter 9.
-/

public section

namespace TauCeti

namespace ArrowWalk

universe u v

variable {V : Type u} {Q : V → V → Type v}

private noncomputable def trimToSetsData {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) :
    {x : Σ a, Σ b, ArrowWalk Q a b //
      x.1 ∈ A ∧ x.2.1 ∈ B ∧ x.2.2.IsPath ∧ x.2.2.vertices ⊆ p.vertices ∧
        x.2.2.arrows ⊆ p.arrows ∧
          (∃ (before : ArrowWalk Q s x.1) (after : ArrowWalk Q x.2.1 t),
            p = before.comp (x.2.2.comp after) ∧
              ∀ z ∈ (x.2.2.comp after).vertices, z ≠ x.1 → z ∉ A) ∧
          (∀ z ∈ x.2.2.vertices, z ≠ x.1 → z ∉ A) ∧
            ∀ z ∈ x.2.2.vertices, z ≠ x.2.1 → z ∉ B} :=
  Classical.choice <| by
    obtain ⟨a, ha, b, hb, q, hq, hfactor, hverts, harrows, hqA, hqB⟩ :=
      hp.exists_infix_interior_notMem hs ht
    exact ⟨⟨⟨a, b, q⟩, ha, hb, hq, hverts, harrows, hfactor, hqA, hqB⟩⟩

/-- The source of the path obtained by trimming `p` between the terminal sets `A` and `B`. -/
noncomputable def trimToSetsSource {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) : V :=
  (trimToSetsData p hp hs ht).1.1

/-- The target of the path obtained by trimming `p` between the terminal sets `A` and `B`. -/
noncomputable def trimToSetsTarget {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) : V :=
  (trimToSetsData p hp hs ht).1.2.1

/-- Trim a directed path from a vertex of `A` to a vertex of `B` to a path whose internal
vertices lie in neither terminal set. The result visits only vertices and traverses only arrows of
the original path. -/
noncomputable def trimToSets {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) :
    ArrowWalk Q (p.trimToSetsSource hp hs ht) (p.trimToSetsTarget hp hs ht) :=
  (trimToSetsData p hp hs ht).1.2.2

/-- The source of a path trimmed between `A` and `B` belongs to `A`. -/
@[simp]
theorem trimToSetsSource_mem {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) : p.trimToSetsSource hp hs ht ∈ A :=
  (trimToSetsData p hp hs ht).2.1

/-- The target of a path trimmed between `A` and `B` belongs to `B`. -/
@[simp]
theorem trimToSetsTarget_mem {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) : p.trimToSetsTarget hp hs ht ∈ B :=
  (trimToSetsData p hp hs ht).2.2.1

/-- Trimming a path between terminal sets produces a path. -/
theorem trimToSets_isPath {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) : (p.trimToSets hp hs ht).IsPath :=
  (trimToSetsData p hp hs ht).2.2.2.1

/-- A trimmed path visits only vertices of the original walk. -/
theorem trimToSets_vertices_subset {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) :
    (p.trimToSets hp hs ht).vertices ⊆ p.vertices :=
  (trimToSetsData p hp hs ht).2.2.2.2.1

/-- A trimmed path traverses only arrows of the original walk. -/
theorem trimToSets_arrows_subset {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) :
    (p.trimToSets hp hs ht).arrows ⊆ p.arrows :=
  (trimToSetsData p hp hs ht).2.2.2.2.2.1

/-- A trimmed path is a contiguous subpath of the original path, beginning at its last vertex in
`A`. -/
theorem exists_eq_comp_trimToSets_comp {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) :
    ∃ (before : ArrowWalk Q s (p.trimToSetsSource hp hs ht))
      (after : ArrowWalk Q (p.trimToSetsTarget hp hs ht) t),
      p = before.comp ((p.trimToSets hp hs ht).comp after) ∧
        ∀ z ∈ ((p.trimToSets hp hs ht).comp after).vertices,
          z ≠ p.trimToSetsSource hp hs ht → z ∉ A :=
  (trimToSetsData p hp hs ht).2.2.2.2.2.2.1

/-- Apart from its source, a path trimmed between `A` and `B` contains no vertex of `A`. -/
theorem trimToSets_notMem_left_of_ne_source {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) {z : V}
    (hz : z ∈ (p.trimToSets hp hs ht).vertices)
    (hza : z ≠ p.trimToSetsSource hp hs ht) : z ∉ A :=
  (trimToSetsData p hp hs ht).2.2.2.2.2.2.2.1 z hz hza

/-- Apart from its target, a path trimmed between `A` and `B` contains no vertex of `B`. -/
theorem trimToSets_notMem_right_of_ne_target {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) {z : V}
    (hz : z ∈ (p.trimToSets hp hs ht).vertices)
    (hzb : z ≠ p.trimToSetsTarget hp hs ht) : z ∉ B :=
  (trimToSetsData p hp hs ht).2.2.2.2.2.2.2.2 z hz hzb

/-- If the source chosen by trimming also belongs to the right terminal set, then it is already
the target. Thus overlapping terminal sets give the permitted zero-length terminal path. -/
theorem trimToSets_source_eq_target_of_source_mem_right {A B : Set V} {s t : V}
    (p : ArrowWalk Q s t) (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B)
    (h : p.trimToSetsSource hp hs ht ∈ B) :
    p.trimToSetsSource hp hs ht = p.trimToSetsTarget hp hs ht := by
  by_contra hne
  exact p.trimToSets_notMem_right_of_ne_target hp hs ht
    (@Quiver.Path.start_mem_vertices V ⟨Q⟩ _ _ (p.trimToSets hp hs ht)) hne h

/-- If the target chosen by trimming also belongs to the left terminal set, then it is already
the source. -/
theorem trimToSets_source_eq_target_of_target_mem_left {A B : Set V} {s t : V}
    (p : ArrowWalk Q s t) (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B)
    (h : p.trimToSetsTarget hp hs ht ∈ A) :
    p.trimToSetsSource hp hs ht = p.trimToSetsTarget hp hs ht := by
  by_contra hne
  exact p.trimToSets_notMem_left_of_ne_source hp hs ht
    (@Quiver.Path.end_mem_vertices V ⟨Q⟩ _ _ (p.trimToSets hp hs ht)) (Ne.symm hne) h

/-- Every non-endpoint vertex of a path trimmed between `A` and `B` lies in neither terminal
set. -/
theorem trimToSets_interior_notMem {A B : Set V} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.IsPath) (hs : s ∈ A) (ht : t ∈ B) {z : V}
    (hz : z ∈ (p.trimToSets hp hs ht).vertices)
    (hza : z ≠ p.trimToSetsSource hp hs ht) (hzb : z ≠ p.trimToSetsTarget hp hs ht) :
    z ∉ A ∧ z ∉ B :=
  ⟨p.trimToSets_notMem_left_of_ne_source hp hs ht hz hza,
    p.trimToSets_notMem_right_of_ne_target hp hs ht hz hzb⟩

/-- Trimming two vertex-disjoint walks preserves their vertex-disjointness. -/
theorem trimToSets_vertices_disjoint {A B : Set V} {s₁ t₁ s₂ t₂ : V}
    (p : ArrowWalk Q s₁ t₁) (q : ArrowWalk Q s₂ t₂) (hp : p.IsPath) (hq : q.IsPath)
    (hs₁ : s₁ ∈ A) (ht₁ : t₁ ∈ B) (hs₂ : s₂ ∈ A) (ht₂ : t₂ ∈ B)
    (h : p.vertices.Disjoint q.vertices) :
    (p.trimToSets hp hs₁ ht₁).vertices.Disjoint (q.trimToSets hq hs₂ ht₂).vertices :=
  fun _ hz₁ hz₂ ↦ h (p.trimToSets_vertices_subset hp hs₁ ht₁ hz₁)
    (q.trimToSets_vertices_subset hq hs₂ ht₂ hz₂)

/-- Trimming two arrow-disjoint walks preserves their arrow-disjointness. -/
theorem trimToSets_arrows_disjoint {A B : Set V} {s₁ t₁ s₂ t₂ : V}
    (p : ArrowWalk Q s₁ t₁) (q : ArrowWalk Q s₂ t₂) (hp : p.IsPath) (hq : q.IsPath)
    (hs₁ : s₁ ∈ A) (ht₁ : t₁ ∈ B) (hs₂ : s₂ ∈ A) (ht₂ : t₂ ∈ B)
    (h : p.arrows.Disjoint q.arrows) :
    (p.trimToSets hp hs₁ ht₁).arrows.Disjoint (q.trimToSets hq hs₂ ht₂).arrows :=
  fun _ ha₁ ha₂ ↦ h (p.trimToSets_arrows_subset hp hs₁ ht₁ ha₁)
    (q.trimToSets_arrows_subset hq hs₂ ht₂ ha₂)

/-- Trimming a pairwise vertex-disjoint family of walks preserves pairwise vertex-disjointness. -/
theorem pairwise_trimToSets_vertices_disjoint {A B : Set V} {I : Type*} {s t : I → V}
    (p : ∀ i, ArrowWalk Q (s i) (t i)) (hp : ∀ i, (p i).IsPath)
    (hs : ∀ i, s i ∈ A) (ht : ∀ i, t i ∈ B)
    (h : Pairwise fun i j ↦ (p i).vertices.Disjoint (p j).vertices) :
    Pairwise fun i j ↦ ((p i).trimToSets (hp i) (hs i) (ht i)).vertices.Disjoint
      ((p j).trimToSets (hp j) (hs j) (ht j)).vertices :=
  fun i j hij ↦ trimToSets_vertices_disjoint (p i) (p j) (hp i) (hp j) (hs i) (ht i)
    (hs j) (ht j) (h hij)

/-- Trimming a pairwise arrow-disjoint family of walks preserves pairwise arrow-disjointness. -/
theorem pairwise_trimToSets_arrows_disjoint {A B : Set V} {I : Type*} {s t : I → V}
    (p : ∀ i, ArrowWalk Q (s i) (t i)) (hp : ∀ i, (p i).IsPath)
    (hs : ∀ i, s i ∈ A) (ht : ∀ i, t i ∈ B)
    (h : Pairwise fun i j ↦ (p i).arrows.Disjoint (p j).arrows) :
    Pairwise fun i j ↦ ((p i).trimToSets (hp i) (hs i) (ht i)).arrows.Disjoint
      ((p j).trimToSets (hp j) (hs j) (ht j)).arrows :=
  fun i j hij ↦ trimToSets_arrows_disjoint (p i) (p j) (hp i) (hp j) (hs i) (ht i)
    (hs j) (ht j) (h hij)

end ArrowWalk

end TauCeti
