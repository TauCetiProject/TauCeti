/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Tree

/-!
# Convex sets of vertices

A set of vertices of a Serre graph is convex when it contains every vertex crossed by a reduced
path between two of its vertices. In a tree, the nonempty convex sets are the vertex sets of the
subtrees, since reduced paths are the geodesics. Convex sets are closed under arbitrary
intersections, and in an acyclic graph every singleton is convex.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §6.1.
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- A set of vertices is convex when every reduced path between two of its vertices only starts
darts at vertices of the set. -/
def IsConvex (S : Set Γ.V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ p : Γ.Path a b, Path.IsReduced Γ p → ∀ e ∈ Path.darts Γ p, Γ.src e ∈ S

variable {Γ}

/-- Unfold convexity. -/
theorem isConvex_iff {S : Set Γ.V} : Γ.IsConvex S ↔
    ∀ a ∈ S, ∀ b ∈ S, ∀ p : Γ.Path a b, Path.IsReduced Γ p →
      ∀ e ∈ Path.darts Γ p, Γ.src e ∈ S := Iff.rfl

/-- A reduced path between vertices of a convex set also ends its darts in the set. -/
theorem IsConvex.tgt_mem {S : Set Γ.V} (hS : Γ.IsConvex S) {a b : Γ.V} (ha : a ∈ S)
    (hb : b ∈ S) {p : Γ.Path a b} (hp : Path.IsReduced Γ p) {e : Γ.E}
    (he : e ∈ Path.darts Γ p) : Γ.tgt e ∈ S := by
  have hp' : Path.IsReduced Γ p.reverse := (Path.isReduced_reverse Γ p).mpr hp
  have he' : Γ.rev e ∈ Path.darts Γ p.reverse := by
    simpa only [Path.darts_reverse, List.mem_map, List.mem_reverse] using ⟨e, he, rfl⟩
  simpa only [src_rev] using hS b hb a ha p.reverse hp' (Γ.rev e) he'

theorem isConvex_univ : Γ.IsConvex Set.univ := fun _ _ _ _ _ _ _ _ => Set.mem_univ _

theorem isConvex_empty : Γ.IsConvex ∅ := fun _ ha => ha.elim

/-- Intersections of convex sets are convex. -/
theorem isConvex_sInter {𝒮 : Set (Set Γ.V)} (h : ∀ S ∈ 𝒮, Γ.IsConvex S) :
    Γ.IsConvex (⋂₀ 𝒮) := fun a ha b hb p hp e he =>
  Set.mem_sInter.mpr fun S hS => h S hS a (ha S hS) b (hb S hS) p hp e he

/-- Intersections of indexed families of convex sets are convex. -/
theorem isConvex_iInter {ι : Sort*} {S : ι → Set Γ.V} (h : ∀ i, Γ.IsConvex (S i)) :
    Γ.IsConvex (⋂ i, S i) :=
  isConvex_sInter (Set.forall_mem_range.mpr h)

theorem IsConvex.inter {S T : Set Γ.V} (hS : Γ.IsConvex S) (hT : Γ.IsConvex T) :
    Γ.IsConvex (S ∩ T) := fun a ha b hb p hp e he =>
  ⟨hS a ha.1 b hb.1 p hp e he, hT a ha.2 b hb.2 p hp e he⟩

/-- In an acyclic graph every singleton is convex. -/
theorem IsAcyclic.isConvex_singleton (h : Γ.IsAcyclic) (v : Γ.V) : Γ.IsConvex {v} := by
  rintro a rfl b rfl p hp e he
  rw [(isAcyclic_iff Γ).mp h b p hp, Path.darts_nil] at he
  exact absurd he List.not_mem_nil

end SerreGraph
end TauCeti
