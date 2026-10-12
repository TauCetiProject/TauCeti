/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Combinatorics.Quiver.UnderlyingGraph
public import TauCeti.RepresentationTheory.Quiver.Acyclic.Basic

/-!
# An orientation of a forest has no oriented cycle

A quiver none of whose arrows has a reverse, in particular one without loops, and whose underlying
graph `TauCeti.Quiver.underlyingGraph` is acyclic, has no oriented cycle
(`TauCeti.Quiver.isAcyclic_of_isAcyclic_underlyingGraph`). An oriented cycle would be a closed walk
in the underlying graph which never turns straight back, since turning back would need an arrow and
its reverse; in a forest such a walk is a path, and a closed path is trivial.

## Main results

* `TauCeti.Quiver.isAcyclic_of_isAcyclic_underlyingGraph`: an orientation of a forest is an
  acyclic quiver.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

variable {V : Type u} [_root_.Quiver.{v} V]

namespace Quiver

variable (hrev : ∀ a b : V, (a ⟶ b) → IsEmpty (b ⟶ a))
include hrev

/-- A path of a quiver none of whose arrows has a reverse, read as a walk in the underlying
graph. -/
private noncomputable def pathToWalk : ∀ {a b : V}, Path a b → (underlyingGraph V).Walk a b
  | _, _, .nil => .nil
  | _, c, .cons (b := b) p e =>
      (pathToWalk p).concat (underlyingGraph_adj_of_hom e fun h ↦ (hrev b c e).elim (h ▸ e))

private theorem length_pathToWalk {a b : V} (p : Path a b) :
    (pathToWalk hrev p).length = p.length := by
  induction p with
  | nil => simp [pathToWalk]
  | cons p e ih => simp [pathToWalk, ih]

/-- The walk underlying a path never turns straight back, and its last edge, if any, is the
underlying edge of an arrow into its endpoint. -/
private theorem isChain_edges_pathToWalk {a b : V} (p : Path a b) :
    List.IsChain (· ≠ ·) (pathToWalk hrev p).edges ∧
      ∀ x ∈ (pathToWalk hrev p).edges.getLast?, ∃ c : V, Nonempty (c ⟶ b) ∧ x = s(c, b) := by
  induction p with
  | nil => simp [pathToWalk]
  | @cons b c p e ih =>
    simp only [pathToWalk, SimpleGraph.Walk.edges_concat, List.concat_eq_append,
      List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def,
      Option.some.injEq]
    refine ⟨List.IsChain.append ih.1 (List.isChain_singleton _) fun x hx y hy ↦ ?_,
      fun x hx ↦ ⟨b, ⟨e⟩, hx.symm⟩⟩
    obtain ⟨d, ⟨f⟩, rfl⟩ := ih.2 x hx
    obtain rfl : s(b, c) = y := by simpa using hy
    intro hdc
    rcases Sym2.eq_iff.mp hdc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact (hrev d d f).elim f
    · exact (hrev b d e).elim f

/-- **An orientation of a forest has no oriented cycle.** If no arrow of a quiver has a reverse, so
that in particular there is no loop, and the underlying graph is acyclic, then every closed path
is trivial. -/
theorem isAcyclic_of_isAcyclic_underlyingGraph (hG : (underlyingGraph V).IsAcyclic) :
    IsAcyclic V := by
  refine isAcyclic_def.mpr fun a p ↦ ?_
  have hpath : (pathToWalk hrev p).IsPath :=
    (hG.isPath_iff_isChain _).mpr (isChain_edges_pathToWalk hrev p).1
  have hlen := length_pathToWalk hrev p
  rw [(SimpleGraph.Walk.isPath_iff_nil.mp hpath).length_eq_zero] at hlen
  exact Path.eq_nil_of_length_zero p hlen.symm

end Quiver

end TauCeti
