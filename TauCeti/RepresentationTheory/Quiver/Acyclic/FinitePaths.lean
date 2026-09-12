/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.BoundedPaths
public import TauCeti.Combinatorics.Quiver.LoopPower
public import TauCeti.RepresentationTheory.Quiver.Acyclic.Basic

/-!
# Finite paths in acyclic quivers

This file proves that a finite quiver with finitely many arrows between any two vertices has only
finitely many paths **exactly when** it is acyclic. The forward half supplies the finiteness
hypothesis needed for the finite-dimensionality of its path algebra. The bound that makes the
count finite is the acyclic one: every path has length below the number of vertices, so the count
reduces to the bounded-length count of `TauCeti.Combinatorics.Quiver.BoundedPaths`.

The converse needs no finiteness of the quiver at all: an oriented cycle has infinitely many
powers (`TauCeti.Quiver.eq_nil_of_finite_path_self`), so a quiver with finitely many paths has
none.

## Main results

* `TauCeti.finite_paths_of_isAcyclic`: a finite acyclic quiver with finite arrow types has
  finitely many paths.
* `TauCeti.isAcyclic_of_finite_paths`: **a quiver with finitely many paths is acyclic.**
* `TauCeti.isAcyclic_iff_finite_paths`: the two together, the extensional form of acyclicity that
  the finite-dimensionality of the path algebra is read off.

## References

This file implements the `finite_paths_of_isAcyclic` part of Layer 0, “Acyclicity, as a
predicate”, in `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose
statement is that for a finite quiver acyclicity *is* finiteness of the path space.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

variable {V : Type u} [Quiver.{v} V]

noncomputable section

namespace Quiver.IsAcyclic

/-- Every path in an acyclic finite quiver has length strictly below the number of vertices. -/
theorem length_lt_card (h : Quiver.IsAcyclic V) [Fintype V] {a b : V} (p : _root_.Quiver.Path a b) :
    p.length < Fintype.card V := by
  -- The bound is unfolded by hand rather than by `simpa`: `Quiver.IsAcyclic.card_path_self` puts
  -- `Nat.card` in scope for this file, and simp then exceeds `maxRecDepth` on this goal.
  have hle := List.Nodup.length_le_card (h.vertices_nodup p)
  rw [_root_.Quiver.Path.vertices_length] at hle
  omega

private theorem finite_paths [Finite V] [∀ a b : V, Finite (a ⟶ b)] (h : Quiver.IsAcyclic V) :
    Finite (Σ a b : V, _root_.Quiver.Path a b) := by
  let : Fintype V := Fintype.ofFinite V
  let pathFinite (a b : V) : Finite (_root_.Quiver.Path.BoundedPaths a b (Fintype.card V - 1)) :=
    _root_.TauCeti.Quiver.finite_boundedPaths _ _ _
  let pathFintype (a b : V) : Fintype (_root_.Quiver.Path.BoundedPaths a b (Fintype.card V - 1)) :=
    Fintype.ofFinite _
  let f : (Σ a b : V, _root_.Quiver.Path.BoundedPaths a b (Fintype.card V - 1)) →
      Σ a b : V, _root_.Quiver.Path a b :=
    fun p ↦ ⟨p.1, p.2.1, p.2.2.1⟩
  let : Finite (Σ a b : V, _root_.Quiver.Path.BoundedPaths a b (Fintype.card V - 1)) :=
    Finite.of_fintype _
  apply Finite.of_surjective f
  rintro ⟨a, b, p⟩
  refine ⟨⟨a, b, p, ?_⟩, rfl⟩
  have hp := h.length_lt_card p
  omega

end Quiver.IsAcyclic

/-- A finite acyclic quiver with finite arrow types has finitely many paths. -/
theorem finite_paths_of_isAcyclic [Finite V] [∀ a b : V, Finite (a ⟶ b)]
    (h : Quiver.IsAcyclic V) : Finite (Σ a b : V, _root_.Quiver.Path a b) :=
  h.finite_paths

/-- **A quiver with finitely many paths is acyclic**: the powers of an oriented cycle are already
infinitely many paths. No finiteness of the vertices or of the arrows is needed. -/
theorem isAcyclic_of_finite_paths (h : Finite (Σ a b : V, _root_.Quiver.Path a b)) :
    Quiver.IsAcyclic V := by
  have := h
  refine Quiver.isAcyclic_def.mpr fun a p => ?_
  have : Finite (_root_.Quiver.Path a a) :=
    Finite.of_injective
      (fun q : _root_.Quiver.Path a a => (⟨a, a, q⟩ : Σ a b : V, _root_.Quiver.Path a b))
      fun _ _ hxy => by simpa using hxy
  exact Quiver.eq_nil_of_finite_path_self p

/-- **For a finite quiver with finite arrow types, acyclicity is finiteness of the path space.**
This is the extensional form of acyclicity, the hypothesis under which the path algebra is a
finite module. -/
theorem isAcyclic_iff_finite_paths [Finite V] [∀ a b : V, Finite (a ⟶ b)] :
    Quiver.IsAcyclic V ↔ Finite (Σ a b : V, _root_.Quiver.Path a b) :=
  ⟨finite_paths_of_isAcyclic, isAcyclic_of_finite_paths⟩

end

end TauCeti
