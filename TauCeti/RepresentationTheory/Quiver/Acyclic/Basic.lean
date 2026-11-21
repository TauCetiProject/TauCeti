/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Data.List.Nodup
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Combinatorics.Quiver.Prefunctor

/-!
# Acyclic quivers

This file defines an acyclic quiver to be one whose closed paths are all trivial. It develops
the elementary path API for excluding directed cycles, including the fact that paths cannot run
in both directions between distinct vertices.

This is the orientation-sensitive notion of acyclicity used for path algebras and quiver
representations. It is distinct from acyclicity of the underlying undirected graph.

## Main definitions

* `TauCeti.Quiver.IsAcyclic`: every closed path in the quiver is trivial.

## Main statements

* `TauCeti.Quiver.IsAcyclic.eq_of_paths`: vertices joined by paths in both directions are equal.
* `TauCeti.Quiver.IsAcyclic.vertices_nodup`: paths in an acyclic quiver visit no vertex twice.
* `Prefunctor.isAcyclic_of_codomain`: a quiver admitting a prefunctor to an acyclic quiver is
  acyclic.
-/

public section

namespace TauCeti

open Quiver

universe u v

variable {V : Type u} [Quiver.{v} V]

/-- A quiver is acyclic if every closed path is trivial. -/
def Quiver.IsAcyclic (V : Type u) [Quiver.{v} V] : Prop :=
  ∀ ⦃a : V⦄ (p : Path a a), p = Path.nil

/-- The defining closed-path condition for an acyclic quiver. -/
theorem Quiver.isAcyclic_def :
    Quiver.IsAcyclic V ↔ ∀ ⦃a : V⦄ (p : Path a a), p = Path.nil :=
  Iff.rfl

/-- A quiver is acyclic exactly when every closed path has length zero. -/
theorem Quiver.isAcyclic_iff_forall_length_eq_zero :
    Quiver.IsAcyclic V ↔ ∀ ⦃a : V⦄ (p : Path a a), p.length = 0 :=
  forall₂_congr fun _ p ↦ (Path.length_eq_zero_iff p).symm

/-- A quiver is acyclic exactly when it has no closed path of positive length. -/
theorem Quiver.isAcyclic_iff_forall_not_length_pos :
    Quiver.IsAcyclic V ↔ ∀ ⦃a : V⦄ (p : Path a a), ¬0 < p.length := by
  simp [Quiver.isAcyclic_iff_forall_length_eq_zero]

/-- A quiver is acyclic exactly when it has no nontrivial closed path. -/
theorem Quiver.isAcyclic_iff_not_exists_ne_nil :
    Quiver.IsAcyclic V ↔ ¬∃ (a : V) (p : Path a a), p ≠ Path.nil := by
  simp [Quiver.isAcyclic_def]

namespace Quiver.IsAcyclic

/-- Every closed path in an acyclic quiver is trivial. -/
theorem eq_nil (h : Quiver.IsAcyclic V) {a : V} (p : Path a a) : p = Path.nil :=
  h p

/-- In an acyclic quiver, every closed path has length zero. -/
@[simp]
theorem length_eq_zero (h : Quiver.IsAcyclic V) {a : V} (p : Path a a) :
    p.length = 0 :=
  Quiver.isAcyclic_iff_forall_length_eq_zero.mp h p

/-- An acyclic quiver has no closed path of positive length. -/
theorem not_length_pos (h : Quiver.IsAcyclic V) {a : V} (p : Path a a) :
    ¬0 < p.length :=
  Quiver.isAcyclic_iff_forall_not_length_pos.mp h p

/-- The composition of paths in opposite directions is trivial in an acyclic quiver. -/
@[simp]
theorem comp_eq_nil (h : Quiver.IsAcyclic V) {a b : V} (p : Path a b) (q : Path b a) :
    p.comp q = Path.nil :=
  h.eq_nil (p.comp q)

/-- If paths run in both directions in an acyclic quiver, the forward path has length zero. -/
theorem length_eq_zero_of_paths_left (h : Quiver.IsAcyclic V) {a b : V}
    (p : Path a b) (q : Path b a) :
    p.length = 0 :=
  Path.nil_of_comp_eq_nil_left (h.comp_eq_nil p q)

/-- If paths run in both directions in an acyclic quiver, the reverse path has length zero. -/
theorem length_eq_zero_of_paths_right (h : Quiver.IsAcyclic V) {a b : V}
    (p : Path a b) (q : Path b a) :
    q.length = 0 :=
  h.length_eq_zero_of_paths_left q p

/-- Vertices joined by paths in both directions in an acyclic quiver are equal. -/
theorem eq_of_paths (h : Quiver.IsAcyclic V) {a b : V} (p : Path a b) (q : Path b a) :
    a = b :=
  p.eq_of_length_zero (h.length_eq_zero_of_paths_left p q)

/-- The vertices encountered by a path in an acyclic quiver are pairwise distinct. -/
theorem vertices_nodup (h : Quiver.IsAcyclic V) {a b : V} (p : Path a b) :
    p.vertices.Nodup := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Path.vertices_cons, List.nodup_concat]
    refine ⟨fun he ↦ ?_, ih⟩
    obtain ⟨-, p₂, -⟩ := p.exists_eq_comp_of_mem_vertices he
    exact Path.cons_ne_nil p₂ e (h _)

/-- Between distinct vertices of an acyclic quiver, paths cannot exist in both directions. -/
theorem not_nonempty_path_and_nonempty_path (h : Quiver.IsAcyclic V) {a b : V} (hab : a ≠ b) :
    ¬(Nonempty (Path a b) ∧ Nonempty (Path b a)) := by
  rintro ⟨⟨p⟩, ⟨q⟩⟩
  exact hab (h.eq_of_paths p q)

/-- A path between distinct vertices of an acyclic quiver excludes every reverse path. -/
theorem isEmpty_path_of_path (h : Quiver.IsAcyclic V) {a b : V} (hab : a ≠ b) (p : Path a b) :
    IsEmpty (Path b a) :=
  ⟨fun q ↦ hab (h.eq_of_paths p q)⟩

/-- In an acyclic quiver, a path excludes every reverse arrow. -/
theorem isEmpty_hom_of_path (h : Quiver.IsAcyclic V) {a b : V} (p : Path a b) :
    IsEmpty (b ⟶ a) :=
  ⟨fun f ↦ Path.cons_ne_nil p f (h _)⟩

/-- An acyclic quiver has no loops. -/
theorem isEmpty_hom_self (h : Quiver.IsAcyclic V) (a : V) :
    IsEmpty (a ⟶ a) :=
  h.isEmpty_hom_of_path Path.nil

/-- Closed paths in an acyclic quiver form a subsingleton. -/
theorem subsingleton_path_self (h : Quiver.IsAcyclic V) (a : V) :
    Subsingleton (Path a a) :=
  ⟨fun p q ↦ (h.eq_nil p).trans (h.eq_nil q).symm⟩

/-- An acyclic quiver has exactly one closed path at each vertex, the trivial one. -/
theorem card_path_self (h : Quiver.IsAcyclic V) (a : V) : Nat.card (Path a a) = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨h.subsingleton_path_self a, ⟨Path.nil⟩⟩

/-- A quiver with no arrows is acyclic. -/
theorem of_isEmpty_hom [∀ a b : V, IsEmpty (a ⟶ b)] :
    Quiver.IsAcyclic V := by
  intro a p
  cases p with
  | nil => rfl
  | cons _ e => exact isEmptyElim e

end Quiver.IsAcyclic

/-- A quiver admitting a prefunctor to an acyclic quiver is acyclic. No injectivity is needed,
since a prefunctor preserves path lengths. -/
theorem _root_.Prefunctor.isAcyclic_of_codomain {W : Type*} [Quiver W] (F : V ⥤q W)
    (hW : Quiver.IsAcyclic W) : Quiver.IsAcyclic V :=
  Quiver.isAcyclic_iff_forall_length_eq_zero.mpr fun _ p ↦
    (F.length_mapPath p).symm.trans (hW.length_eq_zero _)

end TauCeti
