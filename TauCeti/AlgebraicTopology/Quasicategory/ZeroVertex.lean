/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import TauCeti.AlgebraicTopology.Quasicategory.InitialVertex

/-!
# Zero vertices and pointed quasicategories

A vertex of a simplicial set is a *zero vertex* (`SSet.IsZeroVertex`) if it is both an initial
and a terminal vertex; in a quasicategory these are the zero objects. A quasicategory with a zero
vertex (`SSet.HasZeroVertex`) is *pointed* in the sense of Lurie. Pointedness is the first
condition in the definition of a stable quasicategory, whose fibres and cofibres are pullbacks and
pushouts along a zero object. The name `HasZeroVertex`, after `HasZeroObject`, avoids the other
meaning of a pointed simplicial set, one with a chosen basepoint.

In the nerve of a category the zero vertices are the zero objects
(`CategoryTheory.nerve.isZeroVertex_iff`), so the nerve has a zero vertex exactly when the
category has a zero object (`CategoryTheory.nerve.hasZeroVertex_iff`). Every vertex of a terminal
simplicial set, such as `Δ[0]`, is a zero vertex (`SSet.isZeroVertex_of_isTerminal`), while `Δ[1]`
has none (`SSet.stdSimplex.not_hasZeroVertex_one`): its initial and terminal vertices differ.

## References

* J. Lurie, *Higher Algebra*, Definition 1.1.1.1.
* J. Lurie, *Higher Topos Theory*, §1.2.12.
-/

public section

universe v u

open CategoryTheory Limits Simplicial

namespace SSet

variable {X Y : SSet.{u}}

/-- A vertex of a simplicial set is a *zero vertex* if it is both an initial and a terminal
vertex. In a quasicategory these are the zero objects. -/
def IsZeroVertex (x : X _⦋0⦌) : Prop :=
  X.IsInitialVertex x ∧ X.IsTerminalVertex x

lemma isZeroVertex_iff (x : X _⦋0⦌) :
    X.IsZeroVertex x ↔ X.IsInitialVertex x ∧ X.IsTerminalVertex x :=
  Iff.rfl

namespace IsZeroVertex

variable {x : X _⦋0⦌}

lemma isInitialVertex (hx : X.IsZeroVertex x) : X.IsInitialVertex x :=
  hx.1

lemma isTerminalVertex (hx : X.IsZeroVertex x) : X.IsTerminalVertex x :=
  hx.2

/-- Zero vertices are preserved by isomorphisms of simplicial sets. -/
lemma map_iso (hx : X.IsZeroVertex x) (e : X ≅ Y) : Y.IsZeroVertex (e.hom.app _ x) :=
  ⟨hx.1.map_iso e, hx.2.map_iso e⟩

end IsZeroVertex

/-- Zero vertices correspond under isomorphisms of simplicial sets. -/
lemma isZeroVertex_iff_of_iso (e : X ≅ Y) (x : X _⦋0⦌) :
    Y.IsZeroVertex (e.hom.app _ x) ↔ X.IsZeroVertex x := by
  rw [isZeroVertex_iff, isZeroVertex_iff, isInitialVertex_iff_of_iso, isTerminalVertex_iff_of_iso]

/-- Every vertex of a terminal simplicial set is a zero vertex. -/
lemma isZeroVertex_of_isTerminal (hX : IsTerminal X) (x : X _⦋0⦌) : X.IsZeroVertex x :=
  ⟨isInitialVertex_of_isTerminal hX x, isTerminalVertex_of_isTerminal hX x⟩

variable (X) in
/-- A simplicial set *has a zero vertex* if some vertex is both initial and terminal. For a
quasicategory this is Lurie's condition of being *pointed*. -/
def HasZeroVertex : Prop :=
  ∃ x : X _⦋0⦌, X.IsZeroVertex x

lemma hasZeroVertex_iff : X.HasZeroVertex ↔ ∃ x : X _⦋0⦌, X.IsZeroVertex x :=
  Iff.rfl

/-- Having a zero vertex is invariant under isomorphisms of simplicial sets. -/
lemma HasZeroVertex.of_iso (hX : X.HasZeroVertex) (e : X ≅ Y) : Y.HasZeroVertex :=
  let ⟨x, hx⟩ := hX
  ⟨e.hom.app _ x, hx.map_iso e⟩

/-- The point `Δ[0]` has a zero vertex. -/
lemma stdSimplex.hasZeroVertex_zero : (Δ[0] : SSet.{u}).HasZeroVertex :=
  ⟨stdSimplex.obj₀Equiv.symm 0, isZeroVertex_of_isTerminal stdSimplex.isTerminalObj₀ _⟩

/-- The interval `Δ[1]` has no zero vertex: a zero vertex would have edges to and from both
vertices, but `Δ[1]` has no edge from `1` to `0`. -/
lemma stdSimplex.not_hasZeroVertex_one : ¬ (Δ[1] : SSet.{u}).HasZeroVertex := by
  rintro ⟨x, hx⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨e₁⟩ := hx.isInitialVertex.nonempty_edge (stdSimplex.obj₀Equiv.symm 0)
  obtain ⟨e₂⟩ := hx.isTerminalVertex.nonempty_edge (stdSimplex.obj₀Equiv.symm 1)
  have h₁ := (stdSimplex.nonempty_edge_iff i 0).1 ⟨e₁⟩
  have h₂ := (stdSimplex.nonempty_edge_iff 1 i).1 ⟨e₂⟩
  exact absurd (h₂.trans h₁) (by decide)

end SSet

namespace CategoryTheory.nerve

open SSet

/-- A vertex of the nerve of a category is a zero vertex exactly when it is a zero object of the
category. -/
theorem isZeroVertex_iff {C : Type u} [Category.{v} C] (x : C) :
    (nerve C).IsZeroVertex (nerveEquiv.symm x) ↔ IsZero x := by
  refine ((isInitialVertex_iff x).and (isTerminalVertex_iff x)).trans
    ⟨fun ⟨⟨h₁⟩, ⟨h₂⟩⟩ ↦ ⟨fun y ↦ ⟨⟨⟨h₁.to y⟩, fun _ ↦ h₁.hom_ext _ _⟩⟩,
      fun y ↦ ⟨⟨⟨h₂.from y⟩, fun _ ↦ h₂.hom_ext _ _⟩⟩⟩, fun h ↦ ⟨⟨h.isInitial⟩, ⟨h.isTerminal⟩⟩⟩

/-- The nerve of a category has a zero vertex exactly when the category has a zero object. -/
theorem hasZeroVertex_iff {C : Type u} [Category.{v} C] :
    (nerve C).HasZeroVertex ↔ HasZeroObject C := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective x
    exact ((isZeroVertex_iff x).1 hx).hasZeroObject
  · obtain ⟨z, hz⟩ := h.zero
    exact ⟨nerveEquiv.symm z, (isZeroVertex_iff z).2 hz⟩

end CategoryTheory.nerve
